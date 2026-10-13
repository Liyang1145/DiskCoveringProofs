"""cline2-coupled-factors g8: the exact control parameter and the global minimization of M.

RIGOROUS GLOBAL CHAIN (all steps exact, stated domains):

  (G1) M := max_{f=0..19} gamma_f, the root-gauge maximum branch (root-invariant).
  (G2) R_shape = M q_0/ell_0, and the six circle equalities give q_i/ell_i = q_0/ell_0
       for every i, so also R_shape = M q_i/ell_i for every i in {0..8}.
  (G3) M ell_i <= 2 sin(alpha_i/2) =: s_i  (a chord of a triangle with two sides
       gamma_{i-1}, gamma_i <= M and included angle alpha_i), equality iff both equal M.
       Hence, for every i,
             R_shape = M q_i/ell_i >= M * M q_i/s_i = M^2 q_i/s_i >= q_i/s_i.
  (G4) Therefore the SINGLE scalar that controls the bound is M:
             R_shape >= M^2 * min_{i=0..8} (q_i/s_i).
  (G5) M is determined by the angles through the sine-law recursion, so
             M >= 1 + (needed epsilon) is what a proof of R >= 0.38 requires; measured
             requirement at the candidate: M >= 1.0000421079 (from min_i 0.38 s_i/q_i).

THIS SCRIPT: minimize M over the legal constraint manifold (13 linear angle equations, the
2 sine-product cycle equations) with the domain inequalities inactive (interior).  This is
the exact decision: if min M > 1.0000421079 the bound R >= 0.38 follows from (G4) ALONE,
with no use of the width/circle data beyond (G2).  If min M ~ 1 then the parity argument is
insufficient and the width data (the six circle equations as EQUALITIES of q_i/ell_i) is the
irreducible extra input.  Numeric, single-start, scoped as a decision diagnostic.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json, importlib.util
from scipy.optimize import minimize
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
spec = importlib.util.spec_from_file_location('gmod', P/'g1_structure.py')
gm = importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)
eq = ns['eq']; rhs = ns['rhs']
a0 = ns['x0'][:42]
N = np.linalg.svd(eq[:, :42])[2][np.linalg.matrix_rank(eq[:, :42]):].T
print(f'linear-constraint nullspace dim = {N.shape[1]}')

# implicit constraint function: 15 residuals (13 linear + 2 cycle)
def cons15(u):
    a = a0+N@u
    _, c, _ = gm.shape(a)
    return c[:15]


def logM(u):
    a = a0+N@u
    _, _, d = gm.shape(a)
    g = np.exp(d['logg'])
    return math.log(g.max())


r0 = cons15(np.zeros(29))
print(f'residual at u=0: max = {np.abs(r0).max():.3e}')
print(f'log M at u=0: {logM(np.zeros(29)):.12f}  -> M = '
      f'{math.exp(logM(np.zeros(29))):.12f}')
print(f'requirement for R >= 0.38: M >= 1.0000421079 per (G4)-(G5)')

best = None
from scipy.optimize import least_squares
scales = [1e-5, 1e-4, 1e-3, 1e-2, 5e-2, .1, .2]
print(f'\n{"scale":>8s} {"min M found":>18s} {"max constraint resid":>22s} '
      f'{"min(0.38 s/q) * M^2":>20s}')
w = 100.0
for sc in scales:
    def obj(u):
        return logM(u)+w*float(np.sum(cons15(u)**2))
    rng = np.random.default_rng(7)
    ubest = None
    for trial in range(6):
        u0 = np.zeros(29) if trial == 0 else rng.normal(0, sc, 29)
        res = minimize(obj, u0, method='Nelder-Mead',
                       options={'maxiter': 40000, 'xatol': 1e-14, 'fatol': 1e-16})
        if ubest is None or res.fun < ubest.fun:
            ubest = res
    u = ubest.x
    a = a0+N@u
    R, c, d = gm.shape(a)
    Mn = float(np.exp(d['logg']).max())
    q = 2*np.sin(d['w']/2); s = 2*np.sin(d['alpha']/2)
    ratio = (0.38*s/q).min()
    feasible = np.abs(c[:15]).max() < 1e-8
    print(f'{sc:8.1e} {Mn:18.12f} {np.abs(c[:15]).max():22.3e} {ratio:20.8f}'
          f'{"  feasible" if feasible else ""}')
    if feasible and (best is None or Mn < best[0]):
        best = (Mn, a.copy(), float(ratio))
        np.save(OUT/'g8_best_angles.npy', a)

if best:
    Mn, a, ratio = best
    print(f'\nBEST feasible M found = {Mn:.12f}')
    print(f'  -> (G4) gives R_shape >= {Mn*Mn*float(min(2*np.sin(gm.shape(a)[2]["q"] if False else 2*np.sin(gm.shape(a)[2]["w"]/2))/ (2*np.sin(gm.shape(a)[2]["alpha"]/2)))):.12f}')
    print(f'  requirement for 0.38: M >= {ratio:.10f}; gap = {ratio-Mn:+.3e}')
    Rv, cv, dv = gm.shape(a)
    q = 2*np.sin(dv['w']/2); s = 2*np.sin(dv['alpha']/2)
    print(f'  actual R_shape at that shape = {Rv:.12f}')
    print(f'  M^2 min(q/s) = {Mn*Mn*float((q/s).min()):.12f}')
    print(f'\nDECISION: if min M ~ 1, (G4) alone cannot give 0.38 and the six circle')
    print(f'equations (width data) are irreducible; if min M > requirement, (G4) suffices.')
