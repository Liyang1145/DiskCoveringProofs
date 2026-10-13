"""cline2-coupled-factors g5: the exact GEOMETRIC-MEAN bound and the log-sine weights.

Everything here follows from three exact facts at any legal shape (no sampling, no grids):

 (F1) q_i = 2 sin(w_i/2),  and (M ell_i)^2 = gamma_{i-1}^2 + gamma_i^2
      - 2 gamma_{i-1} gamma_i cos(alpha_i)   with gamma_f <= M, M = max_f gamma_f >= 1.
 (F2) the six circle equations give q_i/ell_i = q_0/ell_0 for every i, hence
      R_shape = M q_i/ell_i for EVERY i in {0..8}.
 (F3) sum_i w_i = 2 pi on the legal domain.

Consequences, for ANY weights W_i >= 0 with sum W_i = 1 (all logs are of equal numbers):
     log R_shape = sum_i W_i log q_i - sum_i W_i log ell_i + log M
                 >= sum_i W_i log(2 sin(w_i/2)) - max_i log ell_i + log M.
The second line is the only place where a bound on ell enters, and by (F1) ell_i is a chord
length of a triangle whose two sides are gamma_{i-1}, gamma_i <= M and included angle
alpha_i.  Hence with x_i = gamma_i/M in [0,1],

     M ell_i <= M * sqrt(x_{i-1}^2 + x_i^2 - 2 x_{i-1} x_i cos alpha_i)  and, more usefully,
     M ell_i <= max_{x,y in [0,1]} sqrt(x^2+y^2-2xy cos alpha_i)
              = sqrt(2 - 2 cos alpha_i) = 2 sin(alpha_i/2)   (attained at x = y = 1).

Therefore, GLOBALLY,
     M ell_i <= 2 sin(alpha_i/2) =: s_i,
     R_shape = M q_i/ell_i >= M q_i / (s_i/M) * (1/M) ... let us redo cleanly:
     R_shape = M (q_i/ell_i)  and   ell_i <= s_i/M   =>   q_i/ell_i >= M q_i/s_i,
     so      R_shape >= M^2 q_i / s_i  >= q_i / s_i   (M >= 1).
Multiplying with weights W_i:
     log R_shape >= sum_i W_i log(2 sin(w_i/2)) - sum_i W_i log(2 sin(alpha_i/2)) + log M.
This script evaluates the best such bound (numerically over W) at the candidate and reports
the exact shortfall, plus the parallel arithmetic-mean version.  NO claims, no grids: the
optimization over W is a tiny convex problem whose output is a diagnostic for feasibility.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json, sys, importlib.util
from scipy.optimize import minimize
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
spec = importlib.util.spec_from_file_location('gmod', P/'g1_structure.py')
gm = importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)
a0 = ns['x0'][:42]
R, con, d = gm.shape(a0)
M = float(np.exp(d['logg']).max())
ell = d['ell']; w = d['w']; al = d['alpha']
q = 2*np.sin(w/2)
s = 2*np.sin(al/2)
gam = np.exp(d['logg'])
print(f'candidate: R = {R:.16f}  M = {M:.16f}')
print(f'alpha_i = {np.round(al, 8)}')
print(f'sum alpha_i = {al.sum():.10f}')
print(f'2 sin(alpha_i/2) = {np.round(s, 10)}')
print(f'M ell_i          = {np.round(M*ell, 10)}   (each <= s_i? '
      f'{np.all(M*ell <= s+1e-12)})')
print(f'q_i = 2 sin(w_i/2) = {np.round(q, 10)}')
print(f'ratio M*q_i/(M*ell_i) = {np.round(M*q/ell, 12)}  (all = R)')
print(f'lower bound per sector M^2 q_i/s_i >= R? '
      f'{np.round(M*M*q/s, 12)} vs R = {R:.12f}')

# ---- best weighted bound ----
def best_bound(al_v, w_v, Mv, n=9):
    qv = 2*np.sin(w_v/2); sv = 2*np.sin(al_v/2)
    lq = np.log(qv); ls = np.log(sv)
    def neg(W):
        W = np.abs(W); W = W/W.sum()
        return -(W@lq - W@ls)      # ignoring +log M >= 0
    best = None
    for seed in range(6):
        rng = np.random.default_rng(seed)
        W0 = np.ones(n)/n if seed == 0 else rng.dirichlet(np.ones(n))
        res = minimize(neg, W0, method='Nelder-Mead',
                       options={'xatol': 1e-12, 'fatol': 1e-14, 'maxiter': 20000})
        if best is None or res.fun < best.fun:
            best = res
    W = np.abs(best.x); W = W/W.sum()
    return math.exp(-best.fun), W


lb, W = best_bound(al, w, M)
print(f'\n--- exact global bound (F1)-(F3) with optimized weights ---')
print(f'log R >= sum W log(q_i) - sum W log(s_i) + log M >= {math.log(lb):.12f} '
      f'-> R >= {lb:.12f}')
print(f'optimal weights = {np.round(W, 6)}')
print(f'shortfall vs 0.38: {lb-0.38:+.6f}')
print(f'shortfall vs R_cert: {lb-R:+.6f}')
print(f'(uniform weights give {math.exp(np.mean(np.log(q/s))):.12f})')

# ---- arithmetic version: R >= (1/9) sum q_i / max ell  -- needs max ell, use the cap ----
print(f'\n--- arithmetic version ---')
# R = M q_0/ell_0 = (1/9) sum_i M q_i/ell_i >= (1/9)(sum_i q_i)/max_i(ell_i) if M>=1
print(f'R >= (1/9) sum_i q_i / max_i ell_i = {q.sum()/9/ell.max():.12f}')
print(f'using the global cap ell_i <= s_i/M <= s_i: R >= (1/9) sum_i q_i / max_i s_i '
      f'= {q.sum()/9/ (s.max()/M):.12f}')
print(f'   (note max_i s_i = {s.max():.8f} at alpha_i = {al[int(np.argmax(s))]:.6f})')

# ---- the sharp question: what is the best possible with these tools? ----
print(f'\n--- decisive reading ---')
print(f'The bound (F1)-(F3) is essentially the GLOBAL minimum of the relaxation')
print(f'   min over admissible (alpha_i, w_i, gamma_i) of  sum_i W_i log(q_i/s_i) + log M')
print(f'because ell_i <= s_i/M is the ONLY consequence of gamma_f <= M available.')
print(f'At the candidate the two sides differ by:')
print(f'   sum_i W log(s_i) - sum_i W log(M ell_i) = '
      f'{float(W@np.log(s))-float(W@np.log(M*ell)):+.6f}  (in log units)')
print(f'   i.e. the relaxation loses at most this much; the bound is '
      f'{lb:.12f} vs true {R:.12f}')
