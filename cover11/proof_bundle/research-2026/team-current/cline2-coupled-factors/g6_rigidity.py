"""cline2-coupled-factors g6: the rigidity test that decides R >= 0.38 vs R < 0.38.

EXACT CHAIN (no sampling; all steps are algebraic identities or inequalities with stated
domains):

  (E1)  R_shape = M q_i/ell_i for every sector i,  M = max_f gamma_f >= 1.
  (E2)  M ell_i <= 2 sin(alpha_i/2) =: s_i  with equality iff both endpoints gamma
        equal M (chord length of a triangle with two sides <= M and included angle
        alpha_i).  Hence  R_shape >= M^2 q_i/s_i >= q_i/s_i.
  (E3)  Consequently  R_shape < 0.38  implies, for EVERY sector i,
            M^2 q_i/s_i < 0.38,  so  M^2 < 0.38 s_i/q_i  and  M <= 1 + 0.38 s_i/(2 q_i)
        (using (1+eps)^2 <= 1+3 eps for eps <= 1).
  (E4)  gamma_g/gamma_f = sin(a_fg)/sin(a_gf) along each tree edge, so
            |log gamma_f - log M| <= sum of |log(sin a/sin b)| over tree edges,
        and  |log C_k| = |log prod(ratios around cycle k)| likewise.
  (E5)  the two non-tree cycle products C_1, C_2 must equal 1 exactly.

RIGIDITY TEST.  If M <= 1.00004 then every edge ratio is within ~1e-4 of 1, so each
cross-edges difference |a_fg - a_gf| <= 1.5e-4 or |a_fg + a_gf - pi| <= 1.5e-4.  The
cycle residuals change by a LINEAR function of the free angle perturbations.  We test
whether the two residuals can be driven to their required values while every angle stays
inside its domain box.  If not, M >= 1.000042 is forced by the cycles alone, and combining
with (E3) gives the bound.  LP feasibility, hence a diagnostic (not a proof) of which side
the true global minimum is on.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json, sys, importlib.util, collections
from scipy.optimize import linprog
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
spec = importlib.util.spec_from_file_location('gmod', P/'g1_structure.py')
gm = importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)
A = ns['A']; B = ns['B']; U = ns['U']; V = ns['V']; eq = ns['eq']
a0 = ns['x0'][:42]
R, con, d = gm.shape(a0)
M = float(np.exp(d['logg']).max())
ell = d['ell']; w = d['w']; al = d['alpha']
q = 2*np.sin(w/2); s = 2*np.sin(al/2)
print(f'candidate: R = {R:.16f}   M = {M:.16f}')
print(f'(E3) per-sector cap on M for R < 0.38:')
caps = []
for i in range(9):
    cap = 1 + 0.38*s[i]/(2*q[i])
    caps.append(cap)
    print(f'   i={i}: q={q[i]:.8f} s={s[i]:.8f}  0.38 s/q={0.38*s[i]/q[i]:.8f}  '
          f'M <= {cap:.8f}')
print(f'   binding (smallest) cap: {min(caps):.10f}  -> M <= {min(caps):.10f} would be '
      f'needed for R < 0.38')
eps = min(caps)-1
print(f'   i.e. eps = {eps:.3e}; then every tree ratio is within '
      f'{eps*max(np.sin(a0), 1)*1:.2e}.. of 1')

# ---- cycle structure and the Jacobian of the two cycle residuals ----
edge = []; adj = collections.defaultdict(list)
for k in range(21):
    f = int(np.argmax(U[k, 42:62])); g = int(np.argmax(V[k, 42:62]))
    edge.append((f, g)); adj[f].append((g, k, 1)); adj[g].append((f, k, -1))
parent = {}; order = [0]; seen = {0}
while order:
    nxt = []
    for f in order:
        for gg, k, dd in adj[f]:
            if gg not in seen:
                seen.add(gg); parent[gg] = (f, k, dd); nxt.append(gg)
    order = nxt


def path(v):
    out = []
    while v != 0:
        f, k, dd = parent[v]; out.append((f, k, dd)); v = f
    return out


logg, cy, tree, other = gm.radii(a0, 0)
print(f'\nnon-tree cycle edges: {other} with face pairs '
      f'{[edge[k] for k in other]}')
for kidx, k in enumerate(other):
    f, gg = edge[k]
    terms = [(kk, dd) for (par, kk, dd) in path(f)]
    terms += [(kk, -dd) for (par, kk, dd) in reversed(path(gg))]
    terms.append((k, 1))
    print(f'cycle {kidx+1} (non-tree edge slot {k}): {len(terms)} edges')


def cycle_ratio_jac(k):
    """d/d(angle) of the signed log-sine product around the cycle of non-tree edge k."""
    f, gg = edge[k]
    terms = [(kk, dd) for (par, kk, dd) in path(f)]
    terms += [(kk, -dd) for (par, kk, dd) in reversed(path(gg))]
    terms.append((k, 1))
    J = np.zeros(42)
    for (kk, dd) in terms:
        aa = float(A[kk, :42]@a0); bb = float(B[kk, :42]@a0)
        J += dd*(np.cos(aa)/math.sin(aa)*A[kk, :42]
                 - np.cos(bb)/math.sin(bb)*B[kk, :42])
    return J


Jc = np.array([cycle_ratio_jac(k) for k in other])
print(f'cycle Jacobian row norms: {np.round(np.linalg.norm(Jc, axis=1), 6)}')
print(f'cycle residual values: {np.round(cy, 12)}')
N = np.linalg.svd(eq[:, :42])[2][np.linalg.matrix_rank(eq[:, :42]):].T
print(f'nullspace of the 13 linear constraints: {N.shape}')
Klin = Jc[:2] @ N
print(f'Klin (2 x {Klin.shape[1]}) singular values: '
      f'{np.round(np.linalg.svd(Klin, compute_uv=False)[:4], 6)}')

# ---- the box constraint: which angle q is the "anchor" of each edge ratio? ----
# For a cross-side edge the ratio is sin(a_fg)/sin(a_gf); a perturbation of the anchor
# angles changes the residual; the box limits |delta angle| <= eps_ang.
eps_ang = eps*1.0*1.0
print(f'\nangle box: |delta a| <= eps_ang = {eps_ang:.3e} (from the same M cap)')
tgt = -cy[:2]
# feasibility: find u in R^27 with |N u|_inf <= eps_ang and Klin u = tgt
Aub = np.vstack([np.eye(27), -np.eye(27)])
bub = np.ones(27)
res = linprog(np.zeros(27), A_ub=Aub, b_ub=bub, A_eq=Klin, b_eq=tgt,
              bounds=[(-1, 1)]*27, method='highs')
print(f'\nLP feasibility (can the cycles be restored inside the box?), scaled by eps_ang:')
print(f'   status = {res.status}  ({res.message})')
if res.status == 0:
    u = res.x
    da = N@u
    print(f'   FEASIBLE: max|da| = {np.abs(da).max():.3e} (box {1.0:.3f} in scaled units; '
          f'real bound {eps_ang:.2e})')
    print(f'   residual after linear move: {np.round(Jc[:2]@da+cy[:2], 3e-8)}')
else:
    print('   INFEASIBLE: the cycle equations cannot be restored inside the angle box')
    print('   => M >= 1+eps is forced, and by (E3) R >= 0.38 follows on the linear model')

# ---- cross-check: exact nonlinear feasibility, tiny trust region ----
print('\nnonlinear check: solve the 2 cycle equations by least squares over the 27 dims')
from scipy.optimize import least_squares


def res2(u):
    a = a0+N@u
    _, c, _ = gm.shape(a)
    return c


sol = least_squares(res2, np.zeros(27), bounds=(-eps_ang, eps_ang), xtol=1e-15,
                    ftol=1e-15, gtol=1e-15, max_nfev=400)
print(f'   |cycle residual| after = {np.abs(sol.fun).max():.3e} (start '
      f'{np.abs(res2(np.zeros(27))).max():.3e}), max|da| = '
      f'{np.abs(N@sol.x).max():.3e}')
