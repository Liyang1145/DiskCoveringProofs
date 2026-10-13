"""cline2-coupled-factors f5: why does opening the first-moment adjoint blow up the LP?

Two candidate explanations, both testable in isolation:
 (H1) NUMERIC: the column-generation LP is under-determined and wanders between vertices.
 (H2) STRUCTURAL: the first-moment coefficients really do open an unbounded ray of the
      dual LP, i.e. a one-parameter family of multipliers whose factor-maxima stay below
      the constant's growth.  That happens iff the adjoint of an exact identity is opened
      without the *opposite-sign* counterpart, because for an EXACT identity the dual
      multiplier must satisfy a zero-sum coherence condition, not an inequality.
"""
import numpy as np, json, math, sys, time
from pathlib import Path
from scipy.optimize import linprog
sys.path.insert(0, str(Path(__file__).parent))
import f4_feasible_dual as F

pi = math.pi

# ---------------- H2 test: explicit ray search ----------------
def ray_test(pr, niter=60, verbose=True):
    """Maximize  (base.d) - sum_{f} max_i(-M_fi.d - 2*lam_f)  over directions d with
    |d_j| <= 1.  If the optimum is +inf, the dual LP has an unbounded ray along d
    (base.d is the objective ray, and -M.d the pricing ray)."""
    nz = pr['nz']; nb = len(pr['factors'])
    # We search a ray d with columns of the enlarged LP.  A direction d is a valid ray if
    # for every sample row i:  M_fi.d + t_f^ray <= 0, i.e. t_f^ray <= min_i(-M_fi.d).
    # Rays must also respect the movement into unbounded sides of the variable bounds;
    # we simply cap |d| <= 1 and look for base.d > 0 with all sample rows satisfied.
    rows = []
    for name, v, M in pr['factors']:
        rows.append(M)
    A = np.vstack(rows)                      # (sum samples, nz)
    # choose t^ray = min_i(-M d) per factor, so constraints are automatically satisfied
    # objective ray = base.d + sum_f min_i(-M_fi.d)
    # search max base.d + sum_f t_f  s.t. t_f + M_fi.d <= 0, -1<=d<=1
    nrows = A.shape[0]
    idx = np.zeros(nrows, int)
    st = 0
    for k, (name, v, M) in enumerate(pr['factors']):
        idx[st:st+M.shape[0]] = k; st += M.shape[0]
    from scipy import sparse
    Ab = sparse.hstack([sparse.csr_matrix(A),
                        sparse.csr_matrix((np.arange(nrows), idx), shape=(nrows, nb))])
    c = -np.concatenate([pr['base'], np.ones(nb)])          # maximize
    bnds = [(-1, 1)]*nz + [(None, None)]*nb
    sol = linprog(c, A_ub=Ab, b_ub=np.zeros(nrows), bounds=bnds, method='highs')
    print('ray LP status:', sol.status, sol.message)
    if sol.status == 0:
        print(f'  ray optimum = {-sol.fun:.6f}   (finite => no ray in this box)')
        d = sol.x[:nz]
        print(f'  |d| of first-moment block = {np.abs(d[121:]).max():.6f}')
        return -sol.fun, d
    return None, None


def bounded_run(pr, lb, maxiter=80, tol=1e-11):
    return F.solve(pr, maxiter=maxiter, tol=tol, verbose=False, bounds_l=(-lb, lb))


if __name__ == '__main__':
    print('=== build ===')
    pr = F.build(open_L=True)
    print('nz', pr['nz'], 'factors', len(pr['factors']))
    print('\n=== H1: bounded-ℓ runs (does the LP settle?) ===')
    for lb in [0.25, 0.5, 1.0, 2.0]:
        t0 = time.time()
        best, bz, hist, pick = bounded_run(pr, lb, maxiter=60)
        print(f'  |L|<={lb:4.2f}: best={best:.9f}  iters={len(hist)}  '
              f'lp_last={hist[-1][1]:.9f}  ub_last={hist[-1][2]:.9f}  '
              f'{time.time()-t0:.1f}s')
        if bz is not None:
            np.save(F.OUT / f'z_lb{lb}.npy', bz)
