"""r20-rigidity step 2: local optimality structure at the saved n11 candidate.

Model (geometric, no angle-only elimination assumed):
  x = (c_0..c_10) in R^22;  gamma(x) = covering radius of D = max over the CRITICAL SET
  of the nearest-site distance.  At the saved candidate the critical set has 20 points,
  18 of them tight (9 Voronoi vertices V3 + 9 boundary bisector points V2b) with
  gamma(x*) = C529, and 2 V3 points with slack 1.1527e-3.

Tests (all numeric, no new claim registered):
  T1  gradients of the 18 active functions f_i (mpmath, 40 dps, central differences)
      -> Jacobian J (18x22), rank/nullity, right kernel (with rotation generator)
  T2  GORDAN / DANSKIN first-order test: is 0 in conv{grad f_i}?
      (feasibility of J^T lambda = 0, lambda on the simplex).  If NO -> explicit
      first-order descent direction and a strictly better configuration.
  T3  second order over the FULL kernel (mixed directions, not axes):
      min over the unit sphere of K/rotation of max_i v' H_i v ;
      then direct gamma(x* + t v) vs the quadratic prediction.
  T4  counterexample hunt: random perturbations + local minimisation of the TRUE
      (nonsmooth) covering radius; report the smallest gamma found.
"""
import json, math, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
mp.mp.dps = 40

raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C64 = np.array([[int(v) / 1e17 for v in a] for a in raw['centers_scaled_1e17']], dtype=float)
LO = mp.mpf(raw['certified_interval']['lo'])
Cm = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a]) for a in raw['centers_scaled_1e17']]
n = 11
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']


# ---------- the 18 active functions ----------------------------------------
def circumcentre_mp(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def branch_sign(C, i, j, p):
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    return 1 if sum((p[t] - A0[t]) * nv[t] for t in range(2)) > 0 else -1


def boundary_point(C, i, j, sgn):
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    s = mp.sqrt(1 - sum(A0[t] ** 2 for t in range(2)))
    return mp.matrix([A0[t] + sgn * s * nv[t] for t in range(2)])


ACT = []
for p in tight:
    sites = tuple(p['sites'])
    if p['kind'] == 'V3':
        ACT.append({'kind': 'V3', 'sites': sites,
                    'f': (lambda C, s=sites: mp.sqrt(sum((circumcentre_mp(C, s)[t] - C[s[0]][t]) ** 2
                                                         for t in range(2))))})
    else:
        pt = mp.matrix([mp.mpf(v) for v in p['point']])
        sgn = branch_sign(Cm, sites[0], sites[1], pt)
        ACT.append({'kind': 'V2b', 'sites': sites, 'branch': sgn,
                    'f': (lambda C, s=sites, g=sgn: mp.sqrt(
                        sum((boundary_point(C, s[0], s[1], g)[t] - C[s[0]][t]) ** 2 for t in range(2))))})
assert len(ACT) == 18

fvals = [a['f'](Cm) for a in ACT]
print('active f values (60dps, minus lo):')
for a, v in zip(ACT, fvals):
    print('   %-4s %-10s %s' % (a['kind'], str(a['sites']), mp.nstr(v - LO, 6)))

# ---------- T1 gradients ----------------------------------------------------
H_DIR = mp.mpf('1e-14')


def grad_mp(f, C, k):
    Cp = [mp.matrix([C[i][t] + (H_DIR if (i == k and t == 0) else 0) for t in range(2)]) for i in range(n)]
    Cm_ = [mp.matrix([C[i][t] - (H_DIR if (i == k and t == 0) else 0) for t in range(2)]) for i in range(n)]
    return (f(Cp) - f(Cm_)) / (2 * H_DIR)


def grad_full_mp(f, C):
    g = []
    for k in range(n):
        for t in range(2):
            Cv = [mp.matrix(C[i]) for i in range(n)]
            Cv[k][t] += H_DIR
            Cw = [mp.matrix(C[i]) for i in range(n)]
            Cw[k][t] -= H_DIR
            g.append((f(Cv) - f(Cw)) / (2 * H_DIR))
    return g


J = np.array([[float(v) for v in grad_full_mp(a['f'], Cm)] for a in ACT])
print('\nJ shape', J.shape)
U, S, Vt = np.linalg.svd(J)
print('singular values of J:', np.array2string(S, precision=3, suppress_small=False))
rank = int((S > 1e-8 * S[0]).sum())
print('numeric rank', rank, ' nullity', 22 - rank)
Usub = U[:, rank:]          # left null space
print('left-null space dim', Usub.shape[1])
for k in range(Usub.shape[1]):
    v = Usub[:, k]
    print('  left-null vector %d: min=%.4f max=%.4f  sign pattern %s'
          % (k, v.min(), v.max(), ''.join('+' if x > 0 else '-' for x in v)))

# ---------- T2 Gordan / Danskin --------------------------------------------
# minimise ||J^T lambda||^2 over the simplex {lambda>=0, sum=1}
from scipy.optimize import minimize as spmin

def obj(lam):
    r = J.T @ lam
    return float(r @ r)

lam0 = np.ones(18) / 18
res = spmin(obj, lam0, method='SLSQP',
           constraints=[{'type': 'eq', 'fun': lambda l: l.sum() - 1}],
           bounds=[(0, 1)] * 18, options={'maxiter': 2000, 'ftol': 1e-20})
lam = res.x
r = J.T @ lam
print('\nT2 Gordan/Danskin: min||J^T lambda|| = %.3e  (||J|| scale %.3f)' % (np.linalg.norm(r), S[0]))
print('   lambda min %.4f  max %.4f  argmin index %d' % (lam.min(), lam.max(), int(np.argmin(lam))))
print('   lambda =', np.array2string(lam, precision=4))
print('   all strictly positive:', bool((lam > 1e-6).all()))
# if the residual is not ~0, look for a first-order descent direction
if np.linalg.norm(r) > 1e-6 * S[0]:
    from scipy.optimize import linprog
    lp = linprog(c=np.r_[np.zeros(22), 1.0],
                 A_ub=np.c_[J, -np.ones(18)], b_ub=np.zeros(18),
                 bounds=[(-1, 1)] * 22 + [(None, None)], method='highs')
    print('   LP descent direction found:', lp.status, lp.x[:22] if lp.success else None)


# ---------- kernel of J (right null space) ---------------------------------
K = Vt[rank:].T             # 22 x (22-rank)
rot = np.array([c for i in range(n) for c in (-C64[i, 1], C64[i, 0])])
rot = rot / np.linalg.norm(rot)
print('\nrotation generator: ||J rot|| = %.3e (||rot|| = 1)' % np.linalg.norm(J @ rot))
res = rot - K @ (K.T @ rot)
print('   distance of the rotation direction to ker J: %.3e' % np.linalg.norm(res))
B = K - np.outer(rot, K.T @ rot)        # project the kernel basis orthogonal to rotation
qb, rb = np.linalg.qr(B)
svals = np.abs(np.diag(rb))
Bt = qb[:, :int((svals > 1e-8).sum())]
print('kernel dim (incl. rotation) %d ; kernel mod rotation dim %d' % (K.shape[1], Bt.shape[1]))

# ---------- T3 second order over the FULL kernel ---------------------------
def hess(f, X0, h=1e-4):
    """central second differences in float64 (validation against mpmath below)."""
    X0 = np.array(X0, dtype=float)

    def at(shift):
        Xv = X0.copy()
        for (idx, dl) in shift:
            Xv[idx // 2, idx % 2] += dl * h
        return float(f([mp.matrix([mp.mpf(Xv[i, 0]), mp.mpf(Xv[i, 1])]) for i in range(n)]))

    f0 = at([])
    H = np.zeros((22, 22))
    for a in range(22):
        H[a, a] = (at([(a, +1)]) - 2 * f0 + at([(a, -1)])) / h ** 2
        for b in range(a + 1, 22):
            H[a, b] = H[b, a] = (at([(a, +1), (b, +1)]) - at([(a, +1), (b, -1)])
                                 - at([(a, -1), (b, +1)]) + at([(a, -1), (b, -1)])) / (4 * h ** 2)
    return H


def f_np(kind, sites, branch, X):
    Xm = [mp.matrix([mp.mpf(X[i][0]), mp.mpf(X[i][1])]) for i in range(n)]
    if kind == 'V3':
        u = circumcentre_mp(Xm, sites)
        return float(mp.sqrt(sum((u[t] - Xm[sites[0]][t]) ** 2 for t in range(2))))
    p = boundary_point(Xm, sites[0], sites[1], branch)
    return float(mp.sqrt(sum((p[t] - Xm[sites[0]][t]) ** 2 for t in range(2))))


Hs = []
for a in ACT:
    Hs.append(hess(lambda X, k=a['kind'], s=a['sites'], b=a.get('branch'): f_np(k, s, b, X), C64))
Hs = np.array(Hs)
print('\nT3: Hessians built:', Hs.shape)
# validation of the float Hessian on one active function (mpmath, h=1e-8)
_a = ACT[0]
_f = (lambda X: f_np(_a['kind'], _a['sites'], _a.get('branch'), X)) if _a['kind'] == 'V2b' else \
     (lambda X: f_np('V3', _a['sites'], None, X))
hh = mp.mpf('1e-8')
_err = 0.0
for (p_, q_) in [(0, 0), (1, 1), (0, 1), (5, 7), (20, 20), (3, 21)]:
    def at2(da, db):
        Xv = C64.copy()
        Xv[p_ // 2, p_ % 2] += da * hh
        Xv[q_ // 2, q_ % 2] += db * hh
        return _f([mp.matrix([mp.mpf(Xv[i, 0]), mp.mpf(Xv[i, 1])]) for i in range(n)])
    v_mp = float((at2(1, 1) - at2(1, -1) - at2(-1, 1) + at2(-1, -1)) / (4 * hh ** 2))
    _err = max(_err, abs(v_mp - Hs[0][p_, q_]))
print('   float-Hessian validation vs mpmath (6 entries, h=1e-8): max abs diff = %.3e' % _err)

rng = np.random.default_rng(2026)
N = 40000
V = rng.normal(size=(Bt.shape[1], N))
V /= np.linalg.norm(V, axis=0)
V = Bt @ V
quad = np.einsum('an,ija,jn->in', V, Hs, V)       # (18,N)
gmax = quad.max(axis=0)
i_best = int(np.argmin(gmax))
print('  random sphere sampling: min max_i v^T H_i v = %.6e ; max = %.6e' % (gmax[i_best], gmax.max()))
vbest = V[:, i_best].copy()
g_best = gmax[i_best]
# local refinement on the sphere / modulo rotation
step = 1e-2
for it in range(4000):
    w = vbest + step * (rng.normal(size=22))
    w = Bt @ (Bt.T @ w)                 # project back into ker(J) mod rotation
    w /= np.linalg.norm(w)
    g = max(float(w @ Hs[i] @ w) for i in range(18))
    if g < g_best:
        vbest, g_best = w, g
    if it % 500 == 499:
        step *= 0.5
print('  refined: min max_i v^T H_i v = %.6e   (||J v|| = %.3e)'
      % (g_best, np.linalg.norm(J @ vbest)))
print('  => predicted quadratic law gamma(x*+t v) - gamma* = (t^2/2)*%.4e' % g_best)

# ---------- direct check of the quadratic law + T4 hunt --------------------
def gamma_np(X):
    pts = []
    for (i, j, k) in itertools.combinations(range(11), 3):
        A = np.array([X[j] - X[i], X[k] - X[i]])
        b = 0.5 * np.array([X[j] @ X[j] - X[i] @ X[i], X[k] @ X[k] - X[i] @ X[i]])
        if abs(np.linalg.det(A)) < 1e-14:
            continue
        uu = np.linalg.solve(A, b)
        if uu @ uu > 1.0:
            continue
        d = np.linalg.norm(X - uu, axis=1)
        if set(np.argsort(d)[:3]) == {i, j, k}:
            pts.append(float(d.min()))
    for (i, j) in itertools.combinations(range(11), 2):
        dv = X[i] - X[j]
        dd = dv @ dv
        A0 = (0.5 * (X[i] @ X[i] - X[j] @ X[j]) / dd) * dv
        nv = np.array([-dv[1], dv[0]]) / math.sqrt(dd)
        s2 = 1.0 - A0 @ A0
        if s2 <= 0:
            continue
        for sgn in (+1, -1):
            p = A0 + sgn * math.sqrt(s2) * nv
            d = np.linalg.norm(X - p, axis=1)
            if set(np.argsort(d)[:2]) == {i, j}:
                pts.append(float(d.min()))
    return max(pts)


print('\n  direct check of the quadratic law along the worst kernel direction:')
print('     t        gamma(t)-gamma*      (t^2/2)*g_best')
for t in (1e-4, 1e-3, 5e-3, 1e-2, 2e-2, 5e-2):
    gv = gamma_np(C64 + t * vbest.reshape(11, 2))
    print('   %8.1e   %+.6e      %+.6e' % (t, gv - float(LO), 0.5 * t * t * g_best))

print('\n  T4 counterexample hunt (random perturbations of the true covering radius):')
best = (float('inf'), None, None)
for trial in range(400):
    rad = 10 ** rng.uniform(-4, -1.4)
    d = rng.normal(size=(11, 2))
    d = d / np.linalg.norm(d) * rad
    X = C64 + d
    g = gamma_np(X)
    if g < best[0]:
        best = (g, X.copy(), rad)
print('     best of 400 random perturbations: gamma = %.17f (gamma* = %.17f, excess %+.3e, |pert| = %.2e)'
      % (best[0], float(LO), best[0] - float(LO), best[2]))
# Nelder-Mead polish of the best few
from scipy.optimize import minimize as spmin2
pol = []
for trial in range(12):
    X0 = C64 + rng.normal(size=(11, 2)) * 1e-3
    o = spmin2(lambda z: gamma_np(z.reshape(11, 2)), X0.ravel(), method='Nelder-Mead',
               options={'maxiter': 4000, 'xatol': 1e-12, 'fatol': 1e-14})
    pol.append((float(o.fun), o.x.reshape(11, 2)))
pol.sort(key=lambda t: t[0])
print('     Nelder-Mead from 12 starts: best gamma = %.17f  (excess %+.3e)'
      % (pol[0][0], pol[0][0] - float(LO)))
print('     worst of the 12 starts: %.17f  (excess %+.3e)' % (pol[-1][0], pol[-1][0] - float(LO)))

json.dump({
    'caliber': 'numeric local structure at the saved n11 candidate; no new claim',
    'active_f_minus_lo': [[a['kind'], list(a['sites']), mp.nstr(v - LO, 6)] for a, v in zip(ACT, fvals)],
    'J_shape': list(J.shape), 'singular_values': S.tolist(), 'numeric_rank': rank,
    'left_null_vectors': Usub.tolist(),
    'gordan_lambda': lam.tolist(), 'gordan_residual': float(np.linalg.norm(r)),
    'kernel_dim_including_rotation': int(K.shape[1]),
    'kernel_mod_rotation_dim': int(Bt.shape[1]),
    'min_max_quadform_random': float(gmax[i_best]),
    'min_max_quadform_refined': float(g_best),
    'worst_kernel_direction': vbest.tolist(),
    'quadratic_law_check': [[t, float(gamma_np(C64 + t * vbest.reshape(11, 2)) - float(LO)),
                             0.5 * t * t * g_best] for t in (1e-4, 1e-3, 5e-3, 1e-2, 2e-2, 5e-2)],
    'hunt_best_random': [best[0], best[2]],
    'hunt_nelder_mead_best': pol[0][0], 'hunt_nelder_mead_worst': pol[-1][0],
}, open(P / 'r20_local_structure.json', 'w'), indent=2)
print('\nwritten r20_local_structure.json')
