"""r20-rigidity step 5 (corrected): tangent space and full mixed-direction second order.

Correction with respect to the earlier round: J (18x22) has FULL ROW RANK 18
(sigma_18 = 2.411e-9 is a genuine singular value, verified by a 60-dps mpmath SVD
of the same matrix whose entries are exact to 1e-26; Weyl then forces
sigma_18(J_exact) >= 2.411e-9 - 1e-14 > 0).
Hence
    ker J  = 4-dimensional, contains the rotation generator;
    ker J / rotation = 3-dimensional  (NOT 4);
    0 in conv{grad f_i} FAILS, with residual sigma_18/||u18||_1 ~ 1e-9.

This script:
  S1  kernel decomposition (exact kernel 4-dim, rotation direction, 3-dim quotient)
  S2  min over the unit sphere of the 3-dim quotient of max_i v^T H_i v
      (the ONLY correct second-order test: on ker J the first-order term vanishes)
  S3  direct verification of the quadratic law along the worst MIXED direction and
      along 200 random mixed directions
  S4  Hessian accuracy spot-check against mpmath
"""
import json, math, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
mp.mp.dps = 60
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C64 = np.array([[int(v) / 1e17 for v in a] for a in raw['centers_scaled_1e17']])
LO = float(raw['certified_interval']['lo'])
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']
J = np.load(P / 'r20_J60.npy')
n = 11
U, S, Vt = np.linalg.svd(J)
print('singular values: last 3 =', S[-3:])
rank = 18                                     # verified: sigma_18 = 2.4e-9 is real
Kex = Vt[rank:].T                             # 22 x 4 exact kernel
rot = np.array([c for i in range(n) for c in (-C64[i, 1], C64[i, 0])])
rot /= np.linalg.norm(rot)
print('dims: ker J = %d ; ||J Kex|| = %.2e ; dist(rot, ker J) = %.2e'
      % (Kex.shape[1], np.linalg.norm(J @ Kex), np.linalg.norm(rot - Kex @ (Kex.T @ rot))))
B = Kex - np.outer(rot, Kex.T @ rot)
qb, rb = np.linalg.qr(B)
Bt = qb[:, :int((np.abs(np.diag(rb)) > 1e-8).sum())]
print('ker J / rotation = %d-dimensional' % Bt.shape[1])
print('check: ||J Bt|| = %.2e ; ||Bt^T rot|| = %.2e'
      % (np.linalg.norm(J @ Bt), np.linalg.norm(Bt.T @ rot)))

# ---------- Hessians (same definition as step 2) ---------------------------
def mpm(C):
    return [mp.matrix([mp.mpf(float(x)) for x in C[i]]) for i in range(n)]


def circumcentre_mp(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def boundary_point(C, i, j, sgn):
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    s = mp.sqrt(1 - sum(A0[t] ** 2 for t in range(2)))
    return mp.matrix([A0[t] + sgn * s * nv[t] for t in range(2)])


acts = []
for p in tight:
    if p['kind'] == 'V3':
        acts.append(('V3', tuple(p['sites']), None))
    else:
        i, j = p['sites']
        dv = C64[i] - C64[j]
        dd = float(dv @ dv)
        A0 = (0.5 * (C64[i] @ C64[i] - C64[j] @ C64[j]) / dd) * dv
        nv = np.array([-dv[1], dv[0]]) / math.sqrt(dd)
        acts.append(('V2b', (i, j), 1 if ((np.array(p['point']) - A0) @ nv) > 0 else -1))


def f_np(kind, sites, sgn, X):
    Xm = mpm(X)
    if kind == 'V3':
        u = circumcentre_mp(Xm, sites)
        return float(mp.sqrt(sum((u[t] - Xm[sites[0]][t]) ** 2 for t in range(2))))
    p = boundary_point(Xm, sites[0], sites[1], sgn)
    return float(mp.sqrt(sum((p[t] - Xm[sites[0]][t]) ** 2 for t in range(2))))


def hess(kind, sites, sgn, h=1e-4):
    X0 = C64.copy()

    def at(shift):
        Xv = X0.copy()
        for (idx, dl) in shift:
            Xv[idx // 2, idx % 2] += dl * h
        return f_np(kind, sites, sgn, Xv)

    f0 = at([])
    H = np.zeros((22, 22))
    for a in range(22):
        H[a, a] = (at([(a, +1)]) - 2 * f0 + at([(a, -1)])) / h ** 2
        for b in range(a + 1, 22):
            H[a, b] = H[b, a] = (at([(a, +1), (b, +1)]) - at([(a, +1), (b, -1)])
                                 - at([(a, -1), (b, +1)]) + at([(a, -1), (b, -1)])) / (4 * h ** 2)
    return H


Hs = np.array([hess(k, s, g) for (k, s, g) in acts])

# Hessian spot check: entry (0,0) of ACT[0] against mpmath h=1e-8
hh = mp.mpf('1e-8')
Xv = C64.copy(); Xv[0, 0] += float(hh)
Xw = C64.copy(); Xw[0, 0] -= float(hh)
v_mp = float((f_np(*acts[0], Xv) - 2 * f_np(*acts[0], C64) + f_np(*acts[0], Xw)) / hh ** 2)
print('S4  Hessian spot check: float(h=1e-4) = %.12f  mpmath(h=1e-8) = %.12f  diff = %.2e'
      % (Hs[0][0, 0], v_mp, v_mp - Hs[0][0, 0]))

# ---------- S2/S3 min-max quadratic form over the 3-dim quotient -----------
rng = np.random.default_rng(7)
N = 200000
V = rng.normal(size=(Bt.shape[1], N))
V /= np.linalg.norm(V, axis=0)
V = Bt @ V
quad = np.einsum('an,ija,jn->in', V, Hs, V)
gmax = quad.max(axis=0)
ib = int(np.argmin(gmax))
print('\nS2  over the 3-dim quotient (ker J / rotation), %d directions:' % N)
print('    min max_i v^T H_i v = %.6e   (uniform random sampling)' % gmax[ib])
vbest = V[:, ib].copy()
g_best = float(gmax[ib])
step = 5e-2
for it in range(20000):
    w = vbest + step * rng.normal(size=22)
    w = Bt @ (Bt.T @ w)
    w /= np.linalg.norm(w)
    g = max(float(w @ Hs[i] @ w) for i in range(18))
    if g < g_best:
        vbest, g_best = w, g
    if it % 2000 == 1999:
        step *= 0.6
print('    refined min max_i v^T H_i v = %.6e  (||J v|| = %.2e)' % (g_best, np.linalg.norm(J @ vbest)))
print('    => quadratic growth lower bound  gamma(x*+t v) - gamma* >= %.6f * t^2  (numerically)' % (g_best / 2))

# ---------- direct verification -------------------------------------------
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


print('\nS3  quadratic law along the worst MIXED kernel direction:')
print('      t        gamma(t)-gamma*      (t^2/2)*g_best     ratio')
for t in (1e-4, 1e-3, 2e-3, 5e-3, 1e-2, 2e-2, 5e-2):
    obs = gamma_np(C64 + t * vbest.reshape(11, 2)) - LO
    pred = 0.5 * t * t * g_best
    print('   %8.1e   %+.6e      %+.6e     %.4f' % (t, obs, pred, obs / pred))
print('\n   200 random MIXED kernel directions at t=1e-3 (obs/pred):')
ratios = []
for k in range(200):
    w = Bt @ rng.normal(size=Bt.shape[1])
    w /= np.linalg.norm(w)
    pred = 0.5e-6 * max(float(w @ Hs[i] @ w) for i in range(18))
    obs = gamma_np(C64 + 1e-3 * w.reshape(11, 2)) - LO
    ratios.append(obs / pred)
ratios = np.array(ratios)
print('   ratio min %.4f  median %.4f  max %.4f' % (ratios.min(), np.median(ratios), ratios.max()))

json.dump({
    'rank_J': rank, 'sigma18': float(S[-1]), 'ker_dim': int(Kex.shape[1]),
    'quotient_dim': int(Bt.shape[1]),
    'minmax_quadform_sampled': float(gmax[ib]), 'minmax_quadform_refined': float(g_best),
    'quadratic_growth_coeff': float(g_best / 2),
    'worst_mixed_direction': vbest.tolist(),
    'quadratic_law_check': [[t, float(gamma_np(C64 + t * vbest.reshape(11, 2)) - LO),
                             0.5 * t * t * g_best] for t in (1e-4, 1e-3, 2e-3, 5e-3, 1e-2, 2e-2, 5e-2)],
    'random_mixed_ratios': [float(ratios.min()), float(np.median(ratios)), float(ratios.max())],
}, open(P / 'r20_second_order.json', 'w'), indent=2)
