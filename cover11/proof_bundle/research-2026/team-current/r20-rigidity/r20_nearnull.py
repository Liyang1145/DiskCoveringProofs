"""r20-rigidity step 4: the near-null direction and the forbidden first-order descent.

Established in step 2/3:
  J (18 x 22, gradients of the 18 active distances at the saved candidate) has
  full row rank 18; the smallest singular value sigma_18 = 2.411e-9 is REAL
  (reproduced by an independent 60-dps mpmath SVD of the same float64 matrix,
  and the underlying J entries are exact to 1e-26; Weyl => sigma_18 > 2.4e-9).
  The left singular vector u_18 is strictly positive.
Therefore:
  (i) the Gordan/Danskin relation 0 in conv{grad f_i} does NOT hold exactly --
      the best nonnegative combination has residual 2.4e-9 (2.2e-9 relative);
  (ii) v = -Vt[17] has J v = -sigma_18 u_18 < 0 componentwise: a first-order
      descent direction for ALL 18 tight constraints.
  (iii) gamma(x* - t v) should therefore dip below gamma* for small t.

This script measures the dip (mpmath, 60 dps) and relates v to the mirror
antisymmetrisation direction of the candidate.
"""
import json, math
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
mp.mp.dps = 60
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C64 = np.array([[int(v) / 1e17 for v in a] for a in raw['centers_scaled_1e17']])
LO = mp.mpf(raw['certified_interval']['lo'])
T_CERT = mp.mpf('0.379983853119838689722261606136093214308718957')
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']
J = np.load(P / 'r20_J60.npy')
n = 11

U, S, Vt = np.linalg.svd(J)
v18 = Vt[17]                                  # near-null right singular vector
u18 = U[:, -1]
Jv = J @ v18
print('sigma_18 = %.6e ; u_18 min/max = %.6e / %.6e ; sign pattern %s'
      % (S[-1], u18.min(), u18.max(), ''.join('+' if x > 0 else '-' for x in u18)))
print('J v18 : min %.6e  max %.6e   (all positive == J v18 = +sigma u18)'
      % (Jv.min(), Jv.max()))
print('=> v = -v18 gives J v < 0 componentwise: first-order descent for all 18.')
print('   slope range: %.3e .. %.3e per unit ||v||' % (-Jv.max(), -Jv.min()))

# antisymmetrisation direction (mirror axis from the calibration)
axis = float(cal['A']['best_mirror_axis']['axis_angle_deg']) * math.pi / 180
Rm = np.array([[math.cos(2 * axis), math.sin(2 * axis)], [math.sin(2 * axis), -math.cos(2 * axis)]])
Cr = C64 @ Rm
w = (C64 - Cr).reshape(-1)
print('\nantisymmetrisation direction |w| = %.3e' % np.linalg.norm(w))
w = w / np.linalg.norm(w)
print('|cos(v18, antisym. dir)| = %.8f   |cos(v18, rot)| = %.3e'
      % (abs(float(v18 @ w)), abs(float(v18 @ np.array([c for i in range(n) for c in (-C64[i, 1], C64[i, 0])]))) /
         np.linalg.norm(np.array([c for i in range(n) for c in (-C64[i, 1], C64[i, 0])]))))


# ---- mpmath gamma on the fixed 18+2 critical structure --------------------
def mpm_exact():
    return [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a])
            for a in raw['centers_scaled_1e17']]


def shifted(Cbase, delta_flat):
    return [mp.matrix([Cbase[i][0] + mp.mpf(float(delta_flat[2 * i])),
                       Cbase[i][1] + mp.mpf(float(delta_flat[2 * i + 1]))]) for i in range(n)]


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
        sgn = 1 if ((np.array(p['point']) - A0) @ nv) > 0 else -1
        acts.append(('V2b', (i, j), sgn))


def dist(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def f_act(kind, sites, sgn, C):
    if kind == 'V3':
        u = circumcentre_mp(C, sites)
        return dist(u, C[sites[0]])
    return dist(boundary_point(C, sites[0], sites[1], sgn), C[sites[0]])


def gamma18(C):
    return max(f_act(k, s, g, C) for (k, s, g) in acts)


CM = mpm_exact()
g0 = gamma18(CM)
print('\ngamma(x*) = %s   (certified lo = %s,  gamma-lo = %s)'
      % (mp.nstr(g0, 32), mp.nstr(LO, 32), mp.nstr(g0 - LO, 6)))

print('\ndescent test  v = -v18, t in [1e-10, 2e-7] (mpmath 60 dps):')
print('      t          gamma(x*-t v) - gamma*        slope (per t)      (t^2/2)*0.074 ref')
best = (mp.mpf(0), mp.mpf(0))
for t in ('1e-10', '3e-10', '1e-9', '3e-9', '6e-9', '1e-8', '2e-8', '5e-8', '1e-7', '2e-7'):
    tt = mp.mpf(t)
    d = shifted(CM, -float(tt) * v18)
    val = gamma18(d) - g0
    print('   %-9s  %+.8e          %+.4e' % (t, val, val / tt))
    if val < best[1]:
        best = (tt, val)
print('   best (most negative) : t = %s , delta gamma = %s' % (mp.nstr(best[0], 4), mp.nstr(best[1], 6)))

print('\nsame test in the OPPOSITE direction (+t v18):')
for t in ('3e-9', '1e-8', '1e-7'):
    tt = mp.mpf(t)
    val = gamma18(shifted(CM, float(tt) * v18)) - g0
    print('   %-9s  %+.8e' % (t, val))

# how far does the descent continue?  scan further out in float64
def gamma_np(X):
    import itertools
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


print('\nfloat64 scan of gamma(x* - t v18) for larger t:')
for t in (1e-7, 3e-7, 1e-6, 3e-6, 1e-5):
    print('   t=%-8.1e  gamma-gamma* = %+.6e' % (t, gamma_np(C64 - t * v18.reshape(11, 2)) - float(LO)))

json.dump({
    'sigma_min_J18': float(S[-1]),
    'u18_sign_all_positive': bool((u18 > 0).all()),
    'u18_min': float(u18.min()),
    'Jv18_min_max': [float(Jv.min()), float(Jv.max())],
    'cos_v18_antisym': abs(float(v18 @ w)),
    'gamma_star_60dps': mp.nstr(g0, 32),
    'gamma_minus_lo': mp.nstr(g0 - LO, 6),
    'descent_best': [mp.nstr(best[0], 4), mp.nstr(best[1], 6)],
}, open(P / 'r20_nearnull.json', 'w'), indent=2)
