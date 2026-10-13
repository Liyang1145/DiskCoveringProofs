"""Projected objective gradients + Danskin/KKT degeneracy test (numeric gradients, mpmath).

Free variables: 22 centre coordinates; R fixed at its certified lower endpoint.
Active constraints (18): 9 tight Voronoi vertices and 9 boundary spokes, each written as
"the nearest-site distance of the tight point equals R".

Objective gamma: max over the full critical set.  At the candidate the maximum is attained
by these 18 points, so the direction derivative of gamma is  max_k <grad r_k, dx>
(Danskin).  If some projected gradient on ker J is not a common multiple, there is a
descent direction and the candidate is NOT a local minimum of the covering radius.
"""
import json, io, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, atan2, pi, nstr

mp.dps = 40
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
Cf = [(mpf(int(a)) / mpf(10) ** 17, mpf(int(b)) / mpf(10) ** 17) for a, b in D['centers_scaled_1e17']]
R0 = mpf(float(D['certified_interval']['lo']))
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
SPOKES = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]
X0 = [v for i in range(11) for v in Cf[i]]


def circ(P, Q, W):
    ax, ay = P; bx, by = Q; cx, cy = W
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def spoke_pt(ci, cj, R):
    ax = 2 * (ci[0] - cj[0]); ay = 2 * (ci[1] - cj[1])
    b = (ci[0] ** 2 + ci[1] ** 2) - (cj[0] ** 2 + cj[1] ** 2)
    n2 = ax * ax + ay * ay
    t = b / n2
    fx, fy = ax * t, ay * t
    L2 = 1 - (fx * fx + fy * fy)
    s = sqrt(L2) / sqrt(n2)
    for sg in (mpf(1), mpf(-1)):
        p = (fx - sg * s * ay, fy + sg * s * ax)
        th = atan2(p[1], p[0]) % (2 * pi)
        lo = atan2(ci[1], ci[0]) % (2 * pi); hi = atan2(cj[1], cj[0]) % (2 * pi)
        if hi < lo:
            hi += 2 * pi
        if th < lo:
            th += 2 * pi
        if lo - mpf('1e-9') <= th <= hi + mpf('1e-9'):
            return p
    raise RuntimeError('spoke branch')


def dist_vertex(xx, tri, k=None):
    C = [(xx[2 * i], xx[2 * i + 1]) for i in range(11)]
    v = circ(C[tri[0]], C[tri[1]], C[tri[2]])
    kk = tri[0] if k is None else k
    return sqrt((v[0] - C[kk][0]) ** 2 + (v[1] - C[kk][1]) ** 2)


def dist_spoke(xx, i, j, k=None):
    C = [(xx[2 * i2], xx[2 * i2 + 1]) for i2 in range(11)]
    p = spoke_pt(C[i], C[j], R0)
    kk = i if k is None else k
    return sqrt((p[0] - C[kk][0]) ** 2 + (p[1] - C[kk][1]) ** 2)


def grad(f, x, h):
    n = len(x)
    g = np.zeros(n)
    for j in range(n):
        xp = list(x); xm = list(x)
        xp[j] += h; xm[j] -= h
        g[j] = float((f(xp) - f(xm)) / (2 * h))
    return g


def main():
    h = mpf('1e-23')
    G = []
    for tri in TRIPLES:
        G.append(grad(lambda xx: dist_vertex(xx, tri), X0, h))
    for (i, j) in SPOKES:
        G.append(grad(lambda xx: dist_spoke(xx, i, j), X0, h))
    G = np.array(G)
    u, s, vt = np.linalg.svd(G)
    rk = int((s > 1e-8 * s[0]).sum())
    print('sv of the 18x22 constraint-gradient matrix:')
    print(['%.4e' % y for y in s])
    print('rank = %d  nullity = %d' % (rk, 22 - rk))
    N = vt[rk:].T
    P = G @ N
    print('\nprojected objective gradients:')
    lbl = [str(t) for t in TRIPLES] + ['spoke%s' % str(sp) for sp in SPOKES]
    for r in range(18):
        print('  %2d %-12s |proj|=%12.8f  |grad|=%9.5f  cos=%+.6f' %
              (r, lbl[r], np.linalg.norm(P[r]), np.linalg.norm(G[r]),
               np.linalg.norm(P[r]) / max(1e-30, np.linalg.norm(G[r]))))
    u2, s2, vt2 = np.linalg.svd(P)
    print('\nsingular values of P:', ['%.6f' % y for y in s2])
    print('min-norm convex-combination residual (mean of P):', '%.6f' % np.linalg.norm(P.mean(0)))
    d = N @ vt2[0]
    print('\ntop projected descent direction d (per centre):')
    for i in range(11):
        print('   c%2d (%+.8f, %+.8f)' % (i, d[2 * i], d[2 * i + 1]))
    np.save(Path(__file__).parent.parent / 'out' / 'G18.npy', G)
    np.save(Path(__file__).parent.parent / 'out' / 'Nker.npy', N)
    np.save(Path(__file__).parent.parent / 'out' / 'Pproj.npy', P)
    # sanity: does moving along d change gamma at first order along the manifold?
    print('\nfirst-order predictions <grad r_k, d> for the 18 tight rows:')
    for r in range(18):
        print('   %2d %-12s %+.8e' % (r, lbl[r], G[r] @ d))


if __name__ == '__main__':
    main()
