"""FINAL active set (corrected) + rank / flat-direction test, all with the correct
perpendicular-bisector parametrisation.

Boundary critical points: for pair (i,j),  p . (c_i - c_j) = (|c_i|^2 - |c_j|^2)/2  with
p = A +- s * B,  A = C * (c_i-c_j)/|c_i-c_j|^2  (C = the RHS),  B = perpendicular unit,
s = sqrt(1 - |A|^2).  Exactly 9 such points have the two generating sites as the two nearest
and lie at distance R; they are the consecutive pairs of the induced cyclic order
    [5,7], [7,1], [1,8], [8,6], [6,4], [4,9], [9,10], [10,3], [3,5].

Tight Voronoi vertices: the 9 triple points with nearest-site distance R:
    (0,9,10) (0,2,5) (0,3,5) (2,6,8) (2,5,7) (0,4,6) (0,2,6) (1,2,8) (1,2,7)
(7 single hub + 2 containing the hub-hub edge).

Constraint rows (18, scalar form):
    9 boundary capacity:  w_i + w_{i+1} = t_{i+1} - t_i        (w = arc half width)
    9 Voronoi tightness:  nearest-site distance at the triple point = R
Variables: the 22 centre coordinates (+R held fixed).  We report the rank, the null space,
and the covering radius along the null directions.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, acos

mp.dps = 40
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
S = mpf(10) ** 17
C0 = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in D['centers_scaled_1e17']]
R = mpf(D['certified_interval']['lo'])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
ORDER = [5, 7, 1, 8, 6, 4, 9, 10, 3]
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]


def circ(P, Q, W):
    ax, ay = P; bx, by = Q; cx, cy = W
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def bisect_pt(ci, cj, want_between=True):
    Ax = ci[0] - cj[0]; Ay = ci[1] - cj[1]
    Cc = ((ci[0] ** 2 + ci[1] ** 2) - (cj[0] ** 2 + cj[1] ** 2)) / 2
    dd = Ax * Ax + Ay * Ay
    A0x = Cc * Ax / dd; A0y = Cc * Ay / dd
    rem = 1 - (A0x * A0x + A0y * A0y)
    if rem <= 0:
        return None
    s = sqrt(rem) / sqrt(dd)
    cands = [(A0x + s * (-Ay), A0y + s * Ax), (A0x - s * (-Ay), A0y - s * Ax)]
    ai = atan2(ci[1], ci[0]) % (2 * pi); aj = atan2(cj[1], cj[0]) % (2 * pi)
    if aj < ai:
        aj += 2 * pi
    best = None
    for p in cands:
        th = atan2(p[1], p[0]) % (2 * pi)
        if th < ai:
            th += 2 * pi
        if ai - mpf('1e-9') <= th <= aj + mpf('1e-9'):
            best = p
    return best


def cons(x):
    C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
    rows = []
    for k in range(9):
        i = ORDER[k]; j = ORDER[(k + 1) % 9]
        si = sqrt(C[i][0] ** 2 + C[i][1] ** 2); sj = sqrt(C[j][0] ** 2 + C[j][1] ** 2)
        ti = atan2(C[i][1], C[i][0]) % (2 * pi); tj = atan2(C[j][1], C[j][0]) % (2 * pi)
        if tj < ti:
            tj += 2 * pi
        wi = acos((1 + si * si - R * R) / (2 * si)); wj = acos((1 + sj * sj - R * R) / (2 * sj))
        rows.append(wi + wj - (tj - ti))
    for tri in TRIPLES:
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        rows.append(min(sqrt((u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2) for c in C) - R)
    return rows


def jac(f, x, h=mpf('1e-25')):
    m = len(f(x)); n = len(x)
    J = np.zeros((m, n))
    for j in range(n):
        xp = list(x); xm = list(x)
        xp[j] += h; xm[j] -= h
        fp = f(xp); fm = f(xm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    return J


def gamma(x):
    C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
    best = mpf(0)
    for tri in itertools.combinations(range(11), 3):
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        if u[0] ** 2 + u[1] ** 2 > 1:
            continue
        d = min(sqrt((u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2) for c in C)
        best = max(best, d)
    for k in range(9):
        i = ORDER[k]; j = ORDER[(k + 1) % 9]
        p = bisect_pt(C[i], C[j])
        if p is None:
            continue
        if {i, j} != {min(range(11), key=lambda t: (p[0] - C[t][0]) ** 2 + (p[1] - C[t][1]) ** 2),
                      min(range(11), key=lambda t: (p[0] - C[t][0]) ** 2 + (p[1] - C[t][1]) ** 2)}:
            pass
        d = min(sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2) for c in C)
        best = max(best, d)
    return best


def main():
    x0 = [v for c in C0 for v in c]
    f0 = cons(x0)
    print('18 rows, residual max = %.3e' % float(max(abs(v) for v in f0)))
    for k, v in enumerate(f0):
        print('   row %2d = %s' % (k, nstr(v, 6)))
    print('\ngamma at the candidate = %s' % nstr(gamma(x0), 26))
    print('R (certified lo)      = %s' % nstr(R, 26))
    J = jac(cons, x0)
    u, s, vt = np.linalg.svd(J)
    print('\nsv:', ['%.4e' % y for y in s])
    rk = int((s > 1e-6 * s[0]).sum())
    print('rank=%d nullity=%d' % (rk, 22 - rk))
    N = vt[rk:].T
    print('\nnull directions (22 centre coordinates):')
    for k in range(N.shape[1]):
        print('  null %d:' % k, ' '.join('(c%d: %+.3f,%+.3f)' % (i, N[2 * i, k], N[2 * i + 1, k])
                                        for i in range(11) if abs(N[2 * i, k]) + abs(N[2 * i + 1, k]) > 0.15))
    print('\ngamma along the null directions (linear step only, no re-projection):')
    for k in range(N.shape[1]):
        out = []
        for t in (-1e-3, -1e-4, 1e-4, 1e-3):
            x = [x0[j] + mpf(t) * mpf(float(N[j, k])) for j in range(22)]
            out.append((t, float(gamma(x) - R)))
        print('   null %d: ' % k + '  '.join('t=%+.0e: %+.3e' % (t, d) for t, d in out))


if __name__ == '__main__':
    main()
