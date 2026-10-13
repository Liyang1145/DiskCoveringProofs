"""Second-order behaviour of the covering radius along the active constraint family.

Correct critical set (verified in tools/crit_set.py): for this configuration the maximum of
the nearest-site distance over the unit disk is attained by exactly 18 points, all at
distance R:  the 9 boundary spokes (perpendicular-bisector intersections with bd D, three
sites with 4 or 6 nearest) and the 9 tight Voronoi vertices.  Below them the next critical
value is 0.37883 (gap 1.15e-3).

Family: solutions of the 18 active equations with R fixed at the certified endpoint,
rotation gauge fixed by pinning x(center 1).  Steps are taken along the null directions of
the constraint Jacobian and projected back with a null-space-restricted Newton iteration.
We then record gamma = max over the FULL critical set and fit g(t) = g0 + a t + b t^2.
"""
import json, io, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr

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


def spoke_pt(ci, cj):
    ax = 2 * (ci[0] - cj[0]); ay = 2 * (ci[1] - cj[1])
    b = (ci[0] ** 2 + ci[1] ** 2) - (cj[0] ** 2 + cj[1] ** 2)
    n2 = ax * ax + ay * ay
    t = b / n2
    fx, fy = ax * t, ay * t
    L2 = 1 - (fx * fx + fy * fy)
    if L2 <= 0:
        return None
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
    return None


def nearest_dist(x, p):
    C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
    return min(sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2) for c in C)


def cons(x):
    C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
    rows = [C[1][0] - Cf[1][0]]
    for (i, j) in SPOKES:
        p = spoke_pt(C[i], C[j])
        if p is None:
            raise RuntimeError('spoke')
        rows.append(nearest_dist(x, p) - R0)
    for tri in TRIPLES:
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        rows.append(nearest_dist(x, u) - R0)
    return rows


def jac(f, x, h):
    n = len(x); m = len(f(x))
    J = np.zeros((m, n))
    for j in range(n):
        xp = list(x); xm = list(x)
        xp[j] += h; xm[j] -= h
        fp = f(xp); fm = f(xm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    return J


def gamma(x):
    """max over the full critical set: all triple Voronoi vertices in D + all 9 boundary
    perpendicular-bisector intersections inside the disk."""
    C = [(mpf(x[2 * i]), mpf(x[2 * i + 1])) for i in range(11)]
    best = mpf(0)
    for tri in itertools.combinations(range(11), 3):
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        if u[0] ** 2 + u[1] ** 2 > 1:
            continue
        d = min(sqrt((u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2) for c in C)
        if d > best:
            best = d
    for (i, j) in SPOKES:
        p = spoke_pt(C[i], C[j])
        if p is not None:
            d = min(sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2) for c in C)
            if d > best:
                best = d
    return best


def newton(x, N, h=mpf('1e-20'), iters=40):
    x = [mpf(v) for v in x]
    for it in range(iters):
        f = cons(x)
        if max(abs(v) for v in f) < mpf('1e-28'):
            break
        J = jac(cons, x, h)
        JN = J @ N
        dz = np.linalg.lstsq(JN, np.array([float(v) for v in f]), rcond=None)[0]
        x = [mpf(v) for v in (np.array([float(v) for v in x]) - N @ dz)]
    return x


def main():
    x0 = [mpf(v) for v in X0]
    print('residual at candidate: %.3e' % float(max(abs(v) for v in cons(x0))))
    print('gamma(x0) = %s' % nstr(gamma(x0), 24))
    print('R        = %s' % nstr(R0, 24))
    J = jac(cons, x0, mpf('1e-20'))
    u, s, vt = np.linalg.svd(J)
    print('sv:', ['%.4e' % y for y in s])
    rk = int((s > 1e-7 * s[0]).sum())
    print('rank=%d nullity=%d' % (rk, 22 - rk))
    N = vt[rk:].T
    g0 = gamma(x0)
    print('\nnull-direction step tests (gamma after Newton projection):')
    for k in range(N.shape[1]):
        ts = [-2e-3, -1e-3, -3e-4, -1e-4, 0.0, 1e-4, 3e-4, 1e-3, 2e-3]
        vals = {}
        for t in ts:
            x = np.array([float(v) for v in x0]) + t * N[:, k]
            x = newton(x.tolist(), N)
            vals[t] = float(gamma([mpf(v) for v in x]))
        A = np.array([[1, t, t * t] for t in ts])
        b = np.array([vals[t] for t in ts])
        coef = np.linalg.lstsq(A, b, rcond=None)[0]
        res = max(abs(A @ coef - b))
        print(' null %d: a=%+.6e  b=%+.6e  (maxres %.2e)' % (k, coef[1], coef[2], res))
        print('   ', ' '.join('%+.0e:%+.16f' % (t, vals[t]) for t in ts))


if __name__ == '__main__':
    main()
