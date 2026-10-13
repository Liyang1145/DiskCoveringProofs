"""KKT / degeneracy test at the saved candidate (calibration only).

Free variables: the 22 centre coordinates (R held at its certified value).
Active constraints h_i(x) = 0, i = 1..18: the 9 boundary spokes (nearest-site distance
== R) and the 9 Voronoi-tight vertices (nearest-site distance == R).
Objective: gamma(x) = covering radius = max over the FULL critical set of the nearest-site
distance.  At the candidate gamma = R and 18 critical points share the maximum, so by
Danskin
        d gamma = max_k <grad r_k, dx>.
A first-order necessary condition for local minimality is
        exists mu in conv{grad r_k} with <mu, dx> = 0 for all dx in ker(J_h),
equivalently   dist(0, conv{grad r_k} + rowspan(J_h)) has a minimiser with 0 in the sum.

We also report the projection of the tight-point gradients onto ker(J_h): if some projected
gradient is NOT proportional to the others, a descent direction exists in the tangent space
and the candidate is not a local minimum of the covering radius.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, acos, atan2, pi, nstr

mp.dps = 40
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
Cf = [(mpf(int(a)) / mpf(10) ** 17, mpf(int(b)) / mpf(10) ** 17) for a, b in D['centers_scaled_1e17']]
R0 = mpf(float(D['certified_interval']['lo']))
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
H0, H2 = 0, 2
SPOKES = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6), (1, 2, 8), (1, 2, 7)]


def circ(P, Q, W):
    ax, ay = P; bx, by = Q; cx, cy = W
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def spoke(ci, cj, ang_i, ang_j, R):
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
        lo = ang_i % (2 * pi); hi = ang_j % (2 * pi)
        if hi < lo:
            hi += 2 * pi
        if th < lo:
            th += 2 * pi
        if lo - mpf('1e-9') <= th <= hi + mpf('1e-9'):
            return p
    raise RuntimeError('spoke branch')


def critical_distances(x, R, want_tight_only=False):
    """x = list of 22 coordinates.  Returns list of (value, grad wrt x) for the critical points
    that we treat as active: the 9 spokes and the 9 tight triples."""
    C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
    out = []
    for (i, j) in SPOKES:
        ai = atan2(C[i][1], C[i][0]) % (2 * pi)
        aj = atan2(C[j][1], C[j][0]) % (2 * pi)
        p = spoke(C[i], C[j], ai, aj, R)
        # nearest site: by construction both |p-ci| and |p-cj| equal R; take the first
        out.append(('spoke', (i, j), p, [i]))
    for tri in TRIPLES:
        v = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        out.append(('vert', tri, v, [tri[0]]))
    res = []
    for kind, tag, p, act in out:
        k = act[0]
        d = sqrt((p[0] - C[k][0]) ** 2 + (p[1] - C[k][1]) ** 2)
        res.append((kind, tag, p, k, d))
    return res


def numeric_grad(f, x, h):
    n = len(x)
    g = np.zeros(n)
    for j in range(n):
        xp = list(x); xm = list(x)
        xp[j] += h; xm[j] -= h
        fp = f(xp); fm = f(xm)
        g[j] = float((fp - fm) / (2 * h))
    return g


def main():
    x0 = []
    for i in range(11):
        x0 += [Cf[i][0], Cf[i][1]]
    print('== critical points at the candidate ==')
    pts = critical_distances(x0, R0)
    for kind, tag, p, k, d in pts:
        print('  %-5s %-10s d-R=%s  nearest=%d' % (kind, tag, nstr(d - R0, 4), k))
    h = mpf('1e-22')
    G = np.zeros((18, 22))
    J = np.zeros((18, 22))
    for r, (kind, tag, p, k, d) in enumerate(pts):
        def fz(xx, k=k):
            C = [(xx[2 * i], xx[2 * i + 1]) for i in range(11)]
            if kind == 'spoke':
                i, j = tag
                ai = atan2(C[i][1], C[i][0]) % (2 * pi); aj = atan2(C[j][1], C[j][0]) % (2 * pi)
                q = spoke(C[i], C[j], ai, aj, R0)
                return sqrt((q[0] - C[0][0]) ** 2 + (q[1] - C[0][1]) ** 2) * 0  # placeholder
            v = circ(C[tag[0]], C[tag[1]], C[tag[2]])
            return sqrt((v[0] - C[k][0]) ** 2 + (v[1] - C[k][1]) ** 2)
        G[r] = numeric_grad(lambda xx: radial_spoke_or_vert(xx, kind, tag, k, R0), x0, h)
        # constraint function: value - R
        J[r] = G[r]
    u, s, vt = np.linalg.svd(J)
    rk = int((s > 1e-7 * s[0]).sum())
    print('\nconstraint jacobian rank=%d (out of 18 rows), sv=%s' % (rk, ['%.3e' % y for y in s]))
    N = vt[rk:].T   # 22 x (22-rank) null space of the ACTIVE constraint jacobian
    print('null space dim =', N.shape[1])
    P = G @ N
    print('\ngradients of the 18 tight-point distances projected on the null space:')
    for r in range(18):
        print('  %2d %-5s %-10s |proj|=%.6f  |fullgrad|=%.6f' %
              (r, pts[r][0], str(pts[r][1]), np.linalg.norm(P[r]), np.linalg.norm(G[r])))
    # is the candidate a KKT point?  min over convex weights of || sum_k w_k P_k ||  subject to
    # the *feasible tangent* = full null space; then the direction of the nonzero projection
    # with the LARGEST projection is a descent direction.
    print('\nmax over rows of |proj of grad r_k on ker J| = %.6f' % max(np.linalg.norm(P[r]) for r in range(18)))
    # weight each row by the component along the top right singular vector of P
    u2, s2, vt2 = np.linalg.svd(P)
    print('singular values of the projected gradient matrix P (18x%d):' % N.shape[1], ['%.4f' % y for y in s2])
    dirvec = N @ vt2[0]
    print('top projected-gradient direction (22-vector, centres):')
    for i in range(11):
        print('   c%2d  (%+.6f, %+.6f)' % (i, dirvec[2 * i] * 100, dirvec[2 * i + 1] * 100))
    # second-order sanity: step along the descending direction and watch the (full) covering radius
    print('\nstep test: move along -top direction, project back to the constraint manifold, report gamma')
    for t in (1e-4, 1e-3, 1e-2):
        x = np.array([float(v) for v in x0]) - t * dirvec
        gam = full_covering_radius(x)
        print('   t=%8.1e  gamma=%.17f' % (t, gam))


def radial_spoke_or_vert(xx, kind, tag, k, R):
    C = [(xx[2 * i], xx[2 * i + 1]) for i in range(11)]
    if kind == 'spoke':
        i, j = tag
        ai = atan2(C[i][1], C[i][0]) % (2 * pi); aj = atan2(C[j][1], C[j][0]) % (2 * pi)
        q = spoke(C[i], C[j], ai, aj, R)
    else:
        q = circ(C[tag[0]], C[tag[1]], C[tag[2]])
    return sqrt((q[0] - C[k][0]) ** 2 + (q[1] - C[k][1]) ** 2)


def full_covering_radius(x):
    """max over the full critical set (all Voronoi vertices in D + all boundary spokes)."""
    C = [(mpf(x[2 * i]), mpf(x[2 * i + 1])) for i in range(11)]
    best = mpf(0)
    for tri in itertools.combinations(range(11), 3):
        try:
            v = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        except ZeroDivisionError:
            continue
        if v[0] ** 2 + v[1] ** 2 > 1:
            continue
        d = min(sqrt((v[0] - c[0]) ** 2 + (v[1] - c[1]) ** 2) for c in C)
        best = max(best, d)
    ang = sorted([(atan2(C[i][1], C[i][0]) % (2 * pi), i) for i in RINGS])
    order = [i for a, i in ang]
    for k in range(9):
        i = order[k]; j = order[(k + 1) % 9]
        if (i, j) in SPOKES or (j, i) in SPOKES:
            pass
        A, B = C[i], C[j]
        dx = B[0] - A[0]; dy = B[1] - A[1]
        L2 = dx * dx + dy * dy
        t = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / (2 * L2)
        fx = A[0] + t * dx; fy = A[1] + t * dy
        rem = 1 - (fx * fx + fy * fy)
        if rem <= 0:
            continue
        for sg in (mpf(1), mpf(-1)):
            px = fx + sg * sqrt(rem) * (-dy) / sqrt(L2)
            py = fy + sg * sqrt(rem) * dx / sqrt(L2)
            d = min(sqrt((px - c[0]) ** 2 + (py - c[1]) ** 2) for c in C)
            best = max(best, d)
    return float(best)


if __name__ == '__main__':
    main()
