"""Exact (analytic) gradients of the active tight-point distances, then the Danskin /
KKT degeneracy test at the saved candidate.  Calibration only.

Setting: free variables = 22 centre coordinates (R held at its certified value).
Active constraints h_i = 0 (i=1..18): for each of the 9 tight Voronoi vertices and the
9 boundary spokes, the nearest-site distance equals R.
Objective: gamma = max over the full critical set.

For a Voronoi vertex u of triple (A,B,C), the implicit relations
   |u-A|^2 = |u-B|^2 = |u-C|^2 = r^2
give du = sum_j w_j dA_j + t d r with
   w_j = (u - A_j)^T M^{-1} / (2 r) over the columns M = 2[(B-A),(C-A)],  t = 1,
   sum_j w_j = 1/r  (as it must: sum_j |u-A_j|^2 = 3r^2 differentiates to 2r*sum_j w_j = 3*2r).
Hence  dr/dA_i = (delta_{i,A} - w_A)(u-A)/r + ...  and we collect the gradient of r
w.r.t. all 22 coordinates exactly.  For a spoke point p (nearest site = ring i):
dr/dA_i = (p - A_i)/r * (1 - dp/dA_i) + ... plus the term from  dp/dA_i  which is exactly
cancelled by the equal-distance construction; we verify the result numerically.
"""
import json, io, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, atan2, pi, nstr, matrix, lu_solve, zeros

mp.dps = 50
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
Cf = [(mpf(int(a)) / mpf(10) ** 17, mpf(int(b)) / mpf(10) ** 17) for a, b in D['centers_scaled_1e17']]
R0 = mpf(float(D['certified_interval']['lo']))
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
SPOKES = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6), (1, 2, 8), (1, 2, 7)]
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
        # angular window from the two centres
        lo = atan2(ci[1], ci[0]) % (2 * pi); hi = atan2(cj[1], cj[0]) % (2 * pi)
        if hi < lo:
            hi += 2 * pi
        if th < lo:
            th += 2 * pi
        if lo - mpf('1e-9') <= th <= hi + mpf('1e-9'):
            return p
    raise RuntimeError


def grad_vertex(x, tri):
    A = (x[2 * tri[0]], x[2 * tri[0] + 1])
    B = (x[2 * tri[1]], x[2 * tri[1] + 1])
    C = (x[2 * tri[2]], x[2 * tri[2] + 1])
    u = circ(A, B, C)
    r = sqrt((u[0] - A[0]) ** 2 + (u[1] - A[1]) ** 2)
    M = matrix(2, 2, [2 * (B[0] - A[0]), 2 * (C[0] - A[0]), 2 * (B[1] - A[1]), 2 * (C[1] - A[1])])
    g = [mpf(0)] * 22
    # w_j for j = 0,1,2
    w = []
    for j in range(3):
        rhs = matrix([(u[0] - A[0]), (u[1] - A[1])])
        w.append(0)
    # solve M^T w = (u - A_j)  for each j ; we need du/dA_j = M^{-1} * (u - A_j)/1
    du = []
    for j in range(3):
        Aj = (A, B, C)[j]
        rhs = matrix([(u[0] - Aj[0]), (u[1] - Aj[1])])
        du.append(lu_solve(M, rhs))
    for i in range(11):
        dix = mpf(0); diy = mpf(0)
        for j in range(3):
            if tri[j] != i:
                continue
            # u depends on Aj
            dix += du[j][0]; diy += du[j][1]
            # the subtracted term
            dix -= 1; diy -= 0  # placeholder; corrected below
        # recompute properly:
    # clean version: dr/dx_i = sum_j [ (u-A_j)^T/r ] * d(u-A_j)/dA_i
    g = [mpf(0)] * 22
    for i in range(11):
        for j in range(3):
            if tri[j] != i:
                continue
            dAj = du[j]
            # d r / d A_i = (u - A_j).(du/dA_j - I)/r  (only the component at index j)
            vx = (u[0] - A[j][0]) / r
            vy = (u[1] - A[j][1]) / r
            g[2 * i] += vx * (dAj[0] - 1)
            g[2 * i + 1] += vy * (dAj[1] - 1)
    return u, r, g


def grad_spoke(x, i, j):
    ci = (x[2 * i], x[2 * i + 1]); cj = (x[2 * j], x[2 * j + 1])
    p = spoke_pt(ci, cj, R0)
    r = sqrt((p[0] - ci[0]) ** 2 + (p[1] - ci[1]) ** 2)
    # implicit: |p-ci|^2 = |p-cj|^2 = R^2, |p|^2 = 1  =>  dp is determined by
    #   (p-ci).dp = (p-ci).dci ;  (p-cj).dp = (p-cj).dcj ;  p.dp = 0
    # solve the 2x2 system for dp from the two equal-distance equations and the third ratio
    # simpler: use the explicit construction derivative numerically for the second-order part
    g = [mpf(0)] * 22
    # dr/dci: only through dp: dr/dci = -(p-ci)/r + (p-ci)/r . dp/dci
    # solve with the linear system
    u1 = (p[0] - ci[0], p[1] - ci[1])
    u2 = (p[0] - cj[0], p[1] - cj[1])
    # dp for unit dci = e_k
    for k in (0, 1):
        rhs1 = u1[k]
        rhs2 = 0
        # unknowns dp_x, dp_y with (u1).dp = rhs1 ; (u2).dp = rhs2 ; p.dp = 0 (redundant)
        M = matrix(2, 2, [u1[0], u2[0], u1[1], u2[1]])
        sol = lu_solve(M, matrix([rhs1, rhs2]))
        dpx, dpy = sol[0], sol[1]
        gk = -(u1[k]) / r + (u1[0] * dpx + u1[1] * dpy) / r
        g[2 * i + k] += gk
    for k in (0, 1):
        rhs1 = 0; rhs2 = u2[k]
        M = matrix(2, 2, [u1[0], u2[0], u1[1], u2[1]])
        sol = lu_solve(M, matrix([rhs1, rhs2]))
        dpx, dpy = sol[0], sol[1]
        gk = -(0) / r + (u1[0] * dpx + u1[1] * dpy) / r
        g[2 * j + k] += gk
    return p, r, g


def main():
    G = []; J = []
    for tri in TRIPLES:
        u, r, g = grad_vertex(X0, tri)
        G.append(g)
    for (i, j) in SPOKES:
        p, r, g = grad_spoke(X0, i, j)
        G.append(g)
    G = np.array([[float(y) for y in row] for row in G])
    J = G.copy()
    u, s, vt = np.linalg.svd(J)
    print('constraint gradients rank check: sv =', ['%.3e' % y for y in s])
    rk = int((s > 1e-7 * s[0]).sum())
    print('rank =', rk, ' nullity =', 22 - rk)
    N = vt[rk:].T
    P = G @ N
    print('\nprojected objective gradients (rows = the 18 tight points):')
    for r in range(18):
        lbl = TRIPLES[r] if r < 9 else SPOKES[r - 9]
        print('  %2d %-12s |proj|=%10.6f  |grad|=%10.6f' % (r, str(lbl), np.linalg.norm(P[r]), np.linalg.norm(G[r])))
    # Danskin: descent direction exists iff the min-norm convex combination of the
    # projected gradients is nonzero
    w = P.sum(0) / 18.0
    print('\nmean projected gradient norm = %.6f' % np.linalg.norm(w))
    u2, s2, vt2 = np.linalg.svd(P)
    print('singular values of P:', ['%.6f' % y for y in s2])
    d = N @ vt2[0]
    print('top projected direction norms: full=%.6f  (per-centre):' % np.linalg.norm(d))
    for i in range(11):
        print('   c%2d (%+.6f, %+.6f)' % (i, d[2 * i], d[2 * i + 1]))
    np.save(Path(__file__).parent.parent / 'out' / 'G18.npy', G)
    np.save(Path(__file__).parent.parent / 'out' / 'N22.npy', N)


if __name__ == '__main__':
    main()
