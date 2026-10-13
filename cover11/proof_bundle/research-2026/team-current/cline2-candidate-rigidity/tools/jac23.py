"""Rank of the ACTIVE tight-point system at the saved candidate, general coordinates.

Variables (23): 22 center coordinates (x_i,y_i), i=0..10, plus R.
Constraints (45):
  * 9 spokes (ring-ring neighbour pairs of the induced angular order):
      |v|^2 = 1,  |v-c_i|^2 = R^2,  |v-c_j|^2 = R^2
    where v is the branch of the two-circle intersection on bd D lying between c_i,c_j.
  * 9 tight Voronoi triples: symmetric equidistance rows for the 3 pairs.
NO symmetry is assumed anywhere: all 22 coordinates are independent.

Rank / nullity of the Jacobian at the (rounded) candidate decides whether the active
system pins the configuration up to the two trivial gauges (rotation: 1, scale via R: the
whole system is not scale invariant because |v|=1, so only rotation).
"""
import json, io, itertools, sys
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, acos, atan2, cos, sin, pi, nstr
import numpy as np

mp.dps = 60
ROOT = Path(__file__).resolve().parents[4]
OBJ = ROOT / 'n11' / 'upper' / 'certified_object.json'

TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]
SPOKES = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]


def load():
    d = json.load(io.open(OBJ, encoding='utf-8-sig'))
    S = mpf(10) ** 17
    C = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in d['centers_scaled_1e17']]
    return d, C


def spoke_branch(ci, cj, R, ang_i, ang_j):
    """Branch of {|v|=1, |v-ci|=R, |v-cj|=R} whose polar angle lies in [ang_i, ang_j]."""
    ax = 2 * (ci[0] - cj[0]); ay = 2 * (ci[1] - cj[1])
    b = (ci[0] ** 2 + ci[1] ** 2) - (cj[0] ** 2 + cj[1] ** 2)
    nrm2 = ax * ax + ay * ay
    t = b / nrm2
    fx, fy = ax * t, ay * t
    L2 = 1 - (fx * fx + fy * fy)
    if L2 <= 0:
        return None
    s = sqrt(L2) / sqrt(nrm2)
    cands = [(fx - s * ay, fy + s * ax), (fx + s * ay, fy - s * ax)]
    for p in cands:
        th = atan2(p[1], p[0]) % (2 * pi)
        lo = ang_i % (2 * pi); hi = ang_j % (2 * pi)
        if hi < lo:
            hi += 2 * pi
        if th < lo:
            th += 2 * pi
        if lo - mpf('1e-6') <= th <= hi + mpf('1e-6'):
            return p
    return None


def F(z):
    C = [(z[2 * i], z[2 * i + 1]) for i in range(11)]
    R = z[22]
    out = []
    for (i, j) in SPOKES:
        ai = atan2(C[i][1], C[i][0]); aj = atan2(C[j][1], C[j][0])
        v = spoke_branch(C[i], C[j], R, ai, aj)
        if v is None:
            raise RuntimeError('spoke branch lost')
        out.append(v[0] ** 2 + v[1] ** 2 - 1)
        out.append((v[0] - C[i][0]) ** 2 + (v[1] - C[i][1]) ** 2 - R * R)
        out.append((v[0] - C[j][0]) ** 2 + (v[1] - C[j][1]) ** 2 - R * R)
    for tri in TRIPLES:
        for a, b in itertools.combinations(tri, 2):
            A = C[a]; B = C[b]
            out.append((A[0] - B[0]) ** 2 + (A[1] - B[1]) ** 2)  # placeholder replaced below
    # the symmetric rows are added by the caller through Fsym
    return out


def Fsym(z):
    C = [(z[2 * i], z[2 * i + 1]) for i in range(11)]
    R = z[22]
    rows = []
    for (i, j) in SPOKES:
        ai = atan2(C[i][1], C[i][0]); aj = atan2(C[j][1], C[j][0])
        v = spoke_branch(C[i], C[j], R, ai, aj)
        rows.append(v[0] ** 2 + v[1] ** 2 - 1)
        rows.append((v[0] - C[i][0]) ** 2 + (v[1] - C[i][1]) ** 2 - R * R)
        rows.append((v[0] - C[j][0]) ** 2 + (v[1] - C[j][1]) ** 2 - R * R)
    for tri in TRIPLES:
        a, b, c = tri
        A, B, Cc = C[a], C[b], C[c]
        A2 = A[0] ** 2 + A[1] ** 2
        B2 = B[0] ** 2 + B[1] ** 2
        C2 = Cc[0] ** 2 + Cc[1] ** 2
        # symmetric 3x3 linear system 2*[B-A; C-A] u = [B2-A2; C2-A2]
        for q1, q2, S1, S2 in ((a, b, A2, B2), (a, c, A2, C2), (b, c, B2, C2)):
            P = C[q1]; Q = C[q2]
            rows.append(2 * ((Q[0] - P[0]) * 0 + 0) * 0 + 0)  # placeholder
    return rows


def Fsym2(z):
    """Symmetric equidistance rows for the tight Voronoi triples.

    For the triple (a,b,c) the tight point u satisfies the two linear equations
    u.(B-A) = (B2-A2)/2, u.(C-A) = (C2-A2)/2.  We use the three symmetric rows
        u.(B-A) - (B2-A2)/2,  u.(C-A) - (C2-A2)/2,  u.(C-B) - (C2-B2)/2
    evaluated at u = the weighted circumcentre of A,B,C, written in the symmetric form
    u = (alpha*A + beta*B + gamma*C) with alpha = |B-C|^2*(A2 - ... )/D ... instead we
    simply solve the 2x2 system explicitly; the three rows are then automatically
    symmetric in form though not in expression.
    """
    C = [(z[2 * i], z[2 * i + 1]) for i in range(11)]
    R = z[22]
    rows = []
    for (i, j) in SPOKES:
        ai = atan2(C[i][1], C[i][0]); aj = atan2(C[j][1], C[j][0])
        v = spoke_branch(C[i], C[j], R, ai, aj)
        rows.append(v[0] ** 2 + v[1] ** 2 - 1)
        rows.append((v[0] - C[i][0]) ** 2 + (v[1] - C[i][1]) ** 2 - R * R)
        rows.append((v[0] - C[j][0]) ** 2 + (v[1] - C[j][1]) ** 2 - R * R)
    for tri in TRIPLES:
        A, B, Cc = C[tri[0]], C[tri[1]], C[tri[2]]
        A2 = A[0] ** 2 + A[1] ** 2
        B2 = B[0] ** 2 + B[1] ** 2
        C2 = Cc[0] ** 2 + Cc[1] ** 2
        d1 = B[0] - A[0]; d2 = B[1] - A[1]
        e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
        D = 2 * (d1 * e2 - d2 * e1)
        bx = (B2 - A2) / 2; by = (C2 - A2) / 2
        ux = (bx * e2 - by * d2) / (d1 * e2 - d2 * e1)
        uy = (d1 * by - e1 * bx) / (d1 * e2 - d2 * e1)
        ux = (bx * e2 - by * d2) / (d1 * e2 - d2 * e1)
        uy = (d1 * by - e1 * bx) / (d1 * e2 - d2 * e1)
        rows.append((ux - A[0]) ** 2 + (uy - A[1]) ** 2 - R * R)
        rows.append((ux - B[0]) ** 2 + (uy - B[1]) ** 2 - R * R)
        rows.append((ux - Cc[0]) ** 2 + (uy - Cc[1]) ** 2 - R * R)
    return rows


def main():
    d, C = load()
    R0 = mpmathify(d['certified_interval']['lo'])
    z0 = []
    for c in C:
        z0 += [c[0], c[1]]
    z0.append(R0)
    f0 = Fsym2(z0)
    print('m=%d rows, n=%d vars' % (len(f0), len(z0)))
    print('max |residual| = %s' % nstr(max(abs(v) for v in f0), 6))
    for k, v in enumerate(f0):
        print('   f[%2d] = %s' % (k, nstr(v, 6)))
    h = mpf('1e-25')
    m, n = len(f0), len(z0)
    J = np.zeros((m, n))
    for j in range(n):
        zp = list(z0); zm = list(z0)
        zp[j] += h; zm[j] -= h
        fp = Fsym2(zp); fm = Fsym2(zm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    np.save(ROOT / 'research-2026' / 'team-current' / 'cline2-candidate-rigidity' / 'out' / 'J23.npy', J)
    u, s, vt = np.linalg.svd(J)
    print('\nsingular values:'); print(['%.4e' % x for x in s])
    rk = int((s > 1e-6 * s[0]).sum())
    print('rank=%d  nullity=%d  (n=%d)' % (rk, n - rk, n))
    labels = ['x%d' % i if k % 2 == 0 else 'y%d' % i for i in range(11) for k in (0, 1)] + ['R']
    for k in range(1, min(n - rk, 4) + 1):
        vv = vt[-k]
        print('\nnull vector sv=%.3e:' % s[-k])
        for lab, val in zip(labels, vv):
            if abs(val) > 1e-3:
                print('    %-4s %+.6f' % (lab, val))


if __name__ == '__main__':
    main()
