"""Rank / nullspace of the ACTIVE tight-point system at the saved candidate. Calibration only.

Parameter vector z (14 entries)
  z[0..8]  : polar angles t_k of the 9 ring disks, indexed by the angular order
  z[9,10]  : hub-1 center (u1,v1)
  z[11,12] : hub-2 center (u2,v2)
  z[13]    : radius R
Ring centers are (s_k cos t_k, s_k sin t_k) with |c_k| = s_k free (not parameterised).

Constraint vector f (33 entries), one row each:
  * 9 spoke equations   w_i + w_j - (t_j - t_i) = 0        (boundary arc capacity saturated)
  * 8 Voronoi-triple rows of 3 equations each: r_v(centre) = R for the three generating
    sites of each tight Voronoi vertex.

All coordinates are treated as exact reals; the saved object is a rational rounding of
the true algebraic configuration, so residuals are only of order 1e-17.
"""
import json, io
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, acos, atan2, cos, sin, pi, nstr
import numpy as np

mp.dps = 60
ROOT = Path(__file__).resolve().parents[4]
OBJ = ROOT / 'n11' / 'upper' / 'certified_object.json'

TIGHT_TRIPLES = [
    (0, 9, 10),   # hub-hub edge + ring 0
    (0, 2, 5),    # hub-hub edge + ring 5
    (0, 3, 5),    # ring 0 + one hub + rings 3,5
    (2, 6, 8),    # ring 2 + one hub + rings 6,8
    (2, 5, 7),
    (0, 4, 6),
    (0, 2, 6),
    (1, 2, 8),
    (1, 2, 7),
]


def load():
    d = json.load(io.open(OBJ, encoding='utf-8-sig'))
    S = mpf(10) ** 17
    C = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in d['centers_scaled_1e17']]
    return d, C


def build():
    d, C = load()
    R0 = mpmathify(d['certified_interval']['lo'])
    rings = [1, 3, 4, 5, 6, 7, 8, 9, 10]
    h0, h2 = 0, 2
    A = sorted([(atan2(C[i][1], C[i][0]) % (2 * pi), i) for i in rings])
    order = [i for a, i in A]
    ang0 = {i: a for a, i in A}
    angfl = {i: float(a) for a, i in A}
    return d, C, R0, h0, h2, order, ang0, angfl


D, C0, R0, H0, H2, ORDER, ANG, ANGF = build()


def centers(t, u1, v1, u2, v2):
    out = {}
    for k, i in enumerate(ORDER):
        s = ANG[i]
        out[i] = (s * cos(t[k]), s * sin(t[k]))
    out[H0] = (u1, v1)
    out[H2] = (u2, v2)
    return out


def circum(P, Q, W):
    ax, ay = P
    bx, by = Q
    cx, cy = W
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def F(z):
    t = list(z[:9])
    u1, v1, u2, v2, R = z[9], z[10], z[11], z[12], z[13]
    cc = centers(t, u1, v1, u2, v2)
    out = []
    # spokes
    for k in range(9):
        i = ORDER[k]
        j = ORDER[(k + 1) % 9]
        a = ANG[i]
        b = ANG[j]
        if b < a:
            b += 2 * pi
        wi = acos((1 + a * a - R * R) / (2 * a))
        wj = acos((1 + b * b - R * R) / (2 * b))
        out.append(wi + wj - (b - a))
    # tight Voronoi triples
    for tri in TIGHT_TRIPLES:
        P, Q, W = cc[tri[0]], cc[tri[1]], cc[tri[2]]
        V = circum(P, Q, W)
        for S in (P, Q, W):
            out.append((V[0] - S[0]) ** 2 + (V[1] - S[1]) ** 2 - R * R)
    return out


def main():
    z0 = [ANG[i] for i in ORDER] + [C0[H0][0], C0[H0][1], C0[H2][0], C0[H2][1], R0]
    f0 = F(z0)
    m, n = len(f0), len(z0)
    print('variables n=%d (9 ring angles, 2 hubs x2, R);  constraints m=%d' % (n, m))
    print('max |residual| at candidate = %s' % nstr(max(abs(v) for v in f0), 8))
    for k, v in enumerate(f0):
        print('   f[%2d] = %s' % (k, nstr(v, 8)))
    h = mpf('1e-25')
    J = np.zeros((m, n))
    for j in range(n):
        zp = list(z0); zm = list(z0)
        zp[j] += h; zm[j] -= h
        fp = F(zp); fm = F(zm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    np.save(Path(__file__).parent.parent / 'out' / 'J_tight.npy', J)
    u, s, vt = np.linalg.svd(J)
    print('\nsingular values (m=%d x n=%d):' % (m, n))
    print(['%.4e' % x for x in s])
    rk = int((s > 1e-6 * s[0]).sum())
    print('rank = %d   nullity = %d' % (rk, n - rk))
    labels = ['t(%d)' % i for i in ORDER] + ['u1', 'v1', 'u2', 'v2', 'R']
    print('labels:', labels)
    for k in range(1, min(n - rk, 5) + 1):
        print('null vector sv=%.2e :' % s[-k], np.round(vt[-k], 8))
    return J, s, vt


if __name__ == '__main__':
    main()
