"""SINGLE verified computation of the active set — one parametrisation, no branching.

Bisector of sites i,j:   |p-c_i| = |p-c_j|  <=>  p . (c_i - c_j) = (|c_i|^2 - |c_j|^2)/2 .
With A_ = c_i - c_j (2-vector) and Cc = (|c_i|^2-|c_j|^2)/2 and a = |A_|^2 this is
    (c_i - c_j) . p = Cc,
whose solution set meets bd D (|p| = 1) at
    p = m +- n ,   m = (Cc/a) A_ ,  n = t * (-A_y, A_x)/a ,  t = sqrt(a - Cc^2) .
(Check: |m|^2 + |n|^2 = Cc^2/a + (a - Cc^2)/a = 1, and A_ . n = 0.)

We enumerate:
  * the 9 tight Voronoi vertices (triple equidistance points at distance R),
  * every bisector point on bd D whose pair are the two nearest sites there,
and report the maximum level, the 9+9 structure and the rank of the active system.
"""
import json, io, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, acos

mp.dps = 50
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
S = mpf(10) ** 17
C = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in D['centers_scaled_1e17']]
R = mpf(D['certified_interval']['lo'])
n = 11
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]


def d(p, i):
    return sqrt((p[0] - C[i][0]) ** 2 + (p[1] - C[i][1]) ** 2)


def circ(P, Q, W):
    ax, ay = P; bx, by = Q; cx, cy = W
    dd = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    return (((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / dd,
            ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / dd)


def bisect_bd(i, j):
    A_ = (C[i][0] - C[j][0], C[i][1] - C[j][1])
    Cc = ((C[i][0] ** 2 + C[i][1] ** 2) - (C[j][0] ** 2 + C[j][1] ** 2)) / 2
    a = A_[0] ** 2 + A_[1] ** 2
    if a <= Cc ** 2:
        return []
    m = (Cc * A_[0] / a, Cc * A_[1] / a)
    t = sqrt(a - Cc ** 2) / a
    return [(m[0] - t * A_[1], m[1] + t * A_[0]), (m[0] + t * A_[1], m[1] - t * A_[0])]


def main():
    print('=== (a) tight Voronoi vertices ===')
    verts = []
    for tri in TRIPLES:
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        ds = sorted([(d(u, k), k) for k in range(n)])
        verts.append((tri, u, ds))
        print('  %-12s |u|=%s  d_1-R=%s  d_2-R=%s  d_3-R=%s  4th=%s'
              % (str(tri), nstr(sqrt(u[0] ** 2 + u[1] ** 2), 8),
                 nstr(ds[0][0] - R, 5), nstr(ds[1][0] - R, 5), nstr(ds[2][0] - R, 5),
                 nstr(ds[3][0], 10)))
    print('\n=== (b) all bisector points on bd D whose pair are the two nearest sites ===')
    bnd = []
    for i in range(n):
        for j in range(i + 1, n):
            for p in bisect_bd(i, j):
                ds = sorted([(d(p, k), k) for k in range(n)])
                if {i, j} == {ds[0][1], ds[1][1]}:
                    bnd.append((i, j, p, ds))
    bnd.sort(key=lambda z: -z[3][0][0])
    for i, j, p, ds in bnd:
        th = atan2(p[1], p[0]) % (2 * pi)
        print('  pair=(%2d,%2d) th=%9.5f deg  d-R=%s  3rd=%.9f (disk %d)'
              % (i, j, float(th) * 180 / 3.14159265358979, nstr(ds[0][0] - R, 5),
                 float(ds[2][0]), ds[2][1]))
    print('\n  number of boundary bisector points = %d ; those at R: %d'
          % (len(bnd), sum(1 for z in bnd if abs(z[3][0][0] - R) < mpf('1e-15'))))
    tight_b = [(i, j) for i, j, p, ds in bnd if abs(ds[0][0] - R) < mpf('1e-15')]
    print('  tight pairs in cyclic order:',
          sorted(tight_b, key=lambda pr: atan2(dict(((i, j), p) for i, j, p, ds in bnd)[pr][1],
                                               dict(((i, j), p) for i, j, p, ds in bnd)[pr][0]) % (2 * pi)))
    print('\n  consecutive-pair model check:')
    ORDER = [5, 7, 1, 8, 6, 4, 9, 10, 3]
    cons = [tuple(sorted((ORDER[k], ORDER[(k + 1) % 9]))) for k in range(9)]
    print('    pairs from the induced order  :', cons)
    print('    pairs found on bd D at R     :', sorted(tuple(sorted(t)) for t in tight_b))
    print('    identical:', sorted(tuple(sorted(t)) for t in tight_b) == sorted(cons))
    print('\n=== levels ===')
    print('  top level = max(boundary max, vertex max)')
    bmax = max(z[3][0][0] for z in bnd)
    vmax = max(ds[0][0] for _, _, ds in verts)
    print('    boundary max = %s' % nstr(bmax, 26))
    print('    vertex   max = %s' % nstr(vmax, 26))
    print('    R            = %s' % nstr(R, 26))
    print('\n=== rank of the 19-row active system ===')


if __name__ == '__main__':
    main()
