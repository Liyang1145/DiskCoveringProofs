"""DECISIVE audit of the T_cert literal + hub-hub geometry (no new theory, exact code).

Part 1: covering radius of the SAVED witness, computed from the exact rational centre data
        at 60 dps, via the complete critical set.  Compared against
          * the registered certified interval of the object,
          * the literal T_cert = 0.379983853119838689722261606136093214308718957.
Part 2: is the value 0.379983853119838689722261606136093214308718957 > covering radius of
        the witness?  If any critical point of the witness lies ABOVE it, that literal cannot
        be the witness's covering radius (it would be a radius at which the witness does NOT
        cover D).
Part 3: hub-hub geometry: |c0-c2| vs 2R, and whether the two hub cells share a Voronoi edge.
"""
import json, io, itertools
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, acos

mp.dps = 60
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
S = mpf(10) ** 17
C = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in D['centers_scaled_1e17']]
n = 11
T_LIT = mpf('0.379983853119838689722261606136093214308718957')
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
ORDER = [5, 7, 1, 8, 6, 4, 9, 10, 3]


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
    print('=== PART 1: covering radius of the saved witness (60 dps, exact rationals) ===')
    lo = mpf(D['certified_interval']['lo']); hi = mpf(D['certified_interval']['hi'])
    print('registered interval  lo = %s' % nstr(lo, 62))
    print('registered interval  hi = %s' % nstr(hi, 62))
    print('claim literal  T_cert   = %s' % nstr(T_LIT, 60))
    print('T_LIT - lo = %s     T_LIT - hi = %s' % (nstr(T_LIT - lo, 8), nstr(T_LIT - hi, 8)))
    print()
    pts = []
    for tri in itertools.combinations(range(n), 3):
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        if u[0] ** 2 + u[1] ** 2 > 1:
            continue
        pts.append(('V%s' % (tri,), u, min((d(u, k), k) for k in range(n))))
    for i in range(n):
        for j in range(i + 1, n):
            for p in bisect_bd(i, j):
                ds = sorted([(d(p, k), k) for k in range(n)])
                if {i, j} == {ds[0][1], ds[1][1]}:
                    pts.append(('B(%d,%d)' % (i, j), p, ds[0]))
    pts.sort(key=lambda z: -z[2][0])
    print('top of the critical set (nearest-site distance, 30 digits):')
    for nm, p, (v, k) in pts[:12]:
        print('   %-14s %s   nearest site %d   v - T_LIT = %s' % (nm, nstr(v, 30), k, nstr(v - T_LIT, 8)))
    gmax = pts[0][2][0]
    print()
    print('gamma(witness) = %s' % nstr(gmax, 34))
    print('gamma - lo = %s' % nstr(gmax - lo, 8))
    print('gamma - hi = %s' % nstr(gmax - hi, 8))
    print('gamma - T_LIT = %s' % nstr(gmax - T_LIT, 8))
    print()
    print('=== PART 2: is T_LIT a covering radius of the witness? ===')
    above = [(nm, v) for nm, p, (v, k) in pts if v > T_LIT]
    print('critical points strictly ABOVE T_LIT: %d' % len(above))
    for nm, v in above[:12]:
        print('   %-14s  v = %s  (excess %s)' % (nm, nstr(v, 30), nstr(v - T_LIT, 6)))
    print('=> the 11 disks of radius T_LIT at the saved centres do NOT cover D' if above
          else '=> T_LIT >= all critical values (witness covers at T_LIT)')
    print()
    print('=== PART 3: hub-hub geometry ===')
    d02 = sqrt((C[0][0] - C[2][0]) ** 2 + (C[0][1] - C[2][1]) ** 2)
    R = hi
    print('  |c0| = %s' % nstr(sqrt(C[0][0] ** 2 + C[0][1] ** 2), 20))
    print('  |c2| = %s' % nstr(sqrt(C[2][0] ** 2 + C[2][1] ** 2), 20))
    print('  |c0-c2| = %s' % nstr(d02, 20))
    print('  2R = %s      (R = %s)' % (nstr(2 * R, 20), nstr(R, 20)))
    print('  |c0-c2| - 2R = %s   -> the two hub disks OVERLAP' % nstr(d02 - 2 * R, 8))
    print('  1-2R = %s' % nstr(1 - 2 * R, 20))
    # do the two hub sites share a Voronoi edge?  The shared edge is inside the perpendicular
    # bisector of c0,c2; a point of it must be closer to 0 and 2 than to any other site.
    found = []
    for tp in (mpf('0.02'), mpf('0.05'), mpf('0.1'), mpf('0.2'), mpf('0.3'), mpf('0.5'), mpf('0.7'), mpf('0.9')):
        p = (C[0][0] + tp * (C[2][0] - C[0][0]), C[0][1] + tp * (C[2][1] - C[0][1]))
        ds = sorted([(d(p, k), k) for k in range(n)])
        found.append((float(tp), [k for v, k in ds[:4]], ds[0][1] == 0 or ds[1][1] == 0 or ds[2][1] == 0))
    print('  points on the segment c0-c2, four nearest sites:')
    for tp, near4, has0 in found:
        print('     t=%.2f  nearest4=%s' % (tp, near4))
    # Voronoi edge between hubs: the bisector restricted to the region where 0,2 are nearest
    # sample the bisector line over its intersection with D
    mid = ((C[0][0] + C[2][0]) / 2, (C[0][1] + C[2][1]) / 2)
    dirv = (C[2][1] - C[0][1], -(C[2][0] - C[0][0]))
    nrm = sqrt(dirv[0] ** 2 + dirv[1] ** 2)
    dirv = (dirv[0] / nrm, dirv[1] / nrm)
    good = 0; tot = 0
    for kk in range(-400, 401):
        s = mpf(kk) / 400 * mpf('0.5')
        p = (mid[0] + s * dirv[0], mid[1] + s * dirv[1])
        if p[0] ** 2 + p[1] ** 2 > 1:
            continue
        tot += 1
        ds = sorted([(d(p, k), k) for k in range(n)])
        if ds[0][1] in (0, 2) and ds[1][1] in (0, 2):
            good += 1
    print('  samples on the c0-c2 bisector inside D: %d, of which the two nearest sites are {0,2}: %d'
          % (tot, good))
    print('  => the hub sites %s a Voronoi edge inside D'
          % ('SHARE' if good > 1 else 'do NOT share'))


if __name__ == '__main__':
    main()
