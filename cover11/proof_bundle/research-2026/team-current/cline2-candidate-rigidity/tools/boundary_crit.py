"""Correct boundary critical points: perpendicular-bisector intersections with bd D.

For sites c_i != c_j the perpendicular bisector line is
    p . (c_i - c_j) = (|c_i|^2 - |c_j|^2)/2
and its intersections with bd D are the points where both are equally near on the boundary.
A boundary critical point of the nearest-site map is such an intersection at which i and j
are the two nearest sites; the local maximum of the covering radius over bd D is at one of
these (or at the antipode of a bisector that misses the disk).

This script lists all of them with slack, flags the tight ones (== R) and identifies the
spoke structure, then re-derives gamma.
"""
import json, io, math
import numpy as np
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C = [(int(a) / 1e17, int(b) / 1e17) for a, b in D['centers_scaled_1e17']]
R = float(D['certified_interval']['lo'])
n = 11


def d(p, i):
    return math.hypot(p[0] - C[i][0], p[1] - C[i][1])


def main():
    rows = []
    for i in range(n):
        for j in range(i + 1, n):
            A, B = C[i], C[j]
            dx = B[0] - A[0]; dy = B[1] - A[1]
            L2 = dx * dx + dy * dy
            # m . d = (|A|^2 - |B|^2)/2 with d = B - A
            t = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / (2 * L2)
            fx = A[0] + t * dx; fy = A[1] + t * dy
            rem = 1 - (fx * fx + fy * fy)
            if rem <= 0:
                continue
            for sg in (1.0, -1.0):
                px = fx + sg * math.sqrt(rem) * (-dy) / math.sqrt(L2)
                py = fy + sg * math.sqrt(rem) * dx / math.sqrt(L2)
                ds = sorted(((d((px, py), k), k) for k in range(n)))
                if ds[1][1] not in (i, j):
                    pass
                rows.append((ds[0][0], (i, j), (px, py), ds[:3]))
    rows.sort(reverse=True)
    print('boundary perpendicular-bisector intersections inside D, sorted by nearest-site distance')
    print('(only those where the two generating sites are the two nearest are true critical pts)')
    seen = set()
    tight = []
    for v, pair, p, ds in rows:
        key = (round(p[0], 12), round(p[1], 12))
        if key in seen:
            continue
        seen.add(key)
        two_nearest = {pair[0], pair[1]} == {ds[0][1], ds[1][1]}
        flag = 'TIGHT' if abs(v - R) < 1e-14 else ''
        if two_nearest and abs(v - R) < 1e-14:
            tight.append((pair, p, v))
        if v > R - 3e-3:
            print('  %.17f %s  pair=%s  p=(%+.15f,%+.15f)  two-nearest=%s  d=%s'
                  % (v, flag, pair, p[0], p[1], two_nearest, ['%.9f' % x for x, k in ds]))
    print('\nnumber of tight boundary critical points: %d' % len(tight))
    print('pairs:', [t[0] for t in tight])
    print('\ngamma over bd D (max over these + antipodal scan):')
    best = max(x[0] for x in rows)
    print('   max over bisector intersections = %.17f' % best)
    mx = 0; arg = None
    for k in range(200000):
        th = 2 * math.pi * k / 200000
        p = (math.cos(th), math.sin(th))
        v = min(d(p, i) for i in range(n))
        if v > mx:
            mx = v; arg = math.degrees(th)
    print('   dense scan (200k) max = %.17f at %.4f deg' % (mx, arg))
    print('   R = %.17f' % R)


if __name__ == '__main__':
    main()
