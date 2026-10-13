"""FINAL active-set determination for the saved n11 upper witness.

Boundary critical points of the nearest-site map on bd D come from the perpendicular
bisector of a site pair.  With d = |c_j - c_i|^2 and  C = (|c_i|^2 - |c_j|^2)/2 the bisector
reads  p . (c_j - c_i) = C, so with unit u = (c_j-c_i)/d the foot is at distance C/sqrt(d)
from the origin.  The two boundary intersections are
    p = m +- s * n ,  m = c_i + (C/d)(c_j - c_i) ,  n = perpendicular unit,
    s = sqrt(1 - |m|^2)   (exists iff |C| <= sqrt(d), i.e. the line meets the unit disk).
We report every branch, the nearest sites, and whether the pair really is the two nearest.
"""
import json, io, math
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, mpmathify

mp.dps = 40
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
S = mpf(10) ** 17
C = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in D['centers_scaled_1e17']]
n = 11
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]


def main():
    rows = []
    for i in range(n):
        for j in range(i + 1, n):
            dx = C[j][0] - C[i][0]; dy = C[j][1] - C[i][1]
            dd = dx * dx + dy * dy
            if dd == 0:
                continue
            Cc = ((C[i][0] ** 2 + C[i][1] ** 2) - (C[j][0] ** 2 + C[j][1] ** 2)) / 2
            t = Cc / dd
            mx = C[i][0] + t * dx; my = C[i][1] + t * dy
            rem = 1 - (mx * mx + my * my)
            if rem < 0:
                continue
            s = sqrt(rem)
            L = sqrt(dd)
            for sg in (mpf(1), mpf(-1)):
                px = mx + sg * s * (-dy) / L
                py = my + sg * s * dx / L
                ds = sorted([(sqrt((px - c[0]) ** 2 + (py - c[1]) ** 2), k) for k, c in enumerate(C)])
                rows.append((ds[0][0], (i, j), (px, py), ds[:3]))
    rows.sort(reverse=True)
    print('boundary bisector points on bd D (|p|=1), sorted:')
    tight = []
    for v, pair, p, ds in rows:
        if v < 0.37:
            continue
        two = sorted([pair[0], pair[1]]) == sorted([ds[0][1], ds[1][1]])
        print('   %.24f  pair=%s  p=(%+.15f,%+.15f)  two-nearest=%s  d=%s'
              % (float(v), pair, float(p[0]), float(p[1]), two, ['%.12f' % float(x) for x, k in ds]))
        if two and v > mpf('0.379983853119838'):
            tight.append((pair, p, v))
    print('\ntight boundary points: %d -> %s' % (len(tight), [t[0] for t in tight]))
    # control: x-coordinate of a centre is a valid bisector of that centre - ??? no; use the
    # classic identity |u-c|^2 = |u|^2 - 2 u.c + |c|^2, so |u-c| = |u| iff u.c = |c|^2/2.
    print('\nCONTROL (identity check) for pair (7,1): point p on bd D equidistant from c7 and c1')
    p, pair, v = [(p, pr, v) for pr, p, v in tight if pr == (7, 1)][0] if any(pr == (7, 1) for pr, p, v in tight) else (None, None, None)
    if p is not None:
        for k in (7, 1):
            u = (p[0] - C[k][0], p[1] - C[k][1])
            print('      |p-c%d| = %s' % (k, nstr(sqrt(u[0] ** 2 + u[1] ** 2), 24)))
        print('      p.(c7) = %s   |c7|^2/2 = %s' % (nstr(p[0] * C[7][0] + p[1] * C[7][1], 20),
              nstr((C[7][0] ** 2 + C[7][1] ** 2) / 2, 20)))


if __name__ == '__main__':
    main()
