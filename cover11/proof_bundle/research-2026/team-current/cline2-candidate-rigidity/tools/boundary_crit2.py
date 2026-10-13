"""Correct boundary critical points of the nearest-site map on bd D.

For site pair (i,j) the perpendicular bisector is the line
    p . (c_i - c_j) = (|c_i|^2 - |c_j|^2)/2.
Writing p = (cos th, sin th) this is  A cos th + B sin th = C  with
    A = c_i.x - c_j.x,  B = c_i.y - c_j.y,  C = (|c_i|^2 - |c_j|^2)/2,
so th = atan2(B,A) +- acos(C/sqrt(A^2+B^2))  (valid iff |C| <= sqrt(A^2+B^2)).
The boundary Voronoi vertices are those solutions where i and j are the two nearest sites;
the nearest-site distance there is the boundary covering-radius value.  Calibration only.
"""
import json, io, math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C = [(int(a) / 1e17, int(b) / 1e17) for a, b in D['centers_scaled_1e17']]
R = float(D['certified_interval']['lo'])
n = 11


def dist(p, i):
    return math.hypot(p[0] - C[i][0], p[1] - C[i][1])


def main():
    rows = []
    for i in range(n):
        for j in range(i + 1, n):
            A = C[i][0] - C[j][0]
            B = C[i][1] - C[j][1]
            Cc = ((C[i][0] ** 2 + C[i][1] ** 2) - (C[j][0] ** 2 + C[j][1] ** 2)) / 2
            L = math.hypot(A, B)
            if L == 0 or abs(Cc) > L:
                continue
            base = math.atan2(B, A)
            off = math.acos(Cc / L)
            for th in (base + off, base - off):
                p = (math.cos(th), math.sin(th))
                ds = sorted(((dist(p, k), k) for k in range(n)))
                rows.append((ds[0][0], (i, j), p, ds[:3], th))
    rows.sort(reverse=True)
    print('boundary Voronoi vertices on bd D, sorted by nearest-site distance:')
    tight = []
    for v, pair, p, ds, th in rows:
        if v < R - 2e-3:
            continue
        two = sorted([pair[0], pair[1]]) == sorted([ds[0][1], ds[1][1]])
        tag = 'TIGHT ' if abs(v - R) < 1e-15 else '      '
        print('  %s%.17f  pair=%s  th=%9.5f deg  two-nearest=%s  d=%s'
              % (tag, v, pair, math.degrees(th % (2 * math.pi)), two, ['%.12f' % x for x, k in ds]))
        if abs(v - R) < 1e-15 and two:
            tight.append((pair, p, v))
    print('\ntight boundary points: %d' % len(tight))
    print('pairs (in cyclic order):', [t[0] for t in tight])
    print('\nboundary cyclic order of sites at the tight points:')
    order = sorted(tight, key=lambda t: math.atan2(t[1][1], t[1][0]) % (2 * math.pi))
    for pair, p, v in order:
        print('   th=%9.5f pair=%s' % (math.degrees(math.atan2(p[1], p[0]) % (2 * math.pi)), pair))
    print('\nmax over bd D of the nearest-site distance = %.17f' % max(x[0] for x in rows))
    print('R                                            = %.17f' % R)


if __name__ == '__main__':
    main()
