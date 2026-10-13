"""Active-set reconstruction, mpmath 60 dps, calibration only.

Units: center coordinates are the exact integers of n11/upper/certified_object.json
divided by 10^17, so the unit disk has radius 1 and the scaled coordinates are exact.
R is taken as the certified interval lower endpoint (60 decimals).

Outputs (all calibration, no certificate): the 9 tight boundary spokes, the tight
Voronoi vertices with their exact generating triples, and the residual against R.
"""
import json, io, math
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, acos, atan2, cos, sin, pi, nstr

mp.dps = 60
ROOT = Path(__file__).resolve().parents[4]
OBJ = ROOT / 'n11' / 'upper' / 'certified_object.json'


def load():
    d = json.load(io.open(OBJ, encoding='utf-8-sig'))
    S = mpf(10) ** 17
    C = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in d['centers_scaled_1e17']]
    lo = mpmathify(d['certified_interval']['lo'])
    hi = mpmathify(d['certified_interval']['hi'])
    return d, C, lo, hi


def dist(p, c):
    return sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2)


def circum(P, Q, W):
    ax, ay = P
    bx, by = Q
    cx, cy = W
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if d == 0:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def spoke_point(C, i, j, R):
    """Point on bd D at distance exactly R from both c_i and c_j (the 2-circle map to bd D)."""
    ci, cj = C[i], C[j]
    ax = 2 * (ci[0] - cj[0])
    ay = 2 * (ci[1] - cj[1])
    b = (ci[0] ** 2 + ci[1] ** 2) - (cj[0] ** 2 + cj[1] ** 2)
    nrm2 = ax * ax + ay * ay
    t = b / nrm2
    fx, fy = ax * t, ay * t
    L2 = 1 - (fx * fx + fy * fy)
    if L2 <= 0:
        return None
    s = sqrt(L2) / sqrt(nrm2)
    out = []
    for sg in (mpf(1), mpf(-1)):
        out.append((fx - sg * s * ay, fy + sg * s * ax))
    return out


def main():
    d, C, Rlo, Rhi = load()
    n = len(C)
    print('certified interval: [%s, %s]' % (nstr(Rlo, 62), nstr(Rhi, 62)))
    R = Rlo
    rings = [i for i in range(n) if sqrt(C[i][0] ** 2 + C[i][1] ** 2) > 1 - R]
    hubs = [i for i in range(n) if i not in rings]
    print('ring sites =', rings, ' hubs =', hubs)
    ang = sorted([(atan2(C[i][1], C[i][0]) % (2 * pi), i) for i in rings])
    order = [i for a, i in ang]
    print('angular order =', order)

    print('\n--- (a) 9 boundary spokes: point on bd D equidistant R from both neighbours ---')
    for k in range(9):
        i = order[k]
        j = order[(k + 1) % 9]
        ps = spoke_point(C, i, j, R)
        ai = ang[k][0]
        aj = ang[(k + 1) % 9][0]
        if aj < ai:
            aj += 2 * pi
        best = None
        for p in ps:
            th = atan2(p[1], p[0]) % (2 * pi)
            if th < ai:
                th += 2 * pi
            if ai <= th <= aj:
                best = p
        if best is None:
            continue
        ds = sorted([(dist(best, C[t]), t) for t in range(n)])
        print('  spoke(%2d,%2d): |p|=1-%s   d_i-R=%s   d_j-R=%s   third=%d (d-R=%s)'
              % (i, j, nstr(1 - sqrt(best[0] ** 2 + best[1] ** 2), 5),
                 nstr(ds[0][0] - R, 5), nstr(ds[1][0] - R, 5),
                 ds[2][1], nstr(ds[2][0] - R, 5)))

    print('\n--- (b) Voronoi vertices with nearest-site radius within 5e-3 of R ---')
    import itertools
    rows = []
    seen = set()
    for tri in itertools.combinations(range(n), 3):
        v = circum(C[tri[0]], C[tri[1]], C[tri[2]])
        if v is None:
            continue
        if v[0] ** 2 + v[1] ** 2 > 1:
            continue
        ds = sorted([(dist(v, C[t]), t) for t in range(n)])
        key = (nstr(v[0], 12), nstr(v[1], 12))
        if key in seen:
            continue
        seen.add(key)
        rows.append((ds[0][0], v, tri, ds))
    rows.sort(reverse=True)
    tight = []
    for rv, v, tri, ds in rows:
        if rv > R - mpf('5e-3'):
            tight.append((rv, v, tri, ds))
            print('  Rv=%s  v=(%s,%s)  gen=%s  nearest=%s'
                  % (nstr(rv, 22), nstr(v[0], 20), nstr(v[1], 20), tri,
                     [(t, nstr(x, 6)) for x, t in ds[:4]]))
    print('\n  tight vertices count (Rv > R - 5e-3): %d' % len(tight))
    print('  Rv - R for those: ', [nstr(rv - R, 6) for rv, v, tri, ds in tight])
    return dict(order=order, tight=tight)


if __name__ == '__main__':
    main()
