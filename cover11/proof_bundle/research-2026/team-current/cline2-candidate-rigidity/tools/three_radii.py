"""Three radii compared at 60 dps:
   T_cert = covering radius of the saved RATIONAL witness (22 integers / 10^17)
   [lo,hi] = the certified interval published for that witness
   R_stru  = the true algebraic radius of the active local optimum (bracketed by [lo,hi])

Also measures HOW the witness fails the exact active equalities (residuals per row), which is
the quantitative statement of "rounded witness vs true algebraic solution".
"""
import json, io, math, itertools
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, acos, mpmathify

mp.dps = 60
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
S = mpf(10) ** 17
A = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in D['centers_scaled_1e17']]
lo = mpmathify(D['certified_interval']['lo']); hi = mpmathify(D['certified_interval']['hi'])
print('saved witness centres (exact 17-decimal strings):')
for i, (a, b) in enumerate(D['centers_toFixed17']):
    print('   c%2d %s  %s' % (i, a, b))
print()
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]
SPOKES = [(5, 7), (7, 1), (1, 8), (6, 8), (4, 6), (4, 9), (9, 10), (3, 10), (3, 5)]


def circ(P, Q, W):
    ax, ay = P; bx, by = Q; cx, cy = W
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def spoke_pt(ci, cj):
    ai = atan2(ci[1], ci[0]) % (2 * pi); aj = atan2(cj[1], cj[0]) % (2 * pi)
    if aj < ai:
        aj += 2 * pi
    Ax = ci[0] - cj[0]; Ay = ci[1] - cj[1]
    Cc = ((ci[0] ** 2 + ci[1] ** 2) - (cj[0] ** 2 + cj[1] ** 2)) / 2
    L = sqrt(Ax * Ax + Ay * Ay)
    base = atan2(Ay, Ax); off = acos(Cc / L)
    for th in (base + off, base - off):
        t = th % (2 * pi)
        if t < ai:
            t += 2 * pi
        if ai - mpf('1e-12') <= t <= aj + mpf('1e-12'):
            return (cos(th), sin(th))
    raise RuntimeError


def main():
    C = A
    print('%-22s %-28s %-28s' % ('tight point', 'nearest-site distance', 'vs published lo'))
    vals = []
    for tri in TRIPLES:
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        ds = sorted([(sqrt((u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2), k) for k, c in enumerate(C)])
        vals.append(('V%s' % (tri,), ds[0][0], ds[0][1]))
    for (i, j) in SPOKES:
        p = spoke_pt(C[i], C[j])
        ds = sorted([(sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2), k) for k, c in enumerate(C)])
        vals.append(('S(%d,%d)' % (i, j), ds[0][0], ds[0][1]))
    T = max(v for _, v, _ in vals)
    for nm, v, k in vals:
        print('%-22s %-28s %+.6e   (nearest site %d)' % (nm, nstr(v, 24), float(v - lo), k))
    print()
    print('T_cert = covering radius of the rational witness = %s' % nstr(T, 30))
    print('published certified interval lo = %s' % nstr(lo, 30))
    print('T_cert - lo = %s' % nstr(T - lo, 8))
    print('T_cert - hi = %s' % nstr(T - hi, 8))
    print()
    print('max over the 18 active rows of (value - T_cert):')
    print('   (identically 0 by construction; see the max above)')
    print()
    # spread of the 18 active values at the witness
    vs = sorted(v for _, v, _ in vals)
    print('spread of the 18 active tight-point values: max-min = %s' % nstr(vs[-1] - vs[0], 8))
    print('   min = %s' % nstr(vs[0], 24))
    print('   max = %s' % nstr(vs[-1], 24))


if __name__ == '__main__':
    main()
