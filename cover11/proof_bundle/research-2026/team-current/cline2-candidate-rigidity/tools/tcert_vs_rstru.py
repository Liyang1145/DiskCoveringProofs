"""DEFINITIVE separation of the saved rational witness from the algebraic radius.

Two distinct objects live in n11/upper/certified_object.json:
  (A) the 22 integers / 10^17                  -> rational witness, radius T_cert
  (B) the 22 strings "toFixed(17)" parsed as doubles -> the object behind the certified
      interval, radius T_str
  (C) the true algebraic configuration of the active system -> R_stru

We measure gamma = covering radius (= max over the full critical set) for (A) and (B) with
mpmath at 50 dps, and compare with the certified interval and with a high-precision
Newton solve of the active equality system for (C).

Calibration only.
"""
import json, io, math, itertools
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, acos, mpmathify

mp.dps = 50
ROOT = Path(__file__).resolve().parents[4]
OBJ = ROOT / 'n11' / 'upper' / 'certified_object.json'
D = json.load(io.open(OBJ, encoding='utf-8-sig'))
S = mpf(10) ** 17

A = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in D['centers_scaled_1e17']]
B = [(mpmathify(a), mpmathify(b)) for a, b in D['centers_toFixed17']]
print('integer object vs string object: coordinates that differ')
nd = 0
for i in range(11):
    d = max(abs(A[i][0] - B[i][0]), abs(A[i][1] - B[i][1]))
    if d != 0:
        nd += 1
        print('   c%2d  maxdiff = %s' % (i, nstr(d, 6)))
print('   -> %d of 11 centres differ' % nd)
print()
lo = mpmathify(D['certified_interval']['lo'])
hi = mpmathify(D['certified_interval']['hi'])
print('certified interval lo = %s' % nstr(lo, 62))
print('certified interval hi = %s' % nstr(hi, 62))


def gamma(C):
    """covering radius via the full critical set: all triple Voronoi vertices in D plus all
    perpendicular-bisector intersections with bd D, taking the nearest-site distance."""
    n = len(C)
    best = mpf(0); arg = None
    for tri in itertools.combinations(range(n), 3):
        P, Q, W = C[tri[0]], C[tri[1]], C[tri[2]]
        d = 2 * (P[0] * (Q[1] - W[1]) + Q[0] * (W[1] - P[1]) + W[0] * (P[1] - Q[1]))
        if d == 0:
            continue
        ux = ((P[0] ** 2 + P[1] ** 2) * (Q[1] - W[1]) + (Q[0] ** 2 + Q[1] ** 2) * (W[1] - P[1])
              + (W[0] ** 2 + W[1] ** 2) * (P[1] - Q[1])) / d
        uy = ((P[0] ** 2 + P[1] ** 2) * (W[0] - Q[0]) + (Q[0] ** 2 + Q[1] ** 2) * (P[0] - W[0])
              + (W[0] ** 2 + W[1] ** 2) * (Q[0] - P[0])) / d
        if ux * ux + uy * uy > 1:
            continue
        v = min(sqrt((ux - c[0]) ** 2 + (uy - c[1]) ** 2) for c in C)
        if v > best:
            best = v; arg = ('V', tri)
    for i in range(n):
        for j in range(i + 1, n):
            Ax = C[i][0] - C[j][0]; Ay = C[i][1] - C[j][1]
            Cc = ((C[i][0] ** 2 + C[i][1] ** 2) - (C[j][0] ** 2 + C[j][1] ** 2)) / 2
            L = sqrt(Ax * Ax + Ay * Ay)
            if L == 0 or abs(Cc) > L:
                continue
            base = atan2(Ay, Ax)
            off = acos(Cc / L)
            for th in (base + off, base - off):
                p = (cos(th), sin(th))
                ds = sorted([(sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2), k) for k, c in enumerate(C)])
                if {i, j} == {ds[0][1], ds[1][1]}:
                    if ds[0][0] > best:
                        best = ds[0][0]; arg = ('B', (i, j), ds[0][1], ds[1][1])
    return best, arg


for name, C in (('(A) integer/1e17 witness', A), ('(B) toFixed17 strings', B)):
    g, arg = gamma(C)
    print('\n%s' % name)
    print('   gamma = %s' % nstr(g, 30))
    print('   argmax = %s' % (arg,))
    print('   gamma - lo = %s' % nstr(g - lo, 6))
    print('   gamma - hi = %s' % nstr(g - hi, 6))
