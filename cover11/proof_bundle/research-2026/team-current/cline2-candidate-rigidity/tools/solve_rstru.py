"""High-precision Newton solve of the 18 active tight-point equations -> R_stru.

Variables (23): 22 centre coordinates + R.
Equations (18): nearest-site distance equals R at
   * the 9 tight Voronoi vertices  (7 single-hub + 2 hub-hub -- each counted once), and
   * the 9 boundary perpendicular-bisector points (the "spokes").
A single gauge row (x of ring centre 1) removes the rotation kernel.
Underdetermined system solved by minimal-norm Newton (pseudo-inverse), which converges to
the closest solution of the active system; we then report its radius and compare with the
certified interval and with the covering radius of the rational witness.

Calibration only.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, acos, mpmathify, matrix, lu_solve

mp.dps = 60
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C0 = [(mpmathify(a), mpmathify(b)) for a, b in D['centers_toFixed17']]
Rlo = mpmathify(D['certified_interval']['lo'])
Rhi = mpmathify(D['certified_interval']['hi'])

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
    """Point on bd D equidistant from ci and cj, on the branch between them in angle."""
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
        if abs(t - (ai + aj) / 2) < (aj - ai) / 2 + mpf('1e-9'):
            if ai - mpf('1e-9') <= t <= aj + mpf('1e-9'):
                return (cos(th), sin(th))
    raise RuntimeError('spoke branch not found')


def F(z):
    C = [(z[2 * i], z[2 * i + 1]) for i in range(11)]
    R = z[22]
    rows = [C[1][0] - C0[1][0]]                       # gauge
    for tri in TRIPLES:
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        d2 = min((u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2 for c in C)
        rows.append(d2 - R * R)
    for (i, j) in SPOKES:
        p = spoke_pt(C[i], C[j])
        d2 = min((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2 for c in C)
        rows.append(d2 - R * R)
    return rows


def jac(z, h=mpf('1e-30')):
    m = len(F(z)); n = len(z)
    J = np.zeros((m, n))
    for j in range(n):
        zp = list(z); zm = list(z)
        zp[j] += h; zm[j] -= h
        fp = F(zp); fm = F(zm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    return J


def main():
    z = [v for c in C0 for v in c] + [Rlo]
    print('initial residual: %.3e' % float(max(abs(v) for v in F(z))))
    for it in range(60):
        f = F(z)
        mx = max(abs(v) for v in f)
        if it % 5 == 0 or mx < mpf('1e-40'):
            print('  iter %2d: max|F| = %s   R = %s' % (it, nstr(mx, 6), nstr(z[22], 26)))
        if mx < mpf('1e-45'):
            break
        J = jac(z, mpf('1e-28'))
        df = np.linalg.lstsq(J, -np.array([float(v) for v in f]), rcond=None)[0]
        z = [z[j] + mpf(float(df[j])) for j in range(23)]
    print('\nsolution:')
    print('  R_stru = %s' % nstr(z[22], 40))
    print('  certified lo = %s' % nstr(Rlo, 40))
    print('  certified hi = %s' % nstr(Rhi, 40))
    print('  R - lo = %s' % nstr(z[22] - Rlo, 6))
    print('  final residual = %s' % nstr(max(abs(v) for v in F(z)), 6))
    print('\ncentres (solved) vs saved witness:')
    for i in range(11):
        dx = z[2 * i] - C0[i][0]; dy = z[2 * i + 1] - C0[i][1]
        print('   c%2d  (%+.3e, %+.3e)' % (i, float(dx), float(dy)))
    print('\nper-tight-point residuals (d^2 - R^2):')
    rows = F(z)
    for k, v in enumerate(rows):
        print('   row %2d: %s' % (k, nstr(v, 4)))
    import pickle
    with open(Path(__file__).parent.parent / 'out' / 'z_stru.pkl', 'wb') as fh:
        pickle.dump([str(v) for v in z], fh)


if __name__ == '__main__':
    main()
