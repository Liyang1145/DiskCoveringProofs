"""High-precision (60 dps) minimal-norm Newton solve of the active tight-point system.

Fixes the earlier double-precision bottleneck: the Jacobian, the least-squares pseudo-inverse
(via mpmath QR with column pivoting on the *transpose*) and the correction are all carried in
60-digit arithmetic.  Also gives an honest look at which rows stall (row 13/14 = the two
hub-hub triples) and at the higher-precision value of the radius of the solution reached.
"""
import json, io, math, itertools, pickle
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr, cos, sin, acos, mpmathify, matrix

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
    raise RuntimeError('spoke branch')


def F(z):
    C = [(z[2 * i], z[2 * i + 1]) for i in range(11)]
    R = z[22]
    rows = []
    for tri in TRIPLES:
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        rows.append(min((u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2 for c in C) - R * R)
    for (i, j) in SPOKES:
        p = spoke_pt(C[i], C[j])
        rows.append(min((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2 for c in C) - R * R)
    rows.append(C[1][0] - C0[1][0])            # gauge row 19
    return rows


def mpjac(z, h):
    m = len(F(z)); n = len(z)
    J = matrix(m, n)
    for j in range(n):
        zp = list(z); zm = list(z)
        zp[j] += h; zm[j] -= h
        fp = F(zp); fm = F(zm)
        for i in range(m):
            J[i, j] = (fp[i] - fm[i]) / (2 * h)
    return J


def pinv_solve(J, f):
    """minimal-norm solution of J d = -f  via the normal equations (J J^T) y = -f , d = J^T y."""
    m, n = J.rows, J.cols
    G = J * J.T
    b = matrix([-v for v in f], m, 1)
    y = mp.lu_solve(G, b)
    d = J.T * y
    return d


def main():
    z = [v for c in C0 for v in c] + [Rlo]
    print('m=%d n=%d' % (len(F(z)), len(z)))
    print('initial max|F| = %.3e' % float(max(abs(v) for v in F(z))))
    for it in range(40):
        f = F(z)
        mx = max(abs(v) for v in f)
        if it % 2 == 0:
            print('  it %2d: max|F| = %s  R = %s' % (it, nstr(mx, 6), nstr(z[22], 30)))
        if mx < mpf('1e-52'):
            break
        J = mpjac(z, mpf('1e-40'))
        d = pinv_solve(J, f)
        z = [z[j] + d[j] for j in range(23)]
    f = F(z)
    print('\nfinal max|F| = %s' % nstr(max(abs(v) for v in f), 6))
    for k, v in enumerate(f):
        print('   row %2d : %s' % (k, nstr(v, 4)))
    print('\nR (from the converged point) = %s' % nstr(z[22], 45))
    print('certified lo                 = %s' % nstr(Rlo, 45))
    print('certified hi                 = %s' % nstr(Rhi, 45))
    print('R - lo = %s' % nstr(z[22] - Rlo, 8))
    print('R - hi = %s' % nstr(z[22] - Rhi, 8))
    print('\ndisplacement from the witness (per centre):')
    for i in range(11):
        print('   c%2d (%+.4e, %+.4e)' % (i, float(z[2 * i] - C0[i][0]), float(z[2 * i + 1] - C0[i][1])))
    with open(Path(__file__).parent.parent / 'out' / 'z_stru_mp.pkl', 'wb') as fh:
        pickle.dump([mp.nstr(v, 45) for v in z], fh)
    return z


if __name__ == '__main__':
    main()
