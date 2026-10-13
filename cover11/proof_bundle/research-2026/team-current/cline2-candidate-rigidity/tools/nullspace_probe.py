"""Null-space structure and directional-derivative probe for the active system.

Variables (23): 22 centre coordinates + R.
Active rows (18): 9 boundary spokes (3 rows each, rank 1 each -> we keep 1 symmetric row
per spoke) and 9 Voronoi-tight rows.

Question: what is the null space of the active system, and does the covering radius
gamma = max over the whole critical set decrease along any null direction?  A drop means
the saved candidate is not a local optimum of the covering radius; no drop is evidence
(not proof) for local optimality.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, acos, atan2, cos, sin, pi, nstr

mp.dps = 50
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
Cf = [(mpf(int(a)) / mpf(10) ** 17, mpf(int(b)) / mpf(10) ** 17) for a, b in D['centers_scaled_1e17']]
R0 = mpmathify(D['certified_interval']['lo'])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
H0, H2 = 0, 2
ANG0 = {i: atan2(Cf[i][1], Cf[i][0]) % (2 * pi) for i in RINGS}
S0 = {i: sqrt(Cf[i][0] ** 2 + Cf[i][1] ** 2) for i in RINGS}
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]


def cover_radius(cc):
    """max over Voronoi vertices in D and boundary spokes of the nearest-site distance."""
    C = [cc[i] for i in range(11)]
    best = mpf(0); arg = None
    for tri in itertools.combinations(range(11), 3):
        A, B, Cc = C[tri[0]], C[tri[1]], C[tri[2]]
        d1 = B[0] - A[0]; d2 = B[1] - A[1]; e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
        den = d1 * e2 - d2 * e1
        if den == 0:
            continue
        bx = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        by = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        ux = (bx * e2 - by * d2) / den; uy = (d1 * by - e1 * bx) / den
        if ux * ux + uy * uy > 1:
            continue
        d = min(sqrt((ux - c[0]) ** 2 + (uy - c[1]) ** 2) for c in C)
        if d > best:
            best = d; arg = ('vert', tri)
    ang = sorted([(atan2(C[i][1], C[i][0]) % (2 * pi), i) for i in RINGS])
    order = [i for a, i in ang]
    for k in range(9):
        i = order[k]; j = order[(k + 1) % 9]
        A, B = C[i], C[j]
        dx = B[0] - A[0]; dy = B[1] - A[1]
        L2 = dx * dx + dy * dy
        t = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / (2 * L2)
        fx = A[0] + t * dx; fy = A[1] + t * dy
        rem = 1 - (fx * fx + fy * fy)
        if rem <= 0:
            continue
        for sg in (mpf(1), mpf(-1)):
            px = fx + sg * sqrt(rem) * (-dy) / sqrt(L2)
            py = fy + sg * sqrt(rem) * dx / sqrt(L2)
            d = min(sqrt((px - c[0]) ** 2 + (py - c[1]) ** 2) for c in C)
            if d > best:
                best = d; arg = ('spoke', i, j)
    return best, arg


def cons(z):
    cc = {}
    for k, i in enumerate(RINGS):
        cc[i] = (z[2 * i], z[2 * i + 1])
    cc[H0] = (z[2 * H0], z[2 * H0 + 1]); cc[H2] = (z[2 * H2], z[2 * H2 + 1])
    R = z[22]
    rows = []
    ang = sorted([(atan2(cc[i][1], cc[i][0]) % (2 * pi), i) for i in RINGS])
    order = [i for a, i in ang]
    for k in range(9):
        i = order[k]; j = order[(k + 1) % 9]
        si = sqrt(cc[i][0] ** 2 + cc[i][1] ** 2); sj = sqrt(cc[j][0] ** 2 + cc[j][1] ** 2)
        ai = atan2(cc[i][1], cc[i][0]) % (2 * pi); aj = atan2(cc[j][1], cc[j][0]) % (2 * pi)
        if aj < ai:
            aj += 2 * pi
        rows.append(acos((1 + si * si - R * R) / (2 * si)) + acos((1 + sj * sj - R * R) / (2 * sj)) - (aj - ai))
    for tri in TRIPLES:
        A, B, Cc = cc[tri[0]], cc[tri[1]], cc[tri[2]]
        d1 = B[0] - A[0]; d2 = B[1] - A[1]; e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
        den = d1 * e2 - d2 * e1
        bx = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        by = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        ux = (bx * e2 - by * d2) / den; uy = (d1 * by - e1 * bx) / den
        rows.append((ux - A[0]) ** 2 + (uy - A[1]) ** 2 - R * R)
    return rows


def jac(f, z, h):
    n = len(z); m = len(f(z))
    J = np.zeros((m, n))
    for j in range(n):
        zp = list(z); zm = list(z)
        zp[j] += h; zm[j] -= h
        fp = f(zp); fm = f(zm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    return J


def main():
    z0 = []
    for i in range(11):
        z0 += [Cf[i][0], Cf[i][1]]
    z0.append(R0)
    f0 = cons(z0)
    print('constraints m=%d, vars n=%d, max|res|=%.3e' % (len(f0), len(z0), float(max(abs(v) for v in f0))))
    J = jac(cons, z0, mpf('1e-22'))
    u, s, vt = np.linalg.svd(J)
    print('sv:', ['%.3e' % x for x in s])
    rk = int((s > 1e-6 * s[0]).sum())
    nd = len(z0) - rk
    print('rank=%d nullity=%d' % (rk, nd))
    labels = sum([['x%d' % i, 'y%d' % i] for i in range(11)], []) + ['R']
    P = vt[rk:].T
    for k in range(nd):
        nz = [(labels[j], round(P[j, k], 5)) for j in range(len(labels)) if abs(P[j, k]) > 2e-3]
        print('\n null %d (|sv|=%.2e):' % (k, 0.0), nz)
    # hub-only vs ring-only split of the null space
    hubidx = [2 * H0, 2 * H0 + 1, 2 * H2, 2 * H2 + 1, 22]
    ringidx = [j for j in range(22) if j not in [2 * H0, 2 * H0 + 1, 2 * H2, 2 * H2 + 1]]
    print('\nsubspace mass: for each null vector, ||proj on ring|| vs ||proj on hub+ R||')
    for k in range(nd):
        a = np.linalg.norm(P[ringidx, k]); b = np.linalg.norm(P[hubidx, k])
        print('  null %d: ring=%.4f  hubR=%.4f' % (k, a, b))
    # directional probe: step along null directions, project back onto constraints
    print('\ngamma probe (M over the whole critical set) along null directions:')
    g0, arg0 = cover_radius({i: (z0[2 * i], z0[2 * i + 1]) for i in range(11)})
    print('  gamma(z0) = %s (argmax %s)' % (nstr(g0, 22), arg0))
    for k in range(nd):
        for step in (mpf('1e-5'), mpf('1e-4'), mpf('1e-3')):
            z = [mpf(float(z0[j]) + float(step) * P[j, k]) for j in range(len(z0))]
            for it in range(60):
                fz = cons(z)
                if max(abs(v) for v in fz) < mpf('1e-22'):
                    break
                Jz = jac(cons, z, mpf('1e-22'))
                dz = np.linalg.lstsq(Jz, np.array([float(v) for v in fz]), rcond=None)[0]
                z = [z[j] - mpf(float(dz[j])) for j in range(len(z))]
            cc = {i: (z[2 * i], z[2 * i + 1]) for i in range(11)}
            g, arg = cover_radius(cc)
            print('   null %d step %8s : |cons|=%.1e  gamma=%.20f  gamma-gamma0=%+.4e'
                  % (k, nstr(step, 3), float(max(abs(v) for v in cons(z))), float(g), float(g - g0)))
    # central differences for first derivative of gamma along null directions
    print('\ncentral-difference d gamma / d eps along each null direction (eps=1e-5):')
    for k in range(nd):
        vals = []
        for sgn in (1, -1):
            step = mpf(sgn) * mpf('1e-5')
            z = [mpf(float(z0[j]) + float(step) * P[j, k]) for j in range(len(z0))]
            for it in range(60):
                fz = cons(z)
                if max(abs(v) for v in fz) < mpf('1e-22'):
                    break
                Jz = jac(cons, z, mpf('1e-22'))
                dz = np.linalg.lstsq(Jz, np.array([float(v) for v in fz]), rcond=None)[0]
                z = [z[j] - mpf(float(dz[j])) for j in range(len(z))]
            cc = {i: (z[2 * i], z[2 * i + 1]) for i in range(11)}
            g, arg = cover_radius(cc)
            vals.append(float(g))
        print('   null %d: gamma(+)=%.20f gamma(-)=%.20f  slope=%.4e  argmax+/-=...' %
              (k, vals[0], vals[1], (vals[0] - vals[1]) / 2e-5))


if __name__ == '__main__':
    main()

