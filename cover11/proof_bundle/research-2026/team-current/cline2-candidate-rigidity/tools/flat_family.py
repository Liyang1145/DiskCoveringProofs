"""Is the active tight-point system isolating?  Calibration / diagnostic only.

Parameterisation (14 dof): 9 ring polar angles t_k, 9 ring radii s_k, hub-1 (u1,v1),
hub-2 (u2,v2), and R.  18 constraints:
   * 9 spoke equalities    w_i + w_j = t_j - t_i        (boundary arc capacity saturated)
   * 9 Voronoi-tight equalities  r_v(triple) = R        (one row per tight vertex)
Then we probe the null space: step along each null direction and re-solve the constraints
by Newton, and watch the covering radius  gamma = max over ALL critical points of the new
configuration.  If gamma drops along some direction, the active system does not isolate a
local minimum (i.e. the candidate would not be locally optimal even within the family).
"""
import json, io, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, mpmathify, sqrt, acos, atan2, cos, sin, pi, nstr

mp.dps = 50
ROOT = Path(__file__).resolve().parents[4]
OBJ = ROOT / 'n11' / 'upper' / 'certified_object.json'
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]
SPOKES = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
H0, H2 = 0, 2


def load():
    d = json.load(io.open(OBJ, encoding='utf-8-sig'))
    S = mpf(10) ** 17
    C = [(mpf(int(a)) / S, mpf(int(b)) / S) for a, b in d['centers_scaled_1e17']]
    return d, C


D, C0 = load()
R0 = mpmathify(D['certified_interval']['lo'])
ANG0 = {i: (atan2(C0[i][1], C0[i][0]) % (2 * pi)) for i in RINGS}
S0 = {i: sqrt(C0[i][0] ** 2 + C0[i][1] ** 2) for i in RINGS}


def pack(z):
    t = z[0:9]; s = z[9:18]
    u1, v1, u2, v2, R = z[18], z[19], z[20], z[21], z[22]
    cc = {}
    for k, i in enumerate(RINGS):
        cc[i] = (s[k] * cos(t[k]), s[k] * sin(t[k]))
    cc[H0] = (u1, v1); cc[H2] = (u2, v2)
    return cc, R


def cons(z):
    cc, R = pack(z)
    out = []
    for (i, j) in SPOKES:
        si = sqrt(cc[i][0] ** 2 + cc[i][1] ** 2); sj = sqrt(cc[j][0] ** 2 + cc[j][1] ** 2)
        ai = atan2(cc[i][1], cc[i][0]) % (2 * pi); aj = atan2(cc[j][1], cc[j][0]) % (2 * pi)
        if aj < ai:
            aj += 2 * pi
        wi = acos((1 + si * si - R * R) / (2 * si))
        wj = acos((1 + sj * sj - R * R) / (2 * sj))
        out.append(wi + wj - (aj - ai))
    for tri in TRIPLES:
        A, B, Cc = cc[tri[0]], cc[tri[1]], cc[tri[2]]
        rows = []
        for (P, Q) in ((A, B), (A, Cc), (B, Cc)):
            rows.append(((P[0] - Q[0]) ** 2 + (P[1] - Q[1]) ** 2) ** 0)  # noop
        # circumcentre
        d1 = B[0] - A[0]; d2 = B[1] - A[1]; e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
        bx = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        by = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        ux = (bx * e2 - by * d2) / (d1 * e2 - d2 * e1)
        uy = (d1 * by - e1 * bx) / (d1 * e2 - d2 * e1)
        out.append((ux - A[0]) ** 2 + (uy - A[1]) ** 2 - R * R)
    return out


def num_jac(f, z, h):
    n = len(z); m = len(f(z))
    J = np.zeros((m, n))
    for j in range(n):
        zp = list(z); zm = list(z)
        zp[j] += h; zm[j] -= h
        fp = f(zp); fm = f(zm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    return J


def z_full(z5, zbase, P):
    # P: 14x5 orthonormal basis (null space of the constraint jacobian)
    return list(zbase + P @ z5)


def test():
    z0 = [ANG0[i] for i in RINGS] + [S0[i] for i in RINGS] + \
         [C0[H0][0], C0[H0][1], C0[H2][0], C0[H2][1], R0]
    z0 = [mpf(x) for x in z0]
    f0 = cons(z0)
    print('m=%d n=%d  max|res|=%s' % (len(f0), len(z0), nstr(max(abs(v) for v in f0), 6)))
    h = mpf('1e-20')
    J = num_jac(cons, z0, h)
    u, s, vt = np.linalg.svd(J)
    print('sv:', ['%.3e' % x for x in s])
    rk = int((s > 1e-6 * s[0]).sum())
    print('rank=%d nullity=%d' % (rk, len(z0) - rk))
    P = vt[rk:].T                      # n x nullity
    print('null space dim', P.shape[1])
    labels = ['t(%d)' % i for i in RINGS] + ['s(%d)' % i for i in RINGS] + ['u1', 'v1', 'u2', 'v2', 'R']
    for k in range(P.shape[1]):
        print(' null %d:' % k, {lab: round(P[j, k], 6) for j, lab in enumerate(labels) if abs(P[j, k]) > 1e-3})

    # Now step along each null direction, re-solve constraints by Newton on the 18-dim
    # constraint map restricted to the 5-dim null coordinate (underdetermined -> use the
    # pseudo-inverse flow that follows the family).
    for k in range(P.shape[1]):
        for step in (1e-4, 1e-3, 1e-2):
            z = np.array([float(x) for x in z0]) + step * P[:, k]
            z = z.tolist()
            for it in range(40):
                fz = np.array([float(v) for v in cons([mpf(x) for x in z])])
                if max(abs(fz)) < 1e-14:
                    break
                Jz = num_jac(cons, [mpf(x) for x in z], mpf('1e-24'))
                dz = -np.linalg.lstsq(Jz, fz, rcond=None)[0]
                z = (np.array(z) + dz).tolist()
            cc, R = pack([mpf(x) for x in z])
            # covering radius of the new configuration: max over all Voronoi vertices and spokes
            gam = cover_radius(cc)
            print(' null %d step %8.1e : |cons|=%8.1e  gamma=%.17f  R=%.17f  gamma-R=%+.3e'
                  % (k, step, max(abs(float(v)) for v in cons([mpf(x) for x in z])),
                     float(gam), float(R), float(gam - R)))


def cover_radius(cc):
    """max over (i) all triple-Voronoi vertices inside D, (ii) all boundary pairs, of the
    nearest-site distance."""
    C = [cc[i] for i in range(11)]
    best = mpf(0)
    for tri in itertools.combinations(range(11), 3):
        A, B, Cc = C[tri[0]], C[tri[1]], C[tri[2]]
        d1 = B[0] - A[0]; d2 = B[1] - A[1]; e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
        den = d1 * e2 - d2 * e1
        if den == 0:
            continue
        bx = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        by = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        ux = (bx * e2 - by * d2) / den
        uy = (d1 * by - e1 * bx) / den
        if ux * ux + uy * uy > 1:
            continue
        d = min(sqrt((ux - c[0]) ** 2 + (uy - c[1]) ** 2) for c in C)
        if d > best:
            best = d
    for (i, j) in itertools.combinations(range(11), 2):
        A, B = C[i], C[j]
        dx = B[0] - A[0]; dy = B[1] - A[1]
        L = sqrt(dx * dx + dy * dy)
        if L == 0:
            continue
        mx = (A[0] + B[0]) / 2; my = (A[1] + B[1]) / 2
        hh = sqrt(max(mpf(0), 1 - (mx * mx + my * my)))
        # both unit-circle intersection directions
        for sg in (mpf(1), mpf(-1)):
            nx = -dy / L * sg; ny = dx / L * sg
            px = mx + hh * nx; py = my + hh * ny
            d = min(sqrt((px - c[0]) ** 2 + (py - c[1]) ** 2) for c in C)
            if d > best:
                best = d
    return best


if __name__ == '__main__':
    test()
