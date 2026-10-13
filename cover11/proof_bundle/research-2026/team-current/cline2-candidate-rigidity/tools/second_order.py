"""Second-order behaviour of the covering radius along the active constraint family.

Family: solutions of the 18 active tight-point equations (R held at the certified value,
rotation gauge removed by pinning the first ring centre's x).  We take finite steps along
the null directions of the constraint Jacobian, project back with Newton steps restricted
to the null space (so the step stays on the intended branch), and record

        gamma(x)  = covering radius = max over the FULL critical set,

Then fit a parabola in the step to get d2 gamma / d eps^2 and test whether any null
direction decreases gamma (=> the candidate is not a local optimum of the covering radius)
or all increase it (evidence for local optimality).

Calibration only: no certificate, no global claim.
"""
import json, io, itertools
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, sqrt, atan2, pi, nstr

mp.dps = 40
ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
Cf = [(mpf(int(a)) / mpf(10) ** 17, mpf(int(b)) / mpf(10) ** 17) for a, b in D['centers_scaled_1e17']]
R0 = mpf(float(D['certified_interval']['lo']))
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
SPOKES = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]
X0 = [v for i in range(11) for v in Cf[i]]


def circ(P, Q, W):
    ax, ay = P; bx, by = Q; cx, cy = W
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def spoke_pt(ci, cj, R):
    ax = 2 * (ci[0] - cj[0]); ay = 2 * (ci[1] - cj[1])
    b = (ci[0] ** 2 + ci[1] ** 2) - (cj[0] ** 2 + cj[1] ** 2)
    n2 = ax * ax + ay * ay
    t = b / n2
    fx, fy = ax * t, ay * t
    L2 = 1 - (fx * fx + fy * fy)
    if L2 <= 0:
        return None
    s = sqrt(L2) / sqrt(n2)
    for sg in (mpf(1), mpf(-1)):
        p = (fx - sg * s * ay, fy + sg * s * ax)
        th = atan2(p[1], p[0]) % (2 * pi)
        lo = atan2(ci[1], ci[0]) % (2 * pi); hi = atan2(cj[1], cj[0]) % (2 * pi)
        if hi < lo:
            hi += 2 * pi
        if th < lo:
            th += 2 * pi
        if lo - mpf('1e-9') <= th <= hi + mpf('1e-9'):
            return p
    return None


def cons(x):
    C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
    rows = []
    # gauge: pin x of centre 1 (a ring centre) to remove rotation
    rows.append(C[1][0] - Cf[1][0])
    for (i, j) in SPOKES:
        p = spoke_pt(C[i], C[j], R0)
        if p is None:
            raise RuntimeError('spoke')
        rows.append((p[0] - C[i][0]) ** 2 + (p[1] - C[i][1]) ** 2 - R0 * R0)
    for tri in TRIPLES:
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        rows.append((u[0] - C[tri[0]][0]) ** 2 + (u[1] - C[tri[0]][1]) ** 2 - R0 * R0)
    return rows


def jac(f, x, h):
    n = len(x); m = len(f(x))
    J = np.zeros((m, n))
    for j in range(n):
        xp = list(x); xm = list(x)
        xp[j] += h; xm[j] -= h
        fp = f(xp); fm = f(xm)
        for i in range(m):
            J[i, j] = float((fp[i] - fm[i]) / (2 * h))
    return J


def cover_radius(x):
    C = [(mpf(x[2 * i]), mpf(x[2 * i + 1])) for i in range(11)]
    best = mpf(0)
    for tri in itertools.combinations(range(11), 3):
        u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
        if u[0] ** 2 + u[1] ** 2 > 1:
            continue
        d = min(sqrt((u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2) for c in C)
        if d > best:
            best = d
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
                best = d
    return best


def newton_on_family(x, N, h=mpf('1e-20'), iters=30):
    """Project x back to the active family, moving only within span(N)."""
    x = [mpf(v) for v in x]
    for it in range(iters):
        f = cons(x)
        if max(abs(v) for v in f) < mpf('1e-26'):
            break
        J = jac(cons, x, h)
        JN = J @ N
        dz = np.linalg.lstsq(JN, np.array([float(v) for v in f]), rcond=None)[0]
        xn = np.array([float(v) for v in x]) - JN @ dz
        x = [mpf(v) for v in xn]
    return x


def main():
    x0 = [mpf(v) for v in X0]
    print('residual at candidate:', '%.3e' % float(max(abs(v) for v in cons(x0))))
    J = jac(cons, x0, mpf('1e-20'))
    u, s, vt = np.linalg.svd(J)
    print('sv of constraint jacobian (19x22):', ['%.4e' % y for y in s])
    rk = int((s > 1e-7 * s[0]).sum())
    print('rank=%d nullity=%d' % (rk, 22 - rk))
    N = vt[rk:].T
    g0 = cover_radius(x0)
    print('gamma(x0) = %s' % nstr(g0, 22))
    print('\nparabola fits g(t) = g0 + a*t + b*t^2 along each null direction:')
    for k in range(N.shape[1]):
        vals = {}
        for t in (-2e-3, -1e-3, -3e-4, 0.0, 3e-4, 1e-3, 2e-3):
            x = np.array([float(v) for v in x0]) + t * N[:, k]
            x = newton_on_family(x.tolist(), N)
            vals[t] = float(cover_radius([mpf(v) for v in x]))
        ts = sorted(vals)
        A = np.array([[1, t, t * t] for t in ts])
        b = np.array([vals[t] for t in ts])
        coef = np.linalg.lstsq(A, b, rcond=None)[0]
        res = max(abs(A @ coef - b))
        print('  null %d: g0=%.20f   linear=%+.6e  quad=%+.6e   maxres=%.2e' %
              (k, coef[0], coef[1], coef[2], res))
        print('        values:', ' '.join('%+.3e:%+.17f' % (t, vals[t]) for t in ts))


if __name__ == '__main__':
    main()
