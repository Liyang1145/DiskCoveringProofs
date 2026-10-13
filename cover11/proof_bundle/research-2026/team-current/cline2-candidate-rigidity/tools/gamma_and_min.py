"""Feasibility of the active-constraint family + attempted descent on the covering radius.

(1) gamma computed the correct way: max over (a) all triple Voronoi vertices inside D and
    (b) all 9 perpendicular-bisector intersections with bd D (the only boundary points where
    the "two nearest sites" relation can change).
(2) local minimisation of gamma over the 22 centres from the candidate (Nelder-Mead and
    SLSQP), reporting whether any decrease below R is found.
(3) the null directions of the 18 active constraints: does gamma stay exactly constant?

Calibration only.
"""
import json, io, math, itertools, time
import numpy as np
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C0 = np.array([[int(a) / 1e17 for a in b] for b in D['centers_scaled_1e17']])
R0 = float(D['certified_interval']['lo'])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]


def gamma(x):
    C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
    best = 0.0
    for tri in itertools.combinations(range(11), 3):
        A, B, Cc = C[tri[0]], C[tri[1]], C[tri[2]]
        d1 = B[0] - A[0]; d2 = B[1] - A[1]; e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
        den = d1 * e2 - d2 * e1
        if abs(den) < 1e-17:
            continue
        bx = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        by = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        ux = (bx * e2 - by * d2) / den
        uy = (d1 * by - e1 * bx) / den
        if ux * ux + uy * uy > 1:
            continue
        d = min(math.hypot(ux - c[0], uy - c[1]) for c in C)
        if d > best:
            best = d
    for k in range(9):
        i = RINGS[k]; j = RINGS[(k + 1) % 9]
        # perpendicular bisector intersection with bd D (both branches)
        A, B = C[i], C[j]
        dx = B[0] - A[0]; dy = B[1] - A[1]
        L2 = dx * dx + dy * dy
        if L2 == 0:
            continue
        t = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / (2 * L2)
        fx = A[0] + t * dx; fy = A[1] + t * dy
        rem = 1 - (fx * fx + fy * fy)
        if rem < 0:
            continue
        for sg in (1.0, -1.0):
            px = fx + sg * math.sqrt(rem) * (-dy) / math.sqrt(L2)
            py = fy + sg * math.sqrt(rem) * dx / math.sqrt(L2)
            d = min(math.hypot(px - c[0], py - c[1]) for c in C)
            if d > best:
                best = d
    return best


def main():
    x0 = np.array([v for c in C0 for v in c])
    g0 = gamma(x0)
    print('gamma(saved object)        = %.17f' % g0)
    print('certified lo (R)           = %.17f' % R0)
    print('certified hi               = %.17f' % float(D['certified_interval']['hi']))
    print('gamma - hi                 = %+.3e' % (g0 - float(D['certified_interval']['hi'])))

    print('\nlocal minimisation of gamma from the candidate (Nelder-Mead):')
    from scipy.optimize import minimize
    res = {}
    for opts in ({'maxiter': 40000, 'xatol': 1e-15, 'fatol': 1e-18},
                 {'maxiter': 40000, 'xatol': 1e-15, 'fatol': 1e-18, 'initial_simplex': None}):
        o = minimize(gamma, x0, method='Nelder-Mead', options=opts)
        print('   final gamma=%.17f  (delta=%+.3e)  nfev=%d' % (o.fun, o.fun - g0, o.nfev))
        res[o.fun] = o.x
    best = min(res)
    xb = res[best]
    print('   best = %.17f   ||x-x0||=%.3e' % (best, np.linalg.norm(xb - x0)))
    np.save(ROOT / 'research-2026' / 'team-current' / 'cline2-candidate-rigidity' / 'out' / 'nm_result.npy', xb)
    # report per-centre displacement
    print('   per-centre displacement:')
    for i in range(11):
        dx = xb[2 * i] - x0[2 * i]; dy = xb[2 * i + 1] - x0[2 * i + 1]
        print('     c%2d  (%+.3e, %+.3e)  |d|=%.3e' % (i, dx, dy, math.hypot(dx, dy)))
    return xb


if __name__ == '__main__':
    main()
