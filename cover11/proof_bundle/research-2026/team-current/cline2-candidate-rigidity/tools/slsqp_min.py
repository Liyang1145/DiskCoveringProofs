"""Constrained minimisation of the covering radius (calibration only).

Objective: t.  Constraints: for the 9 tight Voronoi vertices and the 9 boundary spokes,
their nearest-site squared distance <= t^2; plus the two next-largest Voronoi vertices
(v = (0,3,10) and (0,4,9)) also <= t^2 (they are the next binding points).
Gauge: rotation fixed by pinning y(center 1) (a ring centre) to its saved value.

If the minimiser returns t < R the saved object is not a local optimum of the covering
radius, and we have a concrete global-mechanism failure.  If t* = R, the candidate passes
this local optimality test.  Starting point: the saved candidate at t = R.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C0 = np.array([[int(a) / 1e17 for a in b] for b in D['centers_scaled_1e17']])
R0 = float(D['certified_interval']['lo'])
SPOKES = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]
TRIPLES = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
           (1, 2, 8), (1, 2, 7)]
EXTRA = [(0, 3, 10), (0, 4, 9)]


def circ(C, tri):
    A, B, Cc = C[tri[0]], C[tri[1]], C[tri[2]]
    d1 = B[0] - A[0]; d2 = B[1] - A[1]; e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
    den = d1 * e2 - d2 * e1
    if abs(den) < 1e-18:
        return None
    bx = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
    by = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
    return ((bx * e2 - by * d2) / den, (d1 * by - e1 * bx) / den)


def spoke_pt(C, i, j):
    A, B = C[i], C[j]
    dx = B[0] - A[0]; dy = B[1] - A[1]
    L2 = dx * dx + dy * dy
    t = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / (2 * L2)
    fx = A[0] + t * dx; fy = A[1] + t * dy
    rem = 1 - (fx * fx + fy * fy)
    if rem < 0:
        return None
    # pick the branch inside the angular window between the two centres
    cands = []
    for sg in (1.0, -1.0):
        px = fx + sg * math.sqrt(rem) * (-dy) / math.sqrt(L2)
        py = fy + sg * math.sqrt(rem) * dx / math.sqrt(L2)
        cands.append((px, py))
    ai = math.atan2(A[1], A[0]) % (2 * math.pi); aj = math.atan2(B[1], B[0]) % (2 * math.pi)
    if aj < ai:
        aj += 2 * math.pi
    for (px, py) in cands:
        th = math.atan2(py, px) % (2 * math.pi)
        if th < ai:
            th += 2 * math.pi
        if ai - 1e-9 <= th <= aj + 1e-9:
            return (px, py)
    return None


def nd2(C, p):
    return min((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2 for c in C)


def point_fn(kind, tag):
    if kind == 'v':
        def f(x):
            C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
            p = circ(C, tag)
            return nd2(C, p)
        return f
    else:
        def f(x):
            C = [(x[2 * i], x[2 * i + 1]) for i in range(11)]
            p = spoke_pt(C, tag[0], tag[1])
            return nd2(C, p)
        return f


def main():
    fns = [('v', t) for t in TRIPLES] + [('s', s) for s in SPOKES] + [('v', t) for t in EXTRA]
    fns = [(k, t, point_fn(k, t)) for k, t in fns]
    x0 = np.array([v for c in C0 for v in c])
    t0 = float(math.sqrt(max(f(x0) for k, t, f in fns)))
    print('start: t0 = %.17f   R = %.17f' % (t0, R0))

    def obj(z):
        return z[22]

    def cons_eq(z):
        # rotation gauge: y(centre 1) fixed
        return np.array([z[3] - float(C0[1][1])])

    def cons_ineq(z):
        x = z[:22]; t = z[22]
        return np.array([t * t - f(x) for k, tg, f in fns])

    z0 = np.r_[x0, t0]
    bnds = [(-1.5, 1.5)] * 22 + [(0.3, 0.45)]
    print('running SLSQP ...')
    o = minimize(obj, z0, method='SLSQP', bounds=bnds,
                 constraints=[{'type': 'eq', 'fun': cons_eq}, {'type': 'ineq', 'fun': cons_ineq}],
                 options={'maxiter': 3000, 'ftol': 1e-16})
    print('success=%s  t* = %.17f  (delta vs R = %+.4e)' % (o.success, o.fun, o.fun - R0))
    print('min inequality slack (should be ~0 at the binding rows): %.3e' % min(cons_ineq(o.x)))
    print('per-centre displacement from the start:')
    for i in range(11):
        print('   c%2d (%+.4e, %+.4e)' % (i, o.x[2 * i] - x0[2 * i], o.x[2 * i + 1] - x0[2 * i + 1]))
    np.save(Path(__file__).parent.parent / 'out' / 'slsqp_min.npy', o.x)
    # refine with a second run
    o2 = minimize(obj, o.x, method='SLSQP', bounds=bnds,
                  constraints=[{'type': 'eq', 'fun': cons_eq}, {'type': 'ineq', 'fun': cons_ineq}],
                  options={'maxiter': 3000, 'ftol': 1e-18})
    print('refined t* = %.17f  (success=%s)' % (o2.fun, o2.success))
    print('refined delta vs R = %+.4e' % (o2.fun - R0))


if __name__ == '__main__':
    main()
