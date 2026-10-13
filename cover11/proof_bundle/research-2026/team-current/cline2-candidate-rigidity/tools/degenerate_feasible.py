"""Feasibility of covering D at radius R with 11 disks, one of which is DEGENERATE-tangent:
the pinned disk sits at distance exactly R from the origin (so the origin lies exactly on
its boundary) and must own the sector opposite it.

Method: for a fixed R, minimise a soft-max violation
      Phi(x) = max over critical points p of ( min_i |p-c_i| - R )
with the pinned centre c_0 = R*(cos tau, sin tau) and rotation gauge fixed by y of centre 1.
Phi <= 0  <=>  the 11 radius-R disks cover D.
We bracket the minimal feasible R (feasibility monotone in R) and compare with s = 0.38.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C0 = np.array([[int(a) / 1e17 for a in b] for b in D['centers_scaled_1e17']])
R0 = float(D['certified_interval']['lo'])
Y1 = float(C0[1][1])


def crit_batch(C):
    C = [tuple(c) for c in C]
    n = len(C)
    pts = []
    for tri in itertools.combinations(range(n), 3):
        P, Q, W = C[tri[0]], C[tri[1]], C[tri[2]]
        d = 2 * (P[0] * (Q[1] - W[1]) + Q[0] * (W[1] - P[1]) + W[0] * (P[1] - Q[1]))
        if abs(d) < 1e-14:
            continue
        ux = ((P[0] ** 2 + P[1] ** 2) * (Q[1] - W[1]) + (Q[0] ** 2 + Q[1] ** 2) * (W[1] - P[1])
              + (W[0] ** 2 + W[1] ** 2) * (P[1] - Q[1])) / d
        uy = ((P[0] ** 2 + P[1] ** 2) * (W[0] - Q[0]) + (Q[0] ** 2 + Q[1] ** 2) * (P[0] - W[0])
              + (W[0] ** 2 + W[1] ** 2) * (Q[0] - P[0])) / d
        if ux * ux + uy * uy <= 1:
            pts.append((ux, uy))
    for i, j in itertools.combinations(range(n), 2):
        A_, B_ = C[i], C[j]
        ax, ay = A_[0] - B_[0], A_[1] - B_[1]
        Cc = ((A_[0] ** 2 + A_[1] ** 2) - (B_[0] ** 2 + B_[1] ** 2)) / 2
        a2 = ax * ax + ay * ay
        if a2 == 0 or Cc ** 2 > a2:
            continue
        m = (Cc * ax / a2, Cc * ay / a2)
        t = math.sqrt(a2 - Cc ** 2) / a2
        for sg in (1, -1):
            pts.append((m[0] - sg * t * ay, m[1] + sg * t * ax))
    return np.array(pts)


def build_centres(z, R, pinned_norm=True):
    """z = [tau, x1, y1, x2, y2, ..., x10, y10]  (centre 0 pinned)"""
    tau = z[0]
    C = np.zeros((11, 2))
    C[0] = R * np.array([math.cos(tau), math.sin(tau)])
    rest = z[1:].reshape(5, 2)   # only 5 free centres if z has 11 entries
    return C


def objective(z, R, pts0):
    """soft-max violation, with centres = 11 free coordinates (gauge: y of centre 1 fixed)
    z = [x0,y0, x1, x2,y2, x3,y3, ..., x10,y10] i.e. 21 entries."""
    C = np.zeros((11, 2))
    C[0] = z[0:2]
    C[1] = [z[2], Y1]
    for k in range(2, 11):
        C[k] = z[2 + 2 * k - 2:2 + 2 * k]
    pts = crit_batch(C)
    d = np.min(np.linalg.norm(pts[:, None, :] - C[None, :, :], axis=2), axis=1)
    return float(np.max(d - R))


def objective_pinned(z, R):
    """centre 0 pinned at distance R from the origin at angle tau = z[0]; the other 10 centres
    free (centre 1 y-gauge fixed).  z has 1 + 2 + 9*2 = 21 entries."""
    C = np.zeros((11, 2))
    C[0] = R * np.array([math.cos(z[0]), math.sin(z[0])])
    C[1] = [z[1], Y1]
    for k in range(2, 11):
        C[k] = z[2 + 2 * (k - 2):2 + 2 * (k - 2) + 2]
    pts = crit_batch(C)
    d = np.min(np.linalg.norm(pts[:, None, :] - C[None, :, :], axis=2), axis=1)
    return float(np.max(d - R))


def initial_pinned(R):
    """start from the saved centres: scale so that centre 0 has norm R, keep the rest"""
    C = C0.copy()
    tau = math.atan2(C[0][1], C[0][0])
    z = [tau]
    z += [C[1][0]]
    for k in range(2, 11):
        z += [float(C[k][0]), float(C[k][1])]
    return np.array(z)


def main():
    print('calibration on the saved configuration:')
    pts = crit_batch(C0)
    d = np.min(np.linalg.norm(pts[:, None, :] - C0[None, :, :], axis=2), axis=1)
    print('   cover radius = %.12f   (registered %.12f)' % (d.max(), R0))
    print()
    print('pinned-degenerate family: |c_0| = R exactly (origin on the boundary of disk 0)')
    for R in (0.37999, 0.38, 0.385, 0.39, 0.40, 0.42, 0.45):
        z0 = initial_pinned(R)
        best = None
        for trial in range(6):
            zz = z0.copy()
            if trial:
                rng = np.random.default_rng(trial)
                zz = z0 + rng.normal(0, 0.02 * trial, len(z0))
            o = minimize(objective_pinned, zz, args=(R,), method='Nelder-Mead',
                         options={'maxiter': 20000, 'xatol': 1e-10, 'fatol': 1e-14})
            if best is None or o.fun < best:
                best = o.fun
        print('   R = %.6f :  min violation = %+.3e  (%s)'
              % (R, best, 'FEASIBLE' if best <= 0 else 'infeasible'))


if __name__ == '__main__':
    main()
