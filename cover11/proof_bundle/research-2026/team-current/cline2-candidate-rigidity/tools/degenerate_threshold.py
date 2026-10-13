"""Tight numerics for the degenerate-sector question.

For each R we minimise  Phi(x) = max over critical points p of ( min_i |p-c_i| - R ),
with centre 0 pinned at |c_0| = R (origin exactly on the boundary of disk 0, the h_0 = 0
degenerate case).  Phi <= 0 iff the 11 radius-R disks cover D.  Phi is monotone decreasing
in R, so we bisect: the threshold R* is the smallest R admitting the pinned configuration.

Comparison: the target threshold is s = 0.38 (no 10-disk cover at s = 0.38, C840), and the
allowance is R <= U = 0.37999.
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
    P = np.array(pts)
    # deduplicate
    if len(P) > 1:
        key = np.round(P, 10)
        _, idx = np.unique(key, axis=0, return_index=True)
        P = P[np.sort(idx)]
    return P


def unpack(z, R):
    C = np.zeros((11, 2))
    C[0] = R * np.array([math.cos(z[0]), math.sin(z[0])])
    C[1] = [z[1], Y1]
    for k in range(2, 11):
        C[k] = [z[2 + 2 * (k - 2)], z[2 + 2 * (k - 2) + 1]]
    return C


def phi(z, R):
    C = unpack(z, R)
    pts = crit_batch(C)
    d = np.min(np.linalg.norm(pts[:, None, :] - C[None, :, :], axis=2), axis=1)
    return float(np.max(d - R))


def start(R):
    tau = math.atan2(C0[0][1], C0[0][0])
    z = [tau, float(C0[1][0])]
    for k in range(2, 11):
        z += [float(C0[k][0]), float(C0[k][1])]
    return np.array(z)


def solve(R, nrestart=10, seed=0):
    z0 = start(R)
    best = None
    rng = np.random.default_rng(seed)
    for tr in range(nrestart):
        zz = z0.copy()
        if tr == 1:
            # push the ring outward uniformly a little (helps when R is far off)
            for k in range(2, 11):
                zz[2 + 2 * (k - 2)] *= 0.97
                zz[2 + 2 * (k - 2) + 1] *= 0.97
        if tr >= 2:
            zz = z0 + rng.normal(0, 0.01 * tr, len(z0))
        o = minimize(phi, zz, args=(R,), method='Nelder-Mead',
                     options={'maxiter': 40000, 'maxfev': 40000, 'xatol': 1e-9, 'fatol': 1e-13})
        # local polish with Powell
        o2 = minimize(phi, o.x, args=(R,), method='Powell',
                      options={'maxiter': 20000, 'xtol': 1e-10, 'ftol': 1e-13})
        val = min(o.fun, o2.fun)
        if best is None or val < best[0]:
            best = (val, o2.x if o2.fun < o.fun else o.x)
    return best


def main():
    print('threshold search (pinned |c_0| = R, i.e. the h_0 = 0 degenerate sector)')
    for R in (0.37999, 0.38, 0.39, 0.40, 0.405, 0.41, 0.42, 0.43):
        val, x = solve(R, nrestart=8)
        print('   R = %.5f : min Phi = %+.6e   %s' % (R, val, 'FEASIBLE' if val <= 0 else 'infeasible'))
    print()
    # bisection between the last infeasible and first feasible bracket found above
    lo, hi = 0.40, 0.43
    vlo, _ = solve(lo, nrestart=6)
    vhi, _ = solve(hi, nrestart=6)
    if vlo > 0 and vhi <= 0:
        for _ in range(12):
            mid = (lo + hi) / 2
            v, _ = solve(mid, nrestart=6)
            if v <= 0:
                hi = mid
            else:
                lo = mid
        print('bracket: minimal feasible R for the pinned-degenerate family ~ %.6f' % hi)
        val, x = solve(hi, nrestart=14)
        C = unpack(x, hi)
        print('   at R = %.6f: Phi = %+.3e' % (hi, val))
        print('   centre norms:', ' '.join('%.4f' % np.linalg.norm(c) for c in C))
        print('   minimal site separations (sorted, first 12):')
        ds = sorted(np.linalg.norm(C[i] - C[j]) for i in range(11) for j in range(i + 1, 11))
        print('      ', ' '.join('%.4f' % d for d in ds[:12]))
        print('   2R = %.4f' % (2 * hi))


if __name__ == '__main__':
    main()
