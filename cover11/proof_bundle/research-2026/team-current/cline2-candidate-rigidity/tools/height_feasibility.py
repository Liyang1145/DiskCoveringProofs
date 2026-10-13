"""Feasibility test: for a fixed radius R, is there an 11-disk cover of D with prescribed
degeneracy of one ring sector?

Variables: 22 centre coordinates (rotation gauge fixed by pinning y of the first ring site).
Feasible iff every point of the critical set (triple circumcentres in D + all pairwise
bisector points on bd D) is within R of at least one centre, i.e. the 11 radius-R disks
cover D.

Test family for "h_0 = 0": pin ring site k at the point
    c_k = m_k - R * u_k,   m_k = midpoint of the sector chord,  u_k = inward unit normal,
i.e. c_k is exactly at distance R from both sector endpoints and |c_k| = 1 - h_0 with the
height h_0 = 1 - |c_k|; h_0 = 0 puts c_k exactly on the chord midpoint (the degenerate
case).  We then ask for the smallest R at which the remaining centres can cover D.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C0 = np.array([[int(a) / 1e17 for a in b] for b in D['centers_scaled_1e17']])
R0 = float(D['certified_interval']['lo'])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
HUBS = [0, 2]


def crit(C):
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
    return pts


def violation(x, R, fixed=None):
    """max over critical points of (nearest-site distance - R); <= 0 iff covered."""
    C = x.reshape(11, 2)
    worst = -1e9
    for p in crit(C):
        dmin = min(math.hypot(p[0] - c[0], p[1] - c[1]) for c in C)
        worst = max(worst, dmin - R)
    return worst


def cover_radius(x):
    C = x.reshape(11, 2)
    return max(min(math.hypot(p[0] - c[0], p[1] - c[1]) for c in C) for p in crit(C))


def main():
    print('calibration: cover radius of the saved configuration = %.12f (registered %.12f)'
          % (cover_radius(C0.copy()), R0))
    print()
    # Fix ring site index k = 5 (index 5 in C0 ordering is 0.69452655549432385, 0.09408345290543541)
    # and place it at the chord midpoint of its sector, at distance R from both neighbours.
    for kk, (i_a, i_b) in enumerate([(5, 7), (7, 1)]):
        pass
    rings = RINGS
    # choose the degenerate sector: between ring sites RINGS[0]=1 and RINGS[1]=3? use the
    # actual consecutive pairs from the angular order:
    ORDER = [5, 7, 1, 8, 6, 4, 9, 10, 3]
    print('angular order:', ORDER)
    for h_deg in (0.0, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 0.05):
        # construct a trial configuration: saved centres, then move ring site ORDER[0]
        # onto the chord midpoint of its sector at height h_deg
        x = C0.copy()
        i0 = ORDER[0]
        j1 = ORDER[1]
        j8 = ORDER[8]
        A_ = x[j8] / np.linalg.norm(x[j8])
        B_ = x[j1] / np.linalg.norm(x[j1])
        mid = (A_ + B_) / 2.0
        mid /= np.linalg.norm(mid)
        # chord midpoint (on the unit circle) and inward normal
        u = -mid  # inward
        hh = h_deg
        # place c_i0 at distance R0 from both arc endpoints: solve along the radial line
        # point = (1-h) * mid_toward_origin  ... use the exact construction:
        # c = mid - R*u  shifted inward by h:  c = (mid - R*u) + h*(? )
        # simplest: c = mid - (R) * u  gives |c - Q| = R exactly when |mid|=1 and the
        # angle is small; we instead place c at  c = (1-h)*mid  and report its distances.
        c = (1 - hh) * mid
        x[i0] = c
        print(' h=%-8g: |c-%d| = %.9f, %.9f   |c| = %.9f   cover radius = %.9f'
              % (hh, j8, float(np.linalg.norm(c - x[j8])), j1, float(np.linalg.norm(c - x[j1])),
                 float(np.linalg.norm(c)), cover_radius(x)))


if __name__ == '__main__':
    main()
