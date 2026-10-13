"""Probe: can a 9-ring + 2-hub configuration at radius R ~ 0.38 have a sector of height 0?

Setup (inward-root representative, all quantities exact-by-construction scalars):
  * ring site i is placed at distance rho_i = sqrt(1+(R-h_i)^2-R^2) = sqrt(1-2Rh_i+h_i^2)
    from the origin, on direction theta_i, so that its disk of radius R cuts bd D with
    angular half-width
        w_i = t_i - arctan(h_i/(1-h_i)),   t_i = asin(R/r_cc_i),  r_cc_i = sqrt(1-2Rh_i+h_i^2),
    all exactly.
  * height h_i = radial distance from the unit-circle point nearest the site (i.e. the arc
    midpoint) to the SITE, i.e. how far the site sits from the arc it must own:
        h_i = 0   <=>  w_i = asin R  (max possible) and the site is at distance R from both arc
                       endpoints while the arc midpoint is at distance exactly R (tangency).
  * switch between sites i,i+1 = the point of bd D equidistant from both, on the arc between
    their directions; its modulus is 1 - (deviation), giving the gap d_i.

Covering radius of the whole 11-disk configuration is computed from the full critical set:
all triple circumcentres inside D plus all 11*10/2 bisector points on bd D, minimised over
the centres (i.e. max over p in D of min_i |p-c_i|).

Reported per configuration: gamma (covering radius), the heights h_i actually realised by the
sites, and whether any critical point lies outside the 11 disks.
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


def crit_points(C):
    """critical set: triple circumcentres in D and all pairwise bisector points on bd D."""
    C = [tuple(c) for c in C]
    n = len(C)
    pts = []
    for tri in itertools.combinations(range(n), 3):
        P, Q, W = C[tri[0]], C[tri[1]], C[tri[2]]
        d = 2 * (P[0] * (Q[1] - W[1]) + Q[0] * (W[1] - P[1]) + W[0] * (P[1] - Q[1]))
        if abs(d) < 1e-15:
            continue
        ux = ((P[0] ** 2 + P[1] ** 2) * (Q[1] - W[1]) + (Q[0] ** 2 + Q[1] ** 2) * (W[1] - P[1])
              + (W[0] ** 2 + W[1] ** 2) * (P[1] - Q[1])) / d
        uy = ((P[0] ** 2 + P[1] ** 2) * (W[0] - Q[0]) + (Q[0] ** 2 + Q[1] ** 2) * (P[0] - W[0])
              + (W[0] ** 2 + W[1] ** 2) * (Q[0] - P[0])) / d
        if ux * ux + uy * uy > 1:
            continue
        v = min(math.hypot(ux - c[0], uy - c[1]) for c in C)
        pts.append((v, ux, uy, ('V', tri)))
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
            p = (m[0] - sg * t * ay, m[1] + sg * t * ax)
            ds = sorted([(math.hypot(p[0] - c[0], p[1] - c[1]), k) for k, c in enumerate(C)])
            if {i, j} == {ds[0][1], ds[1][1]}:
                pts.append((ds[0][0], p[0], p[1], ('B', i, j)))
    return pts


def gamma_and_heights(C, Cring):
    """covering radius + realised heights for the 9 ring sites."""
    pts = crit_points(C)
    g = max(p[0] for p in pts)
    hs = []
    for c in Cring:
        rho = math.hypot(*c)
        w = math.acos(max(-1, min(1, (1 + rho ** 2 - R0 ** 2) / (2 * rho)))) if rho > 1e-12 else None
        hs.append((rho, w))
    return g, pts, hs


def report(tag, C, Cring):
    g, pts, hs = gamma_and_heights(C, Cring)
    print('%s: gamma = %.9f' % (tag, g))
    print('   ring (|c|, half-width, height-proxy 1-rho):')
    for i, (rho, w) in enumerate(hs):
        print('      ring%2d |c|=%.6f  w=%.6f  (1-|c|)=%.6f  w-ref=%.3e'
              % (RINGS[i], rho, w, 1 - rho, w - math.asin(R0)))
    tt = sorted(pts, reverse=True)[:6]
    print('   top critical points:')
    for v, x, y, tagp in tt:
        print('      %.9f at (%+.6f,%+.6f) %s' % (v, x, y, tagp))
    return g


def main():
    print('R0 = %.12f   U = 0.37999   s = 0.38' % R0)
    C = C0.copy()
    Cring = np.array([C0[i] for i in RINGS])
    print('\n=== sanity: the saved configuration through this probe ===')
    report('saved', C, Cring)
    print()
    # what does independence check give for the saved config heights?
    print('known-best covering radius (registered): 0.3799838531198387')


if __name__ == '__main__':
    main()
