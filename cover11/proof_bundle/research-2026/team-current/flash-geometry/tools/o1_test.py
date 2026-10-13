"""O1 sub-claim test.

Setting: r = 0.38, unit disk D.  Three RING disks B(a_j,r) (so 1-r <= |a_j| <= 1)
which SHARE a common point p in D of equal distance:
      |a_j - p| = d  for j=1,2,3,  p in D,  0 <= d <= r.
(That is the "three rings have a common Voronoi vertex p" situation: the vertex
 distance is d <= r because the cover must hold at p.)

Claim under test: the union U of the three boundary arcs
     arc_j = { u in bd(D) : |u - a_j| <= r }
always has width  |U| < 2*pi - 12*asin(r)  = 1.60562975...
(for any 0<d<=r and any p).

We maximise |U| numerically (relaxing all Voronoi-consecutivity conditions, so the
bound is an upper bound for the real class if the max is below threshold).
"""
import numpy as np, itertools

r = 0.38
THR = 2*np.pi - 12*np.arcsin(r)
print("r =", r, " 2*asin(r) = %.12f" % (2*np.arcsin(r)), " threshold 2pi-12asin r = %.12f" % THR)

def arc_of(a):
    """angular interval of bd(D) covered by B(a,r); None if it misses."""
    rho = np.hypot(*a)
    if rho + r < 1.0 or rho > 1 + r:
        return None
    c = (1 + rho*rho - r*r)/(2*rho)
    c = min(1.0, max(-1.0, c))
    t = np.arccos(c)
    psi = np.arctan2(a[1], a[0])
    return (psi - t, psi + t)

def union_width(arcs):
    arcs = [a for a in arcs if a is not None]
    if not arcs:
        return 0.0
    iv = []
    for lo, hi in arcs:
        iv.append((lo, hi))
        iv.append((lo + 2*np.pi, hi + 2*np.pi))
    iv.sort()
    best = 0.0
    for s in range(len(arcs)):
        cur_lo, cur_hi = iv[s]
        tot = 0.0; cl, ch = cur_lo, cur_hi
        # merge greedily from this start
        for (lo, hi) in iv:
            if lo > ch + 1e-15:
                tot += ch - cl
                cl, ch = lo, hi
            else:
                ch = max(ch, hi)
        tot += ch - cl
        best = max(best, min(tot, 2*np.pi))
    return best

def Uwidth(P, d, phis):
    p = np.array([P, 0.0])
    arcs = []
    for ph in phis:
        a = p + d*np.array([np.cos(ph), np.sin(ph)])
        rho = np.hypot(*a)
        if not (1 - r - 1e-12 <= rho <= 1 + 1e-12):
            return -1.0                       # infeasible
        arcs.append(arc_of(a))
    return union_width(arcs)

best = (-1, None)
for P in np.linspace(0.0, 1.0, 101):
    for d in np.linspace(0.02, r, 19):
        for ph1 in np.linspace(-np.pi, np.pi, 37, endpoint=False):
            for ph2 in np.linspace(-np.pi, np.pi, 37, endpoint=False):
                for ph3 in np.linspace(-np.pi, np.pi, 37, endpoint=False):
                    if not (ph1 <= ph2 <= ph3):
                        continue
                    v = Uwidth(P, d, (ph1, ph2, ph3))
                    if v > best[0]:
                        best = (v, (P, d, ph1, ph2, ph3))
print("grid max |U| = %.6f  at (P,d,phis) = %s" % (best[0], np.round(best[1], 6) if best[1] else None))
print("threshold      = %.6f   slack = %.6f" % (THR, THR - best[0]))
