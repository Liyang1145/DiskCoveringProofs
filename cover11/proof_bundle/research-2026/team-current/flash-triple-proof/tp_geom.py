# -*- coding: utf-8 -*-
"""tp_geom.py -- shared instrumentation for the triple-common-point hole problem.

Object (fixed here, once):
  r in (0, 19/50]; D = closed unit disk; nine closed disks of radius r whose arcs on
  S^1 are essential (nonzero), cyclically ordered, consecutive arcs overlap, each arc
  individually essential.  Three CONSECUTIVE disks (indices i, i+1, i+2) share a point p
  (the triple-common-point subclass).  Six remaining disks are "outer".
  Hole  H = D \\ union of the nine disks.  Question: can H be covered by two radius-r disks?

Instruments here (numeric only, NOT certificates):
  arc_halfwidth(centre)   -- actual arc half-angle of a disk of radius R
  deep_point(C)           -- maximize min_i |z-c_i| over z in D by Voronoi-vertex enumeration
                             + 1-D boundary scan + local polish
  ledger legallity checks -- overlaps/private widths, cluster union arc S, common point radius
"""
import math

R = 0.38
A = math.asin(R)
B = math.asin(2 * R)
T0 = math.pi - B - 5 * A          # >= t0 lower bound for the six outer half-widths
RHO0 = math.cos(T0) - math.sqrt(R * R - math.sin(T0) ** 2)   # >= rho0 lower bound for |c_j|
DMAX = B + 6 * A - math.pi        # total deficit bound
S_MAX = 2 * B                     # cluster union span bound


def arc_halfwidth(t_centre):
    """actual half-angle of the arc S^1 cap cut by B(c,r), c at distance t_centre from O."""
    if t_centre <= 0:
        return math.pi
    cth = (1 + t_centre * t_centre - R * R) / (2 * t_centre)
    if cth >= 1:
        return 0.0
    if cth <= -1:
        return math.pi
    return math.acos(cth)


def rho_minus(t):
    """inward root: centre distance of a disk whose actual half-width is exactly t."""
    return math.cos(t) - math.sqrt(max(R * R - math.sin(t) ** 2, 0.0))


def centre_of(t, psi):
    """inward-root centre at angle psi with half-width t."""
    rr = rho_minus(t)
    return (rr * math.cos(psi), rr * math.sin(psi))


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def dmin(C, z):
    return min(dist(z, c) for c in C)


# ---------------------------------------------------------------- local polish
def polish(C, z, step=0.02, tol=1e-13, iters=200):
    f = lambda w: dmin(C, w)
    best = f(z)
    s = step
    while s > 1e-12 and iters > 0:
        improved = False
        for dx, dy in ((s, 0), (-s, 0), (0, s), (0, -s), (s, s), (s, -s), (-s, s), (-s, -s)):
            w = (z[0] + dx, z[1] + dy)
            if math.hypot(*w) > 1.0:
                continue
            v = f(w)
            if v > best + tol * 0:
                if v > best + 1e-15:
                    best, z, improved = v, w, True
        iters -= 1
        if not improved:
            s *= 0.5
    return best, z


def deep_point(C, ngrid=240):
    """maximize dmin over the closed unit disk.

    three candidate families:
      (i)  interior local maxima: Voronoi vertices (equidistant 3-subsets) inside D
      (ii) boundary local maxima of dmin on |z| = 1 (dmin is min of smooth functions on
           the circle; local maxima occur at antipodes of single centres or at crossings)
      (iii) grid seeds (safety)
    """
    cands = []
    n = len(C)
    # (i) circumcentres of all triples
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                ax, ay = C[i]; bx, by = C[j]; cx, cy = C[k]
                d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
                if abs(d) < 1e-15:
                    continue
                ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay)
                      + (cx * cx + cy * cy) * (ay - by)) / d
                uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx)
                      + (cx * cx + cy * cy) * (bx - ax)) / d
                if math.hypot(ux, uy) <= 1.0:
                    # must be a genuine Voronoi vertex (no other centre closer)
                    dd = dmin(C, (ux, uy))
                    if abs(dd - dist((ux, uy), C[i])) < 1e-9:
                        cands.append((dd, (ux, uy)))
    # (ii) boundary: 1-D scan with breakpoints + antipodes
    N = 720
    for idx in range(N):
        th = 2 * math.pi * idx / N
        p = (math.cos(th), math.sin(th))
        cands.append((dmin(C, p), p))
    for c in C:
        nc = math.hypot(*c)
        if nc > 0:
            p = (-c[0] / nc, -c[1] / nc)
            cands.append((dmin(C, p), p))
    # (iii) grid seeds over the disk
    for i in range(ngrid):
        rr = math.sqrt((i + 0.5) / ngrid)
        for j in range(max(1, int(2 * math.pi * rr * ngrid))):
            th = 2 * math.pi * j / max(1, int(2 * math.pi * rr * ngrid))
            p = (rr * math.cos(th), rr * math.sin(th))
            cands.append((dmin(C, p), p))
    cands.sort(key=lambda t: -t[0])
    best = (-1.0, (0.0, 0.0))
    for dd, p in cands[:40]:
        v, w = polish(C, p, step=0.01)
        if v > best[0]:
            best = (v, w)
    return best


# ---------------------------------------------------------------- legal-builders
def arcs_from_centres(C):
    """actual half-width of each disk's arc (radians)."""
    return [arc_halfwidth(math.hypot(*c)) for c in C]


def ledger(C, cluster_idx=(0, 1, 2)):
    """arc ledger: centres are given in cyclic order of their arcs.
    returns dict with t (half-widths), overlaps o_k (arc i-1 with arc i), private widths,
    cluster union span S, legality flags."""
    t = arcs_from_centres(C)
    n = len(C)
    ph = [math.atan2(c[1], c[0]) for c in C]
    # unroll by cyclic order given (assumed sorted)
    lo = ph[0] - t[0]; hi = ph[0] + t[0]
    span = []
    for k in range(n):
        a, b = ph[k] - t[k], ph[k] + t[k]
        span.append((a, b))
    o = []
    for k in range(n):
        k2 = (k + 1) % n
        gap = (span[k2][0] - span[k][1])
        if k2 == 0:
            gap += 2 * math.pi
        o.append(t[k] + t[k2] - gap)
    priv = [2 * t[k] - o[k - 1] - o[k] for k in range(n)]
    ci = list(cluster_idx)
    S = (span[ci[-1]][1] - span[ci[0]][0])
    return dict(t=t, o=o, priv=priv, S=S, ph=ph, span=span)


def cluster_common_point(C3):
    """min over x of max_i |x - c_i|  (radius of the smallest enclosing circle) --
    computed by enumerating circumcircles (up to 3 points) + pairwise diameters."""
    best = (min(dist((0, 0), c) for c in C3), (0.0, 0.0))
    pts = list(C3)
    n = len(pts)
    for i in range(n):
        for j in range(i + 1, n):
            mid = ((pts[i][0] + pts[j][0]) / 2, (pts[i][1] + pts[j][1]) / 2)
            r = dist(mid, pts[i]) / 2 * 1.0
            m = max(dist(mid, c) for c in pts)
            if m < best[0]:
                best = (m, mid)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                ax, ay = pts[i]; bx, by = pts[j]; cx, cy = pts[k]
                d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
                if abs(d) < 1e-15:
                    continue
                ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay)
                      + (cx * cx + cy * cy) * (ay - by)) / d
                uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx)
                      + (cx * cx + cy * cy) * (bx - ax)) / d
                m = max(dist((ux, uy), c) for c in pts)
                if m < best[0]:
                    best = (m, (ux, uy))
    return best


def sep3_packing(C):
    """Largest k such that the hole contains k points pairwise > 2r apart (numeric, grid-free:
    exhaustive over Voronoi-vertex candidates + boundary antipodes + max-min point).
    Returns (k, witness points).  Greedy exact for k<=3 by enumeration of candidate sets."""
    cand = []
    n = len(C)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                ax, ay = C[i]; bx, by = C[j]; cx, cy = C[k]
                d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
                if abs(d) < 1e-15:
                    continue
                ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay)
                      + (cx * cx + cy * cy) * (ay - by)) / d
                uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx)
                      + (cx * cx + cy * cy) * (bx - ax)) / d
                if math.hypot(ux, uy) <= 1.0 and dmin(C, (ux, uy)) > R:
                    cand.append((ux, uy))
    N = 2000
    for idx in range(N):
        th = 2 * math.pi * idx / N
        p = (math.cos(th), math.sin(th))
        if dmin(C, p) > R:
            cand.append(p)
    best = ([], 0)
    for i in range(len(cand)):
        for j in range(i + 1, len(cand)):
            if dist(cand[i], cand[j]) <= 2 * R:
                continue
            for k in range(j + 1, len(cand)):
                if dist(cand[i], cand[k]) > 2 * R and dist(cand[j], cand[k]) > 2 * R:
                    return (3, [cand[i], cand[j], cand[k]])
            best = max(best, ([cand[i], cand[j]], 2), key=lambda z: z[1])
    return (best[1], best[0])
