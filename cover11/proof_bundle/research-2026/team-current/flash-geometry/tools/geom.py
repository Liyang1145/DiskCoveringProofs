"""Shared geometry helpers for the n=11 low-radius covering study.

Caliber: D = unit closed disk (R=1). All disks have radius rr (target radius,
e.g. 19/50). Lengths in units of the target radius R_D... no: in units of the
unit-disk radius (=1). Angles in radians.

Object: a "ring" configuration is a list of centers a_i (covers by |x-a_i|<=rr);
coverage of the target circle means every p with |p|=1 is within rr of some a_i.
The HOLE H is {x in D : |x-a_i|>rr for all i}; cl(H) must be covered by the two
hub disks of the same radius rr.
"""
import numpy as np

def arc_halfwidth(rho, rr):
    """Half angular width (about the origin) of the arc of the target circle
    covered by a disk of radius rr whose center is at distance rho from origin.
    Returns None if the disk misses the circle (rho < 1-rr or rho > 1+rr)."""
    if rho < 1.0 - rr - 1e-15 or rho > 1.0 + rr + 1e-15:
        return None
    c = (1.0 + rho * rho - rr * rr) / (2.0 * rho)
    c = min(1.0, max(-1.0, c))
    return float(np.arccos(c))

def arc_ends(rho, phi, rr):
    """Angular interval [lo,hi] of target-circle directions covered by
    center at polar (rho,phi), radius rr."""
    w = arc_halfwidth(rho, rr)
    if w is None:
        return None
    return (phi - w, phi + w)

def tiling_rho_uniform(m, rr):
    """rho such that m equal disks centered on a circle of radius rho with
    centers spaced 2*pi/m tile the target circle exactly (adjacent covered
    arcs touch, no overlap).  Solve m*arc_halfwidth(rho,rr) = pi."""
    lo, hi = 1.0 - rr + 1e-12, 1.0
    f = lambda rho: m * arc_halfwidth(rho, rr) - np.pi
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)

def tiling_r_uniform(m, rho):
    """rr such that m disks at radius rho spaced 2pi/m tile the circle."""
    # arc_halfwidth(rho,rr)=pi/m  ->  cos(pi/m) = (1+rho^2-rr^2)/(2rho)
    # -> rr^2 = 1+rho^2-2rho cos(pi/m)
    return float(np.sqrt(max(0.0, 1.0 + rho * rho - 2.0 * rho * np.cos(np.pi / m))))

def pocket_corners(rho_a, phi_a, rho_b, phi_b, rr):
    """Points of the hole between two overlapping covering disks of radius rr:
    the two intersection points of the boundaries of B(a,rr),B(b,rr) that lie
    outside both disks are the pocket's "corners" close to the origin; returns
    list of candidate extreme points (numpy arrays)."""
    a = np.array([rho_a * np.cos(phi_a), rho_a * np.sin(phi_a)])
    b = np.array([rho_b * np.cos(phi_b), rho_b * np.sin(phi_b)])
    d = b - a
    L = np.linalg.norm(d)
    if L == 0 or L > 2 * rr:
        return []
    u = d / L
    n = np.array([-u[1], u[0]])
    h = np.sqrt(rr * rr - (L / 2) ** 2)
    m = 0.5 * (a + b)
    return [m + h * n, m - h * n]

def min_enclosing_ball(pts):
    """Smallest enclosing circle of a point list (exact via Welzl/brute force)."""
    pts = [np.asarray(p, dtype=float) for p in pts]
    if not pts:
        return None, 0.0
    n = len(pts)
    if n == 1:
        return pts[0], 0.0
    best_c, best_r = None, float('inf')
    from itertools import combinations
    for i, j in combinations(range(n), 2):
        c = 0.5 * (pts[i] + pts[j])
        r = np.linalg.norm(pts[i] - c)
        if all(np.linalg.norm(p - c) <= r + 1e-12 for p in pts):
            if r < best_r:
                best_r, best_c = r, c
    for i, j, k in combinations(range(n), 3):
        ax, ay = pts[i]; bx, by = pts[j]; cx, cy = pts[k]
        d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if abs(d) < 1e-14:
            continue
        ux = ((ax**2 + ay**2) * (by - cy) + (bx**2 + by**2) * (cy - ay) + (cx**2 + cy**2) * (ay - by)) / d
        uy = ((ax**2 + ay**2) * (cx - bx) + (bx**2 + by**2) * (ax - cx) + (cx**2 + cy**2) * (bx - ax)) / d
        c = np.array([ux, uy])
        r = max(np.linalg.norm(p - c) for p in pts)
        if all(np.linalg.norm(p - c) <= r + 1e-12 for p in pts):
            if r < best_r:
                best_r, best_c = r, c
    return best_c, best_r

def hole_coverable_by(pts, rr):
    """Can ALL given exact hole points be covered by two disks of radius rr?"""
    pts = [np.asarray(p, dtype=float) for p in pts]
    if len(pts) <= 1:
        return True, None
    n = len(pts)
    # brute force over 2-colouring (smalled n only)
    from itertools import product
    for mask in product((0, 1), repeat=n):
        if all(m == 0 for m in mask):
            continue
        c1, r1 = min_enclosing_ball([pts[i] for i in range(n) if mask[i] == 0])
        c2, r2 = min_enclosing_ball([pts[i] for i in range(n) if mask[i] == 1])
        if (r1 <= rr + 1e-12) and (r2 <= rr + 1e-12):
            return True, (mask, c1, r1, c2, r2)
    return False, None
