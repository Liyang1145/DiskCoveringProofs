# -*- coding: utf-8 -*-
"""
r20-alternative / read-only probe of the n=11 certified upper-bound object.

Purpose (strategic, not a certificate):
  Which constraint is BINDING at the certified candidate?
   (a) boundary seam between two ring disks,
   (b) interior Voronoi vertex (waist: ring+hub or hub+hub),
   (c) boundary arc saturation (sum of ring arcs = 2*pi).
Also: is the hole's 2-center radius close to the covering radius (two-center route)
or far below it (two-center route cannot be sharp)?

Inputs (read-only): n11/upper/certified_object.json  (integers/1e17)
Output: printed table only (no writes outside this directory).
"""
import json, os, sys
from mpmath import mp, mpf, sqrt, acos, pi, cos, sin, atan2

mp.dps = 40

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OBJ = os.path.join(ROOT, "n11", "upper", "certified_object.json")

with open(OBJ, encoding="utf-8-sig") as fh:
    raw = json.load(fh)
S = mpf(10) ** int(raw["decimals"])
C = [(mpf(str(a)) / S, mpf(str(b)) / S) for a, b in raw["centers_scaled_1e17"]]
n = len(C)


def dist(p, c):
    return sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2)


def depth(p):
    return min(dist(p, c) for c in C)


def argdepth(p):
    ds = [dist(p, c) for c in C]
    m = min(ds)
    return m, [i for i, d in enumerate(ds) if d <= m * (1 + mpf(10) ** -25)]


# ---- 1. candidate family: V3 (circumcenters of triples inside D) ----
cands = []
for i in range(n):
    for j in range(i + 1, n):
        for k in range(j + 1, n):
            (ax, ay), (bx, by), (cx, cy) = C[i], C[j], C[k]
            d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
            if abs(d) < mpf(10) ** -25:
                continue
            ux = ((ax ** 2 + ay ** 2) * (by - cy) + (bx ** 2 + by ** 2) * (cy - ay)
                  + (cx ** 2 + cy ** 2) * (ay - by)) / d
            uy = ((ax ** 2 + ay ** 2) * (cx - bx) + (bx ** 2 + by ** 2) * (ax - cx)
                  + (cx ** 2 + cy ** 2) * (bx - ax)) / d
            p = (ux, uy)
            if p[0] ** 2 + p[1] ** 2 <= 1 + mpf(10) ** -30:
                cands.append(("V3", (i, j, k), p, depth(p)))

# ---- 2. V2b: bisector of pair i,j intersected with |p| = 1 ----
for i in range(n):
    for j in range(i + 1, n):
        ax, ay = C[i]
        bx, by = C[j]
        mx, my = (ax + bx) / 2, (ay + by) / 2
        dx, dy = bx - ax, by - ay
        # points p with |p|=1 and |p-a|^2 = |p-b|^2  <=>  2 p.(b-a) = |b|^2-|a|^2
        rhs = (bx ** 2 + by ** 2 - ax ** 2 - ay ** 2) / 2
        nrm = sqrt(dx ** 2 + dy ** 2)
        dd = rhs / nrm            # signed distance from origin to the bisector line
        ux, uy = dx / nrm, dy / nrm   # normal direction
        if abs(dd) > 1:
            continue
        h = sqrt(1 - dd ** 2)
        for sgn in (1, -1):
            p = (dd * ux - sgn * h * uy, dd * uy + sgn * h * ux)
            cands.append(("V2b", (i, j), p, depth(p)))

# V1: radial points +-c/|c| are never maximal here (all |c|<1); skip but record depth
R, arg = None, None
for tag, idx, p, d in cands:
    if R is None or d > R:
        R, arg = d, (tag, idx, p)

print("candidate count:", len(cands))
print("R_D(numerical, candidate family) =", mp.nstr(R, 25))
print("argmax type/idx =", arg[0], arg[1])
print("argmax point     =", mp.nstr(arg[2][0], 18), mp.nstr(arg[2][1], 18), " |p| =", mp.nstr(sqrt(arg[2][0] ** 2 + arg[2][1] ** 2), 18))
mm, act = argdepth(arg[2])
print("active centers at argmax:", act, " common value =", mp.nstr(mm, 25))

# all local maxima above a threshold: report the top 8 distinct candidates
cands.sort(key=lambda t: -t[3])
print("\ntop distinct candidates (depth, type, idx, point):")
seen = []
for tag, idx, p, d in cands:
    if any(sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2) < mpf(10) ** -6 for q in seen):
        continue
    seen.append(p)
    print("  ", mp.nstr(d, 20), tag, idx, "(", mp.nstr(p[0], 12), ",", mp.nstr(p[1], 12), ")")
    if len(seen) >= 8:
        break

# ---- 3. ring/hub classification and boundary arcs ----
print("\nindex  |c|            role   arc halfwidth psi (deg)   seam-relevant")
info = []
for i, c in enumerate(C):
    d = sqrt(c[0] ** 2 + c[1] ** 2)
    role = "hub" if d < 1 - R else "ring"
    if role == "ring":
        cs = (1 + d * d - R * R) / (2 * d)
        cs = min(mpf(1), max(mpf(-1), cs))
        psi = acos(cs)
        info.append((i, d, psi))
        print(f"{i:5d}  {mp.nstr(d, 12):14s} {role}   {mp.nstr(psi * 180 / pi, 12)}")
    else:
        print(f"{i:5d}  {mp.nstr(d, 12):14s} {role}")
    info.append((i, d, None)) if role == "hub" else None

tot = sum(psi for _, _, psi in info if psi is not None)
print("\nsum of ring arc halfwidths =", mp.nstr(tot, 15), " = ", mp.nstr(tot * 180 / pi, 10), "deg",
      "  (pi =", mp.nstr(pi, 12), ")", " slack =", mp.nstr(tot - pi, 10))
print("max possible halfwidth arcsin(R) =", mp.nstr(acos(sqrt(1 - R * R)) * 180 / pi, 12), "deg")

# ---- 4. boundary depth profile: local maxima via sampled + refined seams ----
N = 200000
best = None
arr = []
for t in range(N):
    th = 2 * pi * t / N
    p = (cos(th), sin(th))
    dd = depth(p)
    arr.append((dd, th))
arr.sort(key=lambda x: -x[0])
print("\nboundary depth max over %d samples = %s at theta = %s deg" % (
    N, mp.nstr(arr[0][0], 20), mp.nstr(arr[0][1] * 180 / pi, 12)))
mm, act = argdepth((cos(arr[0][1]), sin(arr[0][1])))
print("  active centers:", act, " common value:", mp.nstr(mm, 20))

# ---- 5. interior Voronoi vertices: max interior depth (waist) ----
bestv = None
for tag, idx, p, d in cands:
    if tag != "V3":
        continue
    if p[0] ** 2 + p[1] ** 2 > 1 - mpf(10) ** -12:
        continue
    if bestv is None or d > bestv[3]:
        bestv = (tag, idx, p, d)
print("\nmax interior V3 depth =", mp.nstr(bestv[3], 20), " at", bestv[1], "(",
      mp.nstr(bestv[2][0], 12), ",", mp.nstr(bestv[2][1], 12), ")",
      " |p| =", mp.nstr(sqrt(bestv[2][0] ** 2 + bestv[2][1] ** 2), 12))
roles = ["hub" if sqrt(C[i][0] ** 2 + C[i][1] ** 2) < 1 - R else "ring" for i in range(n)]
print("  roles of that triple:", [(i, roles[i]) for i in bestv[1]])

# ---- 6. hole (D minus union of 9 ring disks): max inscribed radius (distance to the ring union) ----
ring = [i for i in range(n) if roles[i] == "ring"]
hub = [i for i in range(n) if roles[i] == "hub"]
print("\nring indices:", ring, " hub indices:", hub)


def dist_to_ring_union(p):
    """distance from p to the union of the 9 ring disks (positive iff p is outside)."""
    return min(dist(p, C[i]) - R for i in ring)


best_hole = mpf(0)
best_pt = None
M = 260
for a in range(M):
    for b in range(M):
        x = -1 + 2 * mpf(a) / (M - 1)
        y = -1 + 2 * mpf(b) / (M - 1)
        if x * x + y * y > 1:
            continue
        p = (x, y)
        if dist_to_ring_union(p) > 0:
            d = dist_to_ring_union(p)
            if d > best_hole:
                best_hole, best_pt = d, p
print("coarse hole max inscribed radius (distance to the ring-disk union) =",
      mp.nstr(best_hole, 12), "at", mp.nstr(best_pt[0], 10), mp.nstr(best_pt[1], 10))
print("  R =", mp.nstr(R, 12), "  (this is the ONE-center/'MEC' scale, not the 2-center one; see hole_two_center_check.py)")
