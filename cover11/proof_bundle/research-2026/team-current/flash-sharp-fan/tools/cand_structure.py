# -*- coding: utf-8 -*-
"""Own instrument: structure of the record candidate for n=11 (q=0 fan class).
Reads the certified 1e17-scaled integer centres, r = R_stru (independently recomputed below
from the JSON if present, else taken from the documented ledger).
Outputs: ledger (t,o,gamma), ring cyclic order, Delaunay edges & triangle census,
hub degrees, circumradii of all Delaunay triangles, tight/max covering diagnostics,
tips, hull(tips) vs hole containment.
"""
import json, math, os, sys
import numpy as np
from scipy.spatial import Delaunay

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, os.pardir, "out")
os.makedirs(OUT, exist_ok=True)
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir, os.pardir, os.pardir))
OBJ = os.path.join(ROOT, "n11", "upper", "certified_object.json")

R_STRU = 0.379983853119838689722261606136093214308718956152215317048319  # documented candidate

with open(OBJ, "r", encoding="utf-8") as f:
    obj = json.load(f)
sc = obj["centers_scaled_1e17"]
C = np.array([[int(a) / 1e17, int(b) / 1e17] for a, b in sc])
n = len(C)
mod = [np.hypot(*c) for c in C]
lines = []
def P(s=""):
    lines.append(s)
    print(s)

P("[obj] n=%d  documented r_upper=%s" % (n, obj.get("statement", "")[:60]))
P("[obj] |c| : " + " ".join("%d:%.6f" % (i, m) for i, m in enumerate(mod)))
ring = [i for i in range(n) if mod[i] + R_STRU >= 1]          # disk meets dD
hub = [i for i in range(n) if mod[i] + R_STRU < 1]
P("[obj] ring=%s  hub=%s" % (ring, hub))
assert len(ring) == 9 and len(hub) == 2

# Delaunay
tri = Delaunay(C)
simp = tri.simplices
P("[del] #triangles=%d  #edges=%d" % (len(simp), len(set(tuple(sorted((s[k], s[(k+1) % 3])))
                                                        for s in simp for k in range(3)))))
edges = set()
for s in simp:
    for k in range(3):
        edges.add(tuple(sorted((s[k], s[(k + 1) % 3]))))
ring_edges = sorted(e for e in edges if e[0] in ring and e[1] in ring)

# cyclic order of the ring indices by argument
arg = lambda i: math.atan2(C[i][1], C[i][0])
order = sorted(ring, key=arg)
P("[ring] cyclic order (by polar angle) = %s" % order)
pos = {c: k for k, c in enumerate(order)}
def g(i, j):
    d = abs(pos[i] - pos[j]) % 9
    return min(d, 9 - d)
P("[ring] ring-ring Delaunay edges: %s" % [(e, g(*e)) for e in ring_edges])
P("[ring] #non-consecutive ring-ring Delaunay edges = %d"
  % sum(1 for e in ring_edges if g(*e) != 1))
hub_ring = sorted(e for e in edges if (e[0] in hub) ^ (e[1] in hub))
hub_hub = sorted(e for e in edges if e[0] in hub and e[1] in hub)
deg = {i: sum(1 for e in edges if i in e) for i in range(n)}
P("[ring] hub-hub edges %s ; hub degrees %s (sum=%d)"
  % (hub_hub, {i: deg[i] for i in hub}, sum(deg[i] for i in hub)))
P("[ring] #hub-ring Delaunay edges = %d" % len(hub_ring))
for i in hub:
    nb = sorted(j for e in hub_ring for j in (e[0], e[1]) if i in e and j != i)
    P("[ring]   hub %d ring-neighbours (%d): %s  positions %s" % (i, len(nb), nb, [pos[j] for j in nb]))

# circumradii of Delaunay triangles
def circum(a, b, c):
    ax, ay = a; bx, by = b; cx, cy = c
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(d) < 1e-18:
        return float("inf"), None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    o = np.array([ux, uy])
    return float(np.linalg.norm(o - a)), o

P("[circ] triangle  kind                circumradius   R-r        |x|    acute?")
for s in simp:
    t = [C[i] for i in s]
    rr, o = circum(*t)
    kinds = "".join("H" if i in hub else "R" for i in s)
    ac = all(np.dot(t[(k + 1) % 3] - t[k], t[(k + 2) % 3] - t[k]) > 0 for k in range(3))
    P("        %-14s %-4s  %.9f  %+.3e  %.6f  %s"
      % (str(s), kinds, rr, rr - R_STRU, np.linalg.norm(o), ac))

# ledger on the boundary circle
def t_of(a):
    ca = (1 + a * a - R_STRU * R_STRU) / (2 * a)
    return math.acos(max(-1.0, min(1.0, ca)))
ts = {i: t_of(mod[i]) for i in ring}
ph = {i: arg(i) for i in ring}
P("[led] i  |c|  t(deg)  phi(deg)  gamma(next,deg)  o(next,deg)")
gam, ov = {}, {}
for k, i in enumerate(order):
    j = order[(k + 1) % 9]
    gm = (ph[j] - ph[i]) % (2 * math.pi)
    gam[i] = gm
    ov[i] = ts[i] + ts[j] - gm
for k, i in enumerate(order):
    j = order[(k + 1) % 9]
    P("      %2d %.6f  %9.6f %10.6f  %12.6f %12.3e" % (i, mod[i], math.degrees(ts[i]), math.degrees(ph[i]), math.degrees(gam[i]), math.degrees(ov[i])))
P("[led] sum t (deg) = %.12f   (pi = 180)" % math.degrees(sum(ts.values())))
P("[led] sum o (deg) = %.3e ; max o (deg) = %.3e" % (math.degrees(sum(ov.values())), math.degrees(max(ov.values()))))
P("[led] min arc length l_i (deg) = %.6f" % min(math.degrees(2 * ts[i] - ov[order[k - 1]] - ov[i]) for k, i in enumerate(order)))

# tips: inner crossings of adjacent circle pair
def crossings(ci, cj, r):
    d = np.linalg.norm(cj - ci)
    if d > 2 * r:
        return []
    m = (ci + cj) / 2
    h2 = r * r - d * d / 4
    if h2 < 0:
        return []
    hh = math.sqrt(max(0.0, h2))
    perp = np.array([-(cj - ci)[1], (cj - ci)[0]]) / d
    return [m + hh * perp, m - hh * perp]

tips = []
P("[tip] k  |v_in|  |v_out|  rho_k-1  ...")
for k, i in enumerate(order):
    j = order[(k + 1) % 9]
    pts = crossings(C[i], C[j], R_STRU)
    if not pts:
        P("      %2d no crossing" % k); continue
    pts = sorted(pts, key=lambda p: np.linalg.norm(p))
    vin, vout = pts[0], pts[-1]
    tips.append(vin)
    P("      %2d %.9f %.9f  in-D=%s out-D=%s" % (k, np.linalg.norm(vin), np.linalg.norm(vout),
                                                 np.linalg.norm(vin) < 1, np.linalg.norm(vout) > 1))
tips = np.array(tips)

# tips lemma margin (numeric, sanity only): each tip outside every non-participating ring disk
marg = 1e9
for k in range(len(tips)):
    for i in ring:
        if g(order[k], i) <= 1:
            continue
        marg = min(marg, np.linalg.norm(tips[k] - C[i]) - R_STRU)
P("[tip] worst non-participating ring-disk margin = %+.3e" % marg)

# hull(tips) vs the true hole: sample polar+carteisan grid
from matplotlib.path import Path as MplPath
hull = tips[np.argsort(np.arctan2(tips[:, 1], tips[:, 0]))]
# only hull vertices matter, but tips are convex here (check)
def cross2(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
ccw = all(cross2(hull[i], hull[(i + 1) % 9], hull[(i + 2) % 9]) > 0 for i in range(9))
P("[hull] 9 tips in strictly convex position (ccw): %s" % ccw)
path = MplPath(hull)
inside = 0; hole = 0; hole_out = 0; worst = None
N = 900
for iy in range(N):
    y = -1 + 2 * (iy + 0.5) / N
    for ix in range(N):
        x = -1 + 2 * (ix + 0.5) / N
        if x * x + y * y > 1:
            continue
        p = np.array([x, y])
        dmin = min(np.linalg.norm(p - C[i]) for i in ring)
        if dmin <= R_STRU:
            continue
        hole += 1
        if path.contains_point(p):
            inside += 1
        else:
            hole_out += 1
            dm = dmin - R_STRU
            if worst is None or dm > worst[0]:
                worst = (dm, x, y)
P("[hull] grid %dx%d: hole samples=%d, inside hull=%d, outside hull=%d, worst depth=%s"
  % (N, N, hole, inside, hole_out, None if worst is None else "%.3e at (%.4f,%.4f)" % worst))

# covering function: max over D of dist to nearest centre; compare with r
N2 = 1200
mx = 0; argmax = None
for iy in range(N2):
    y = -1 + 2 * (iy + 0.5) / N2
    for ix in range(N2):
        x = -1 + 2 * (ix + 0.5) / N2
        if x * x + y * y > 1:
            continue
        p = np.array([x, y])
        dm = min(np.linalg.norm(p - C[i]) for i in range(n))
        if dm > mx:
            mx = dm; argmax = (x, y)
P("[cover] grid max of nearest-centre distance = %.9f at (%.5f,%.5f) ; r=%.9f ; r-max=%+.3e"
  % (mx, argmax[0], argmax[1], R_STRU, R_STRU - mx))

with open(os.path.join(OUT, "cand_structure.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
