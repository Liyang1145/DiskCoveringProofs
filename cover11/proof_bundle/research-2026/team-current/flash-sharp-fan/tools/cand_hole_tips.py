# -*- coding: utf-8 -*-
"""Own instrument 2: hole vs conv(tips); tip coverage by hubs; tightness diagnostics.
No matplotlib: own convex-hull + point-in-polygon."""
import json, math, os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, os.pardir, "out")
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir, os.pardir, os.pardir))
R = 0.379983853119838689722261606136093214308718956152215317048319
with open(os.path.join(ROOT, "n11", "upper", "certified_object.json"), "r", encoding="utf-8") as f:
    obj = json.load(f)
C = np.array([[int(a) / 1e17, int(b) / 1e17] for a, b in obj["centers_scaled_1e17"]])
mod = np.array([np.hypot(*c) for c in C])
ring = [i for i in range(11) if mod[i] + R >= 1]
hub = [i for i in range(11) if mod[i] + R < 1]
lines = []
def P(s=""):
    lines.append(s); print(s)

arg = lambda i: math.atan2(C[i][1], C[i][0])
order = sorted(ring, key=arg)
P("[order] %s" % order)

# tips: inner crossing of the pair (order[k], order[k+1])
def crossing_inner(ci, cj, r):
    d = np.linalg.norm(cj - ci)
    m = (ci + cj) / 2
    hh = math.sqrt(max(0.0, r * r - d * d / 4))
    perp = np.array([-(cj - ci)[1], (cj - ci)[0]]) / d
    pts = [m + hh * perp, m - hh * perp]
    return min(pts, key=lambda p: np.linalg.norm(p))

tips = []
P("[tips] pair  |v|      angle(deg)   dist-h0   dist-h2   min-over-hubs  margin-to-r")
for k, i in enumerate(order):
    j = order[(k + 1) % 9]
    v = crossing_inner(C[i], C[j], R)
    tips.append(v)
    d0 = np.linalg.norm(v - C[hub[0]]); d2 = np.linalg.norm(v - C[hub[1]])
    P("       (%2d,%2d) %.9f %10.4f  %.9f %.9f  %.9f  %+.3e"
      % (i, j, np.linalg.norm(v), math.degrees(math.atan2(v[1], v[0])), d0, d2, min(d0, d2), min(d0, d2) - R))
tips = np.array(tips)

# own convex hull (monotone chain)
def hull(pts):
    pts = sorted(map(tuple, pts))
    def half(pts):
        h = []
        for p in pts:
            while len(h) >= 2 and (h[-1][0]-h[-2][0])*(p[1]-h[-2][1]) - (h[-1][1]-h[-2][1])*(p[0]-h[-2][0]) <= 0:
                h.pop()
            h.append(p)
        return h
    return half(pts)[:-1] + half(pts[::-1])[:-1]

H = np.array(hull(tips))
P("[hull] %d vertices: %s" % (len(H), np.round(H, 6).tolist()))
def in_hull(p, H):
    n = len(H)
    for i in range(n):
        a, b = H[i], H[(i + 1) % n]
        if (b[0]-a[0])*(p[1]-a[1]) - (b[1]-a[1])*(p[0]-a[0]) < -1e-15:
            return False
    return True
P("[hull] all 9 tips are hull vertices: %s" % (len(H) == 9))

# hole = points of D with all ring distances > R ; check containment in hull
N = 1100
hole = 0; out = 0; worst = None
for iy in range(N):
    y = -1 + 2 * (iy + 0.5) / N
    for ix in range(N):
        x = -1 + 2 * (ix + 0.5) / N
        if x * x + y * y > 1:
            continue
        p = np.array([x, y])
        dmin = min(np.linalg.norm(p - C[i]) for i in ring)
        if dmin <= R:
            continue
        hole += 1
        if not in_hull(p, H):
            out += 1
            depth = dmin - R
            if worst is None or depth > worst[0]:
                worst = (depth, x, y)
P("[hole] grid %d^2: hole=%d outside-hull=%d worst-depth-outside=%s" % (N, hole, out,
  None if worst is None else "%.3e at (%.4f,%.4f)" % worst))

# is the specific deep point p5 = (|c5|-R) u(phi5) in the hole and where?
i5 = 5
p5 = (mod[i5] - R) * C[i5] / mod[i5]
ds = sorted((np.linalg.norm(p5 - C[i]) - R, i) for i in ring)
P("[deep] p5=(%.5f,%.5f) |p5|=%.6f : ring margins (dist-R) sorted lowest: %s"
  % (p5[0], p5[1], np.linalg.norm(p5), [(int(i), round(float(d), 6)) for d, i in ds[:3]]))
P("[deep] p5 in hull(tips): %s ; hub dists %.6f %.6f (r=%.6f)"
  % (in_hull(p5, H), np.linalg.norm(p5 - C[hub[0]]), np.linalg.norm(p5 - C[hub[1]]), R))

# a* circle capacity
a_star = min(mod[i] for i in ring) - R
def beta(a, s, r):
    c = (a * a + s * s - r * r) / (2 * a * s)
    if c <= -1: return math.pi
    if c >= 1: return 0.0
    return math.acos(c)
s1, s2 = np.linalg.norm(C[hub[0]]), np.linalg.norm(C[hub[1]])
b1, b2 = beta(a_star, s1, R), beta(a_star, s2, R)
P("[cap] a*=%.9f  |h0|=%.9f |h2|=%.9f  beta1=%.6f deg beta2=%.6f deg  sum=%.6f deg  slack vs 180 = %+.6f deg"
  % (a_star, s1, s2, math.degrees(b1), math.degrees(b2), math.degrees(b1 + b2), math.degrees(b1 + b2 - math.pi)))

# Voronoi vertices (Delaunay triangle circumcentres) and tightness
from scipy.spatial import Delaunay
tri = Delaunay(C)
worst_slack = 0
P("[vor] triangle   circumradius   R-r        |x|")
for s in tri.simplices:
    t = C[s]
    d = 2 * (t[0][0]*(t[1][1]-t[2][1]) + t[1][0]*(t[2][1]-t[0][1]) + t[2][0]*(t[0][1]-t[1][1]))
    ux = ((t[0][0]**2+t[0][1]**2)*(t[1][1]-t[2][1]) + (t[1][0]**2+t[1][1]**2)*(t[2][1]-t[0][1]) + (t[2][0]**2+t[2][1]**2)*(t[0][1]-t[1][1]))/d
    uy = ((t[0][0]**2+t[0][1]**2)*(t[2][0]-t[1][0]) + (t[1][0]**2+t[1][1]**2)*(t[0][0]-t[2][0]) + (t[2][0]**2+t[2][1]**2)*(t[1][0]-t[0][0]))/d
    o = np.array([ux, uy]); rr = np.linalg.norm(o - t[0])
    P("       %-14s %.9f  %+.3e  %.6f" % (str(s), rr, rr - R, np.linalg.norm(o)))

# hub cell sizes at the optimum: farthest Voronoi vertex from each hub
for hji, hj in enumerate(hub):
    best = None
    for s in tri.simplices:
        if hj not in s: continue
        t = C[s]
        d = 2 * (t[0][0]*(t[1][1]-t[2][1]) + t[1][0]*(t[2][1]-t[0][1]) + t[2][0]*(t[0][1]-t[1][1]))
        ux = ((t[0][0]**2+t[0][1]**2)*(t[1][1]-t[2][1]) + (t[1][0]**2+t[1][1]**2)*(t[2][1]-t[0][1]) + (t[2][0]**2+t[2][1]**2)*(t[0][1]-t[1][1]))/d
        uy = ((t[0][0]**2+t[0][1]**2)*(t[2][0]-t[1][0]) + (t[1][0]**2+t[1][1]**2)*(t[0][0]-t[2][0]) + (t[2][0]**2+t[2][1]**2)*(t[1][0]-t[0][0]))/d
        o = np.array([ux, uy]); d2 = np.linalg.norm(o - C[hj])
        if best is None or d2 > best[0]:
            best = (d2, s, o)
    P("[hub%d] farthest Voronoi vertex of its cell: dist=%.9f (R-r=%+.3e) tri=%s |x|=%.6f"
      % (hj, best[0], best[0] - R, best[1], np.linalg.norm(best[2])))

with open(os.path.join(OUT, "cand_hole_tips.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
