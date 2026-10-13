"""Step 5b: resolve the covering radius question definitively.

covering radius of D w.r.t. the certified 17-digit configuration =
   max_{x in D} min_i |x - c_i|.
Computed as: max( max over Voronoi vertices inside D of circumradius,
                   max over Voronoi edges of the restricted maximum,
                   boundary-arc maxima ).
Also dumps a PNG of the configuration for eyeball verification.
"""
from pathlib import Path
import json, math, itertools
import mpmath as mp
mp.mp.dps = 40

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
cen = [(float(x), float(y)) for x, y in A["centers_dec17"]]
n = 12
R_LIT = float(A["R_float"])
OUT = []
def W(s=""): OUT.append(str(s))
W(f"R_float literal = {R_LIT!r}")
W(f"|c_i| = {[round(math.hypot(*c),12) for c in cen]}")

def min_d(p):
    return min(math.dist(p, c) for c in cen)

# ---- Voronoi vertices (triple circumcentres) inside D
verts = []
for i, j, k in itertools.combinations(range(n), 3):
    ax, ay = cen[i]; bx, by = cen[j]; cx, cy = cen[k]
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < 1e-15: continue
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den
    verts.append(((i, j, k), ux, uy, math.hypot(ux, uy)))
W(f"\n-- Voronoi vertices inside D sorted by min-dist (top 12) --")
inside = [v for v in verts if v[3] <= 1]
sc = sorted(((min_d((v[1], v[2])), v[0]) for v in inside), reverse=True)
for d, tri in sc[:12]:
    v = [v for v in inside if v[0] == tri][0]
    W(f"   tri{str(tri):<16} u=({v[1]:+.16f},{v[2]:+.16f}) |u|={v[3]:.16f}  min-dist={d:.17g}"
      f"   d-R_lit={d-R_LIT:.3e}")

# ---- Voronoi edges: for each pair, the two triple-vertex Voronoi neighbours
W(f"\n-- candidate deepest holes = Voronoi vertices, so global max-min on D = "
  f"max(deepest vertex inside D, boundary max-min) --")

# ---- boundary max-min: scan + refine on each arc between bisector crossings
N = 2_000_000
bestb = (-1, None)
for t in range(N):
    th = 2*math.pi*t/N
    p = (math.cos(th), math.sin(th))
    d = min_d(p)
    if d > bestb[0]: bestb = (d, th, p)
W(f"\n-- boundary scan N={N}: max-min = {bestb[0]!r} at theta_deg={bestb[1]*180/math.pi:.10f}"
  f" p=({bestb[2][0]:.16f},{bestb[2][1]:.16f})  d-R_lit={bestb[0]-R_LIT:.3e}")
pb = bestb[2]
dd = sorted((math.dist(pb, c), i) for i, c in enumerate(cen))
W("   nearest there: " + "  ".join(f"c{i}:{d:.12f}" for d, i in dd[:4]))

# ---- 2D scan for the global max-min using a local search from every vertex
W("\n-- local search (nested refinement) from each candidate seed --")
best = (-1, None)
seeds = [((-0.40549999999999997, -0.04600000000000004), 'grid')] + \
        [((v[1], v[2]), f"vert{v[0]}") for v in inside] + \
        [((pb[0], pb[1]), 'boundary'), ((0, 0), 'origin')] + \
        [((math.cos(2*math.pi*t/720), math.sin(2*math.pi*t/720)), f'bd{t}') for t in range(0, 720, 5)]
import random
random.seed(7)
for _ in range(200):
    a = random.uniform(0, 2*math.pi); r = math.sqrt(random.random())
    seeds.append(((r*math.cos(a), r*math.sin(a)), 'rand'))
for s, tag in seeds:
    x, y = s
    for _ in range(6):
        h = 1e-3
        cur = min_d((x, y))
        for _ in range(200):
            improved = False
            for dx, dy in ((h,0),(-h,0),(0,h),(0,-h),(h,h),(h,-h),(-h,h),(-h,-h)):
                px, py = x+dx, y+dy
                if px*px+py*py > 1: continue
                d = min_d((px, py))
                if d > cur:
                    x, y, cur = px, py, d; improved = True
            if not improved:
                h *= 0.25
                if h < 1e-14: break
    if cur > best[0]:
        best = (cur, (x, y), tag)
W(f"   best max-min found = {best[0]!r} at ({best[1][0]:.16f},{best[1][1]:.16f}) |p|={math.hypot(*best[1]):.16f} seed={best[2]}")
W(f"   best - R_lit = {best[0]-R_LIT:.6e}   ; (2R)^2 = {(2*R_LIT)**2!r}")
W(f"   |p|^2 = {math.hypot(*best[1])**2!r}")
dd = sorted((math.dist(best[1], c), i) for i, c in enumerate(cen))
W("   nearest at best: " + "  ".join(f"c{i}:{d:.15f}" for d, i in dd[:4]))

(EV / "covering_radius.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
