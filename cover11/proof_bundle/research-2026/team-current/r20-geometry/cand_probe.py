"""Candidate probe: local sector-2 data of the CERTIFIED genuine cover, evaluated in the
same frozen-dual relaxation as the flat patch.

Why this matters: the flat certificates prove  const + sum22 + J_flat < pi  on the flat
slice (alpha_2 = pi).  Any "domain-preserving monotone deformation to the flat slice"
(domination) would extend that to the non-flat domain.  But the certified cover exists at
allowance R* in (.379,.37999) and the dual inequality reads
    pi = area <= const + sum22(x*) + J(x*)
with sum22(x*) <= sum22_sup, hence  J(x*) >= pi - const - sum22_sup.
If the flat program completes (J_flat < pi - const - sum22_sup) then domination is FALSE.

This script computes J(x*) from the certified integer centers (n11/upper/certified_object.json).
Inputs are read-only.
"""
import json, io, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
PI, R = L.PI, L.R

obj = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
scale = 10 ** int(obj["decimals"])
centers = np.array([[int(a), int(b)] for a, b in obj["centers_scaled_1e17"]], dtype=float) / scale
print("centers (x,y), |c|, arg(deg):")
for i, c in enumerate(centers):
    print("  %2d  %+.17f %+.17f   |c|=%.15f  arg=%8.3f" % (i, c[0], c[1], np.hypot(*c), math.degrees(math.atan2(c[1], c[0]))))
print("certified interval:", obj["certified_interval"]["lo"], obj["certified_interval"]["hi"])
print("argmax_pair:", obj["argmax_pair"])

n = len(centers)
r_lo = float(obj["certified_interval"]["lo"])
r_hi = float(obj["certified_interval"]["hi"])


def dist2(i, th):
    return (math.cos(th) - centers[i][0]) ** 2 + (math.sin(th) - centers[i][1]) ** 2


def owner(th):
    d = [dist2(i, th) for i in range(n)]
    return int(np.argmin(d)), min(d)


# ---------- nearest-owner partition of the unit circle --------------------------------
NS = 1 << 19
ths = np.linspace(0.0, 2 * math.pi, NS, endpoint=False)
own = np.empty(NS, dtype=int)
worst = 0.0
for k, th in enumerate(ths):
    i, d = owner(th)
    own[k] = i
    worst = max(worst, d)
print("sampled max nearest-distance^2 =", worst, " -> radius %.17f" % math.sqrt(worst))

# runs
runs = []
start = 0
for k in range(1, NS + 1):
    if k == NS or own[k % NS] != own[start]:
        runs.append((own[start], start, k))  # [start,k)
        start = k
# merge wraparound
if runs and runs[0][0] == runs[-1][0]:
    i, s0, e0 = runs.pop(0)
    i2, s1, e1 = runs[-1]
    runs[-1] = (i2, s1, e1 + NS)
print("\narc runs (owner, width deg, mean nearest radius):")
arc = []
for (i, s0, e0) in runs:
    w = (e0 - s0) * 2 * math.pi / NS
    mid = (s0 + e0) / 2 * 2 * math.pi / NS
    arc.append(dict(i=i, s=s0, e=e0, w=w, mid=mid, rad=math.sqrt(dist2(i, mid))))
    print("  owner %2d  w=%9.5f deg  mid=%8.3f deg  ownrad=%.17f" % (i, math.degrees(w), math.degrees(mid), math.sqrt(dist2(i, mid))))
owners_used = sorted(set(a["i"] for a in arc))
print("owners used:", owners_used, " #arcs:", len(arc))

# ---------- switch points (refine by bisection for each pair of neighbours) -----------
def switch(theta_a, theta_b):
    """bisect the tie between the owners at the two ends of an angular interval"""
    fa = lambda t: dist2(own[int((t % (2 * math.pi)) / (2 * math.pi) * NS)], t)
    ia = own[int((theta_a % (2 * math.pi)) / (2 * math.pi) * NS)]
    ib = own[int((theta_b % (2 * math.pi)) / (2 * math.pi) * NS)]
    lo, hi = theta_a, theta_b
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if dist2(ia, mid) - dist2(ib, mid) <= 0:
            lo = mid
        else:
            hi = mid
    t = 0.5 * (lo + hi)
    return (ia, ib, t)


sw = []
for k, a in enumerate(arc):
    b = arc[(k + 1) % len(arc)]
    ta = (a["e"] - 0.5) * 2 * math.pi / NS
    tb = (b["s"] + 0.5) * 2 * math.pi / NS
    ia, ib, t = switch(ta, tb)
    sw.append(dict(pair=(ia, ib), theta=t, P=(math.cos(t), math.sin(t)),
                   rad=math.sqrt(dist2(ia, t))))
print("\nswitches (pair, theta deg, common radius):")
for s in sw:
    print("   %s  theta=%8.3f deg  rad=%.17f" % (str(s["pair"]), math.degrees(s["theta"]), s["rad"]))

# ---------- which centres are hubs ---------------------------------------------------
own_set = set(owners_used)
hubs = [i for i in range(n) if i not in own_set]
print("\nhubs (no boundary arc):", hubs, " norms:", [np.hypot(*centers[i]) for i in hubs])
ring = owners_used

# adjacency of rings via shared switches
adj = {i: set() for i in ring}
for s in sw:
    a, b = s["pair"]
    if a in adj and b in adj:
        adj[a].add(b)
        adj[b].add(a)
print("\nring-adjacency (shared switch):")
for i in ring:
    print("  ring %2d -> %s   |c|=%.15f" % (i, sorted(adj[i]), np.hypot(*centers[i])))

# ---------- identify the A-chain -----------------------------------------------------
# hubs 9,10 in the abstract graph; rings 0 and 4 are adjacent to BOTH hubs.
# In the data: a ring is "hub-adjacent" if the hub centre is among the 3 nearest
# Delaunay-ish neighbours on the boundary side; instead use the geometric test:
# ring i is adjacent to hub h if the segment c_i-h is a Delaunay edge of the centre set.
from scipy.spatial import Delaunay

tri = Delaunay(centers)
edges = set()
for simplex in tri.simplices:
    for a in range(3):
        for b in range(a + 1, 3):
            e = tuple(sorted((int(simplex[a]), int(simplex[b]))))
            edges.add(e)
print("\nDelaunay edges:", sorted(edges))
common = [i for i in ring if all(tuple(sorted((i, h))) in edges for h in hubs)]
print("rings adjacent (Delaunay) to BOTH hubs:", common)
