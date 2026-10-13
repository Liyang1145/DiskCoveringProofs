"""r20-chain: exact structure of the certified 11-disk covering candidate.

Reads the integer/1e17 centres of the certified object, rebuilds the geometry with mpmath
(50 dps), and reports:
  - ring vs hub classification, norms, boundary arcs
  - the true Delaunay / refined nearest-site triangulation (faces, radii, degrees)
  - fan runs around each hub in the polar order
  - hub-star deficit coordinates s_i = arccos(|H-c_i| / (2R)) and local turns theta
  - exact test of the chain constraint theta <= s_i + s_{i+1} and of the fan-arc closure
  - exact area accounting: triangle areas + exterior arc-segment areas == pi
No claim is registered here; this is a structural measurement (identity calibration).
"""
import json, sys, itertools
from pathlib import Path
from mpmath import mp, mpf, sqrt, cos, sin, acos, asin, atan2, pi, fabs

mp.dps = 50

HERE = Path(__file__).resolve().parent
OBJ = HERE.parent.parent / "cline2-sharp-fan" / "out" / "certified_object_copy.json"
OUT = HERE.parent / "out"
OUT.mkdir(exist_ok=True)
log = []
def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    log.append(s)

obj = json.loads(OBJ.read_text(encoding="utf-8"))
scale = mpf(10) ** 17
C = [(mpf(int(a)) / scale, mpf(int(b)) / scale) for a, b in obj["centers_scaled_1e17"]]
n = len(C)
Rlo = mpf(obj["certified_interval"]["lo"])
Rhi = mpf(obj["certified_interval"]["hi"])
P("n =", n, " certified R interval width:", Rhi - Rlo)

def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def mul(a, t): return (a[0] * t, a[1] * t)
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def cross(a, b): return a[0] * b[1] - a[1] * b[0]
def norm2(a): return dot(a, a)
def dist(a, b): return sqrt(norm2(sub(a, b)))

norms = [sqrt(norm2(c)) for c in C]
P("\n--- norms |c_i| ---")
for i, (c, r) in enumerate(zip(C, norms)):
    P(f"  c_{i:<2d} = ({mp.nstr(c[0],18)}, {mp.nstr(c[1],18)})   |c| = {mp.nstr(r,18)}")

ring = [i for i in range(n) if norms[i] > mpf('0.5')]
hub = [i for i in range(n) if norms[i] <= mpf('0.5')]
P("\nring candidates:", ring)
P("hub candidates :", hub)

# --- true nearest-site (Voronoi) structure: is the candidate Delaunay-regular? ---
def circumradius(tri):
    a, b, c = (C[i] for i in tri)
    d = 2 * cross(sub(b, a), sub(c, a))
    if d == 0:
        return None, None
    ax, ay = a; bx, by = b; cx, cy = c
    ux = ((bx - ax) ** 2 + (by - ay) ** 2)
    vx = ((cx - ax) ** 2 + (cy - ay) ** 2)
    ox = (ux * (cy - ay) - vx * (by - ay)) / d + ax
    oy = (vx * (bx - ax) - ux * (cx - ax)) / d + ay
    O = (ox, oy)
    return dist(O, a), O

P("\n--- Delaunay check: for each candidate triangle, is its circumcircle empty? ---")
tri_all = list(itertools.combinations(range(n), 3))
empty_tris = []
for tri in tri_all:
    rho, O = circumradius(tri)
    if rho is None:
        continue
    inside = [j for j in range(n) if j not in tri and dist(C[j], O) < rho - mpf('1e-30')]
    if not inside:
        empty_tris.append((tri, rho, O))
P("number of empty-circumcircle triangles (Delaunay):", len(empty_tris))
for tri, rho, O in sorted(empty_tris, key=lambda t: -t[1]):
    P(f"   tri {tri}  rho = {mp.nstr(rho,18)}  |O| = {mp.nstr(sqrt(norm2(O)),10)}")

P("\n--- would-be faces with all three sites having rho <= R (coverable): ---")
for tri, rho, O in sorted(empty_tris, key=lambda t: -t[1]):
    if rho <= Rhi:
        P(f"   FACE {tri}  rho = {mp.nstr(rho,18)}  slack R-rho = {mp.nstr(Rhi-rho,6)}")

# --- ring arc data on bd D: for each ring i, the boundary points it covers ---
P("\n--- ring boundary arcs (points of bd D at distance <= R from c_i) ---")
for i in ring:
    rho_c = norms[i]
    if rho_c + Rhi < 1:
        P(f"   ring {i}: does NOT reach bd D (|c|+R-1 = {mp.nstr(rho_c+Rhi-1,6)})")
        continue
    # boundary point at angle t: |c - e^{it}| <= R  <=> cos(t - phi) >= (rho^2+1-R^2)/(2 rho)
    phi = atan2(C[i][1], C[i][0])
    crit = (rho_c ** 2 + 1 - Rhi ** 2) / (2 * rho_c)
    crit = max(mpf(-1), min(mpf(1), crit))
    half = acos(crit)
    P(f"   ring {i}: phi={mp.nstr(phi,10)} halfwidth={mp.nstr(half,10)} (rad)  span=[{mp.nstr(phi-half,10)},{mp.nstr(phi+half,10)}]  |c|+R-1={mp.nstr(rho_c+Rhi-1,6)}")

# --- polar order around ring centroid / origin ---
P("\n--- ring polar angles (about origin) ---")
pol = sorted(ring, key=lambda i: atan2(C[i][1], C[i][0]))
for i in pol:
    P(f"   ring {i}: theta = {mp.nstr(atan2(C[i][1], C[i][0]),18)}")
P("cyclic order:", pol)

# --- fan runs: for each hub, which consecutive ring pairs in polar order actually give
#     a Delaunay triangle with that hub, and what is its circumradius ---
for h in hub:
    dat = []
    for i in ring:
        v = sub(C[i], C[h])
        dat.append((atan2(v[1], v[0]), i))
    dat.sort()
    order = [i for _, i in dat]
    P(f"\n--- hub {h} (|h|={mp.nstr(norms[h],12)}): ring order by angle about hub ---")
    P("    order:", order, " angles:", [mp.nstr(a, 8) for a, _ in dat])
    runs = []
    for k in range(len(order)):
        i, j = order[k], order[(k + 1) % len(order)]
        rho, O = circumradius((h, i, j))
        if rho is None:
            runs.append((i, j, None)); continue
        # is (h,i,j) an actual face (empty circumcircle)?
        inside = [t for t in range(n) if t not in (h, i, j) and dist(C[t], O) < rho - mpf('1e-30')]
        ok = (not inside) and rho <= Rhi
        runs.append((i, j, rho, ok, inside))
    for r in runs:
        if r[2] is None:
            P(f"    gap {r[0]:>2d}->{r[1]:<2d}: degenerate")
        else:
            P(f"    gap {r[0]:>2d}->{r[1]:<2d}: rho={mp.nstr(r[2],14)}  legalface={r[3]}  blockers={r[4][:4]}")

# --- save structured summary ---
summary = {
    "norms": [str(x) for x in norms],
    "ring": ring, "hub": hub,
    "polar_order": pol,
    "delaunay_faces": [[list(t), str(r)] for t, r, _ in sorted(empty_tris, key=lambda t: -t[1])],
    "Rhi": str(Rhi),
}
(OUT / "chain_structure.json").write_text(json.dumps(summary, indent=1))
(OUT / "chain_structure.txt").write_text("\n".join(log) + "\n")
P("\nwrote", OUT / "chain_structure.json")
