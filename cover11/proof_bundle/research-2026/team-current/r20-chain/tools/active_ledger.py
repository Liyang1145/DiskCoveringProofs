"""r20-chain: active constraint ledger + chain capacity bound at the certified candidate.

Part 1  Voronoi/nearest-site ledger: which Voronoi vertices are tight (radius == R).
Part 2  Alternating chain ledger: for every ring edge (i,j), the two faces (A,i,j), (B,i,j)
        and their slack to R; the constraint theta_ij(H) <= s_i^H + s_j^H; the deficit
        difference Delta = |s_i - s_j|; and the hub angle.
Part 3  Chain capacity (the object of direction C): for a hub H and a maximal run of
        consecutive ring vertices whose faces are all legal, compute
            Gamma = Sigma theta      (turn budget = spoke-discrepancy bound)
            Sigma_theta_max = min( k*pi/2, (k-1)*pi/2 + s_0 + s_k )
            Sigma_theta_min = |s_k - s_0| + (hub-angle accounting)
        and compare with the realized value, i.e. how much room the chain leaves.
"""
import json
from pathlib import Path
from mpmath import mp, mpf, sqrt, cos, sin, acos, asin, atan2, pi, nstr, atan

mp.dps = 50
HERE = Path(__file__).resolve().parent
OBJ = HERE.parent.parent / "cline2-sharp-fan" / "out" / "certified_object_copy.json"
OUT = HERE.parent / "out"
log = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); log.append(s)

obj = json.loads(OBJ.read_text(encoding="utf-8"))
sc = mpf(10) ** 17
C = [(mpf(int(a)) / sc, mpf(int(b)) / sc) for a, b in obj["centers_scaled_1e17"]]
R = mpf(obj["certified_interval"]["lo"])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def crs(a, b): return a[0] * b[1] - a[1] * b[0]
def dd(a, b): return sqrt(dot(sub(a, b), sub(a, b)))
def ang(a, b):
    c = dot(a, b) / (sqrt(dot(a, a)) * sqrt(dot(b, b)))
    return acos(max(mpf(-1), min(mpf(1), c)))

HA, HB = 0, 2
RING = [1, 3, 4, 5, 6, 7, 8, 9, 10]
def circR(tri):
    a, b, c = (C[i] for i in tri)
    K = abs(crs(sub(b, a), sub(c, a))) / 2
    if K == 0: return None
    return dd(a, b) * dd(b, c) * dd(c, a) / (4 * K)

P("R =", nstr(R, 30))
P("\n================ PART 1: Voronoi ledger ================")
# Voronoi vertices: triples whose circumcircle is empty (computed previously -> the 11 faces)
faces = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
         (1, 2, 8), (1, 2, 7), (0, 3, 10), (0, 4, 9)]
tight = []
for f in faces:
    a, b, c = (C[i] for i in f)
    d = 2 * crs(sub(b, a), sub(c, a))
    ax, ay = a; bx, by = b; cx, cy = c
    ux = dot(sub(b, a), sub(b, a)); vx = dot(sub(c, a), sub(c, a))
    ox = (ux * (cy - ay) - vx * (by - ay)) / d + ax
    oy = (vx * (bx - ax) - ux * (cx - ax)) / d + ay
    O = (ox, oy)
    rho = dd(O, a)
    nearest = [i for i in range(11) if dd(O, C[i]) < rho + mpf('1e-25')]
    tag = "TIGHT" if rho >= R - mpf('1e-12') else "     "
    P(f"  face {str(f):>12s}  vtx |O|={nstr(dd(O,(0,0)),8):>10s}  radius={nstr(rho,20)}  R-rho={nstr(R-rho,6):>10s} {tag}  nearest={nearest}")

P("\n================ PART 2: alternating chain ledger ================")
def deficit(H, i):
    return acos(min(mpf(1), dd(C[H], C[i]) / (2 * R)))
sA = {i: deficit(HA, i) for i in RING}
sB = {i: deficit(HB, i) for i in RING}
P("  ring  |A-c|        s_A        |B-c|        s_B        d(i,j)     circR_A      circR_B")
# ring edges in polar order (counterclockwise about origin)
order = [4, 9, 10, 3, 5, 7, 1, 8, 6]
edges = [(order[k], order[(k + 1) % 9]) for k in range(9)]
for (i, j) in edges:
    cA = circR((HA, i, j)); cB = circR((HB, i, j))
    P(f"  {i:>2d}-{j:<2d} | {nstr(dd(C[HA],C[i]),10)} {nstr(sA[i],10)} | {nstr(dd(C[HB],C[i]),10)} {nstr(sB[i],10)} |"
      f" {nstr(dd(C[i],C[j]),10)} | {nstr(cA,16)} (s={nstr(R-cA,7)}) | {nstr(cB,16)} (s={nstr(R-cB,7)})")
P("\n  per-edge constraint ledger: theta_ij(H) <= s_i^H + s_j^H   [the only metric constraint")
P("  needed for face (H,i,j) to have circumradius <= R]")
for (i, j) in edges:
    for H, s in ((HA, sA), (HB, sB)):
        v1, v2 = sub(C[i], C[H]), sub(C[j], C[H])
        th = ang(v1, v2)
        hi = s[i] + s[j]; lo = abs(s[i] - s[j])
        c = circR((H, i, j))
        P(f"   edge {i:>2d}-{j:<2d} hub {H}: theta={nstr(th,12)}  lo={nstr(lo,12)} hi={nstr(hi,12)}"
          f"  slack_hi={nstr(hi-th,6):>12s} slack_lo={nstr(th-lo,6):>12s}  circR={nstr(c,14)} {'LEGAL' if c<=R else 'ILLEGAL'}")

P("\n  hub-angle ledger: sum of theta over ALL nine edges around each hub")
for H, s in ((HA, sA), (HB, sB)):
    ths = []
    for (i, j) in edges:
        ths.append(ang(sub(C[i], C[H]), sub(C[j], C[H])))
    P(f"   hub {H}: sum theta = {nstr(sum(ths),18)}   (2pi = {nstr(2*pi,18)})  defect = {nstr(2*pi-sum(ths),10)}")
    P(f"           max possible = 9*pi/2 = {nstr(9*pi/2,10)}")

P("\n================ PART 3: chain capacity ================")
P("  For a hub H and an ordered chain c_0..c_k of consecutive ring vertices with all")
P("  faces legal, the *turn budget* of the chain is Gamma = sum_{i<k} theta_i, and the")
P("  metric constraint set is exactly  { |s_i - s_j| <= theta_ij <= s_i + s_j }.")
P("  Derived exact bounds:")
P("    Gamma <= min( k*pi/2 , (k-1)*pi/2 + s_0 + s_k )      [telescoping via theta<=s_i+s_j]")
P("    Gamma >= |s_k - s_0|                                  [theta >= |s_i - s_j|]")
P("  REALIZED chains at the candidate (maximal runs of legal faces):")
# maximal legal runs: walk the ring cycle in polar order, keep edges where at least one hub's face is legal
for label, H, s in (("A", HA, sA), ("B", HB, sB)):
    legal = []
    for (i, j) in edges:
        c = circR((H, i, j))
        legal.append(c <= R)
    P(f"   hub {label} legal-face mask (9 edges in polar order): {['1' if x else '0' for x in legal]}")
    # find maximal runs of consecutive legal edges (cyclic)
    runs = []
    if all(legal):
        runs = [(0, 8)]
    else:
        start = legal.index(False)
        k = 0
        cur = []
        idx = (start) % 9
        for t in range(9):
            e = (start + 1 + t) % 9
            if legal[e]:
                cur.append(e)
            else:
                if cur: runs.append((cur[0], cur[-1])); cur = []
        if cur: runs.append((cur[0], cur[-1]))
    for (a, b) in runs:
        chain = [edges[a][0]]
        for t in range(a, b + 1):
            chain.append(edges[t][1])
        k = len(chain) - 1
        th = [ang(sub(C[chain[t]], C[H]), sub(C[chain[t + 1]], C[H])) for t in range(k)]
        G = sum(th)
        s0, sk = s[chain[0]], s[chain[-1]]
        ub = min(k * pi / 2, (k - 1) * pi / 2 + s0 + sk)
        P(f"     chain {chain} (k={k}): Gamma={nstr(G,16)}  ub={nstr(ub,16)}  slack={nstr(ub-G,10)}"
          f"   lower |s_k-s_0| = {nstr(abs(sk-s0),10)}")
        # capacity note: the *area* of the chain's faces
        area = 0
        for t in range(k):
            rho1, rho2 = dd(C[H], C[chain[t]]), dd(C[H], C[chain[t + 1]])
            area += rho1 * rho2 * sin(th[t]) / 2
        P(f"        face areas sum = {nstr(area,16)}   (each <= 2R^2 * cos s_i cos s_j sin(s_i+s_j))")

(OUT / "active_ledger.txt").write_text("\n".join(log) + "\n")
P("\nwrote", OUT / "active_ledger.txt")
