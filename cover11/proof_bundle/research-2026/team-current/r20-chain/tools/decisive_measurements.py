"""r20-chain: decisive measurements at the certified candidate.

(1) Every Voronoi-vertex covering constraint rho_v <= R (is it tight?).
(2) Ring angular spans: for each hub H and consecutive pair (i,i+1), the ACTUAL angle
    theta_H(i,i+1) at H (always in (0,2pi)) and the hub's nine-turn sum (must be 2pi).
(3) The q0(6,7) exclusion budget: which constraints are saturated at the candidate.
(4) Chain capacity with the CORRECT per-sector factors:
    each edge i is coupled to BOTH hubs; the edge's total angular budget in the dual is
        min over hubs H visible on the edge of  (s_i^H + s_j^H),
    and the total must be >= 2pi because the ring turns once around EACH hub.
"""
import json
from pathlib import Path
from mpmath import mp, mpf, sqrt, cos, sin, acos, atan2, pi, nstr

mp.dps = 40
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
faces = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6), (0, 2, 6),
         (1, 2, 8), (1, 2, 7), (0, 3, 10), (0, 4, 9)]

P("R =", nstr(R, 30))
P("\n=== (1) covering constraints at every Voronoi vertex ===")
vtxs = []
for f in faces:
    a, b, c = (C[i] for i in f)
    d = 2 * crs(sub(b, a), sub(c, a))
    ax, ay = a; bx, by = b; cx, cy = c
    ux = dot(sub(b, a), sub(b, a)); vx = dot(sub(c, a), sub(c, a))
    ox = (ux * (cy - ay) - vx * (by - ay)) / d + ax
    oy = (vx * (bx - ax) - ux * (cx - ax)) / d + ay
    O = (ox, oy); rho = dd(O, a)
    vtxs.append((f, O, rho))
    P(f"   {str(f):>12s}  rho={nstr(rho,20)}  R-rho={nstr(R-rho,6):>12s}  |O|={nstr(dd(O,(0,0)),6)}"
      f"  {'TIGHT' if R-rho < mpf('1e-14') else ''}")

P("\n=== (2) ring turn sums at the candidate (must be exactly 2pi each) ===")
ring_ids = [1, 3, 4, 5, 6, 7, 8, 9, 10]
pol = sorted(ring_ids, key=lambda i: atan2(C[i][1], C[i][0]))
P("   polar order about origin:", pol)
for H, nm in ((HA, "A=0"), (HB, "B=2")):
    sp = []
    for k in range(9):
        i, j = pol[k], pol[(k + 1) % 9]
        v1, v2 = sub(C[i], C[H]), sub(C[j], C[H])
        t = atan2(crs(v1, v2), dot(v1, v2))       # signed, in (-pi,pi)
        sp.append(t)
    P(f"   hub {nm}: signed turns (rad):")
    P("      " + " ".join(nstr(t, 8) for t in sp))
    P(f"      sum of signed turns = {nstr(sum(sp),20)}  (target 2pi = {nstr(2*pi,20)})"
      f"   difference = {nstr(sum(sp)-2*pi,6)}")

P("\n=== (3) per-edge two-hub budget and its min ===")
P("   edge      d(i,j)   a_i=sA_i+sA_j  b_i=sB_i+sB_j   min(a,b)    theta_i(actual, both hubs)")
tot_min = mpf(0); tot_th = mpf(0)
rows = []
for k in range(9):
    i, j = pol[k], pol[(k + 1) % 9]
    dA1, dA2 = dd(C[HA], C[i]), dd(C[HA], C[j])
    dB1, dB2 = dd(C[HB], C[i]), dd(C[HB], C[j])
    def s(d): return acos(min(mpf(1), d / (2 * R))) if d <= 2 * R else None
    sA1, sA2, sB1, sB2 = s(dA1), s(dA2), s(dB1), s(dB2)
    a = (sA1 + sA2) if (sA1 is not None and sA2 is not None) else None
    b = (sB1 + sB2) if (sB1 is not None and sB2 is not None) else None
    m = min(a, b) if (a is not None and b is not None) else (a if a is not None else b)
    thA = ang(sub(C[i], C[HA]), sub(C[j], C[HA]))
    thB = ang(sub(C[i], C[HB]), sub(C[j], C[HB]))
    th = min(thA, thB)
    tot_min += m if m is not None else mpf(0); tot_th += th
    rows.append((i, j, a, b, m, thA, thB))
    P(f"   {i:>2d}-{j:<2d}  {nstr(dd(C[i],C[j]),8)}   {('   ----  ' if a is None else nstr(a,10))}"
      f"   {('   ----  ' if b is None else nstr(b,10))}   {nstr(m,10)}   {nstr(thA,8)} / {nstr(thB,8)}")
P(f"   sum of per-edge min budgets = {nstr(tot_min,18)}   minus 2pi = {nstr(tot_min-2*pi,8)}")
P(f"   sum of per-edge min actual angles = {nstr(tot_th,18)}")

P("\n=== (4) 'cap' arithmetic: which face is where ===")
P("   For each ordered pair (hub, ring edge) print (face exists?) by testing the")
P("   necessary condition  face circumradius <= R.")
for H, nm in ((HA, "A"), (HB, "B")):
    out = []
    for k in range(9):
        i, j = pol[k], pol[(k + 1) % 9]
        a, b, c = C[H], C[i], C[j]
        K = abs(crs(sub(b, a), sub(c, a))) / 2
        circ = dd(a, b) * dd(b, c) * dd(c, a) / (4 * K) if K > 0 else mpf(10)
        out.append('Y' if circ <= R else ('.' if circ < 10 else '#'))
    P(f"   hub {nm}: legal faces over the 9 ring edges: {''.join(out)}")
# and the ring-edge presence in the actual Delaunay triangulation
deen = {tuple(sorted(f)) for f in faces}
P("   actual Delaunay faces (as edge sets) with their hub:")
for f in sorted(faces):
    P("      ", f)

(OUT / "decisive_measurements.txt").write_text("\n".join(log) + "\n")
P("\nwrote", OUT / "decisive_measurements.txt")
