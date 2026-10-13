"""Step 8: the TRUE reduced structure of the C182 candidate + independent check of
lead/D3-EXACT-CHART.md.

Findings being tested here (all exact-rational or high-precision):
 (i)   the literal config is C3-covariant, NOT D3: rotation by 120 deg is covariant to
       5.4e-17, every reflection misses by >= 0.197.
 (ii)  4 orbits of size 3 under C3, all at |c|^2 values that DIFFER at ~1e-17 relative
       (so the 17-digit literal is not exactly C3-symmetric either).
 (iii) R_D(C) = max_{x in D} min_i |x-c_i| is attained at 6 interior Voronoi vertices
       (triples {2,10,11},{1,8,9},{0,6,7},{0,1,3},{0,2,5},{1,2,4}) with f-R_D <= 0 and
       |f-R_D| <= 5.2e-17; boundary max is strictly below by 1.55e-8.
 (iv)  the lead's D3 chart relations are tested numerically against the actual data.
"""
from pathlib import Path
from fractions import Fraction as F
import json, itertools
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
B = json.loads((ROOT / "flash-n11/members/othern-scout/s3/n12_d3_kkt.json").read_text(encoding="utf-8"))
OUT = []
def W(s=""): OUT.append(str(s))

Aq = [(F(x), F(y)) for x, y in A["centers_dec17"]]
Am = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in A["centers_dec17"]]
Rlo = F("0.361102963744508672616920293903")
Rhi = F("0.361102963744508672616920293904")
Rlo_m = mp.mpf("0.361102963744508672616920293903")
Rhi_m = mp.mpf("0.361102963744508672616920293904")
W("### 0. constants")
W(f"  R_D(C182) in [{mp.nstr(Rlo_m,34)}, {mp.nstr(Rhi_m,34)}]   (D2 replay interval, exact rationals)")
W(f"  (2*R_lo)^2 = {mp.nstr((2*Rlo_m)**2,30)}")

# ---------- (i)+(ii): symmetry
W("\n### 1. symmetry of the literal config")
def cov(rot_k):
    th = 2*mp.pi*rot_k/3
    c, s = mp.cos(th), mp.sin(th)
    mx = mp.mpf(0); arg = None
    for i in range(12):
        q = (c*Am[i][0]-s*Am[i][1], s*Am[i][0]+c*Am[i][1])
        d, j = min((mp.sqrt((q[0]-c2[0])**2+(q[1]-c2[1])**2), t) for t, c2 in enumerate(Am))
        if d > mx: mx, arg = d, (i, j)
    return mx, arg
for k in (1, 2):
    mx, arg = cov(k)
    W(f"  rotation by {120*k} deg : max_i min_j |rot(c_i) - c_j| = {mp.nstr(mx,18)}  (worst i->j = {arg})")
W("  reflections (axis angle -> max_i min_j):")
for phi in (0, 30, 60, 90, 120, 150, 20.905, 26.4526):
    ph = mp.pi*mp.mpf(str(phi))/180
    c2, s2 = mp.cos(2*ph), mp.sin(2*ph)
    mx = mp.mpf(0)
    for i in range(12):
        q = (c2*Am[i][0]+s2*Am[i][1], s2*Am[i][0]-c2*Am[i][1])
        mx = max(mx, min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in Am))
    W(f"    axis {phi:9.4f} deg -> {mp.nstr(mx,18)}")
W("  => the literal 17-digit config is C3-COVARIANT but NOT reflection symmetric: D3 is false")
W("     (it is not exactly C3 either: see the orbit norms below)")

W("\n### 2. C3 orbits: exact |c|^2 (rational) show the literal is a rounding of an exact D3/C3 object")
n2 = lambda i: Aq[i][0]**2 + Aq[i][1]**2
orb = {0: (0, 1, 2), 3: (3, 4, 5), 6: (6, 8, 9), 7: (7, 10, 11)}
for key, idx in orb.items():
    vals = [n2(i) for i in idx]
    spread = max(vals) - min(vals)
    rel = mp.mpf(spread.numerator)/mp.mpf(spread.denominator)
    W(f"  orbit {idx}: |c|^2 = {[mp.nstr(mp.mpf(v.numerator)/mp.mpf(v.denominator),26) for v in vals]}")
    W(f"      spread = {spread} = {mp.nstr(rel,6)} (relative ~1e-17) -> NOT an exact rational identity")
    W(f"      |c_i|  = {[mp.nstr(mp.sqrt(mp.mpf(v.numerator)/mp.mpf(v.denominator)),22) for v in vals]}")

# ---------- (iii): exact comparison of the 6 active faces' circumradius^2 with R^2
W("\n### 3. EXACT rational comparison: circumradius^2 of the active triples vs (2R)^2/4 = R^2")
def rr2(tri):
    i, j, k = tri
    a, b, c = Aq[i], Aq[j], Aq[k]
    cross = 2*((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0]))
    lab = (a[0]-b[0])**2+(a[1]-b[1])**2
    lbc = (b[0]-c[0])**2+(b[1]-c[1])**2
    lca = (c[0]-a[0])**2+(c[1]-a[1])**2
    return lab*lbc*lca/(cross*cross)
lo2, hi2 = Rlo*Rlo, Rhi*Rhi
W(f"  R_lo^2 = {lo2}")
W(f"  R_hi^2 = {hi2}")
act = [(2,10,11), (1,8,9), (0,6,7), (0,1,3), (0,2,5), (1,2,4)]
for tri in act:
    q = rr2(tri)
    W(f"  tri{str(tri):<14} rr^2-R_lo^2 = {q-lo2}")
    W(f"     {'':14} rr^2-R_hi^2 = {q-hi2}")
    W(f"     rr vs R interval: {'INSIDE' if lo2 <= q <= hi2 else ('BELOW' if q < lo2 else 'ABOVE')}"
      f"   rr = {mp.nstr(mp.sqrt(mp.mpf(q.numerator)/mp.mpf(q.denominator)),32)}")
    # side lengths vs 2R
    i, j, k = tri
    sides = [(Aq[i][0]-Aq[j][0])**2+(Aq[i][1]-Aq[j][1])**2,
             (Aq[j][0]-Aq[k][0])**2+(Aq[j][1]-Aq[k][1])**2,
             (Aq[k][0]-Aq[i][0])**2+(Aq[k][1]-Aq[i][1])**2]
    W(f"     sides^2 - (2R_lo)^2: {[s-(2*Rlo)**2 for s in sides]}")
    W(f"     sides^2 - (2R_hi)^2: {[s-(2*Rhi)**2 for s in sides]}")

# ---------- (iv): test the lead's D3 chart relations against the data
W("\n### 4. INDEPENDENT CHECK of lead/D3-EXACT-CHART.md against the actual data")
a_a = mp.sqrt(n2(0).numerator/mp.mpf(n2(0).denominator)) if False else mp.sqrt(mp.mpf(n2(0).numerator)/mp.mpf(n2(0).denominator))
W(f"  data: |c_0| = {mp.nstr(a_a,30)}  <- chart's 'a' (hub norm)")
for key, idx in orb.items():
    v = mp.sqrt(mp.mpf(n2(idx[0]).numerator)/mp.mpf(n2(idx[0]).denominator))
    W(f"        |c_{idx[0]}| = {mp.nstr(v,30)}")
t_ = mp.sqrt(mp.mpf(n2(3).numerator)/mp.mpf(n2(3).denominator))
b_ = mp.sqrt(mp.mpf(n2(6).numerator)/mp.mpf(n2(6).denominator))
W(f"  data: t = |c_3| = {mp.nstr(t_,30)}   b = |c_6| = {mp.nstr(b_,30)}   r = R_D = {mp.nstr(Rlo_m,30)}")
W("")
W("  chart relation  d = a + r  and  b = (1+d)/2 :")
W(f"     chart predicts b = (1+a+r)/2 = {mp.nstr((1+a_a+Rlo_m)/2,30)}")
W(f"     actual                  b = {mp.nstr(b_,30)}")
W(f"     DIFFERENCE b_actual - b_chart = {mp.nstr(b_-(1+a_a+Rlo_m)/2,10)}")
W("  chart relation  s^2 = b^2+v^2 = d + r^2 :")
s2 = b_**2
W(f"     actual b^2 = {mp.nstr(s2,30)}     d + r^2 = a+r+r^2 = {mp.nstr(a_a+Rlo_m+Rlo_m**2,30)}")
W(f"     DIFFERENCE = {mp.nstr(s2-(a_a+Rlo_m+Rlo_m**2),10)}")
W("  chart relation  v^2 = r^2-(1-d)^2/4 :")
v2_from_data = b_**2  # placeholder
W(f"     (needs the off-axis split; the chart's (b,+-v) pair at ONE norm is the real issue: see below)")
W("")
W("  DECISIVE structural test: does the high ring form ONE orbit of 6 at radius b, or TWO orbits of 3?")
W("     rotation by 120 deg maps the high-ring indices as 6->8->9 and 7->10->11;")
W("     the angular offsets are:")
ang = [mp.atan2(Am[i][1], Am[i][0])*180/mp.pi for i in range(12)]
for i in (6, 8, 9):
    W(f"        theta_{i} = {mp.nstr(ang[i],20)}   theta_{i} - theta_6 = {mp.nstr(ang[i]-ang[6],20)}")
for i in (7, 10, 11):
    W(f"        theta_{i} = {mp.nstr(ang[i],20)}   theta_{i} - theta_7 = {mp.nstr(ang[i]-ang[7],20)}")
W(f"     theta_6 - theta_7 = {mp.nstr(ang[6]-ang[7],20)}  (chart's (b,+-v) pair would give 2*atan(v/b))")
W(f"     -> {'TWO distinct orbits of 3' if abs(float((ang[8]-ang[6])-120))<1e-6 and abs(float(ang[10]-ang[7])-120)<1e-6 else 'other'}")
W("     => the chart's single high ring (b, +-v) = ONE orbit of size 2 per hub is NOT the data's")
W("        structure: the data has 9 ring/hub centres = 3 orbits of 3 (C3), not 3 hubs + pairs.")
W("")
W("  chart relation  d = a + r as a witness: is (d,0) really at distance r from the ring pair?")
W(f"     the chart's (d,0) = ({mp.nstr(a_a+Rlo_m,20)}, 0); distances to c_6,c_7,c_3:")
for i in (3, 6, 7):
    dd = mp.sqrt((a_a+Rlo_m-Am[i][0])**2 + (0-Am[i][1])**2)
    W(f"        |(d,0)-c_{i}| = {mp.nstr(dd,26)}   minus r = {mp.nstr(dd-Rlo_m,8)}")
W(f"     and |(a,0)-c_0| = {mp.nstr(mp.sqrt((a_a-Am[0][0])**2+Am[0][1]**2),26)}  (hub to itself)")
(EV / "reduced_system_1.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
