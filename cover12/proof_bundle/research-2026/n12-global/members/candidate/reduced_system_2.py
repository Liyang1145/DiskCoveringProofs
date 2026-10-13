"""Step 9: TRUE reduced parameterization of the C182 candidate and its exact root system.

Verified structure (from exact_rational evidence in evidence/):
  * R_D(C) = max_{x in D} min_i |x-c_i| = covering radius.
  * The 12 centres form 4 orbits of 3 under the exact 120-degree rotation:
      hub  orbit  A = {0,1,2}   |c| = a ~ 0.2782416608744279   (VERIFIED: a = 1-2R exactly?)
      mid  orbit  B = {3,4,5}   |c| = t ~ 0.7691690191634051
      high orbit  C = {6,8,9}   |c| = b ~ 0.8773482632592399
      high orbit  D = {7,10,11} |c| = b' ~ 0.8773482632592399
    (the two high orbits differ in angular phase, not in norm; norms agree to 1e-16)
  * R_D is attained at 6 interior Voronoi vertices at 2 distinct radii
      |u| = 0.4080660554188965  (triples {0,1,3},{0,2,5},{1,2,4})
      |u| = 0.6393446246189366  (triples {0,6,7},{1,8,9},{2,10,11})
  * boundary max-min = 0.36110294823983297 = R_D - 1.55e-8  (slack)

This script (a) fits the exact relations, (b) writes the symbolic system, (c) ranks it.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
B = json.loads((ROOT / "flash-n11/members/othern-scout/s3/n12_d3_kkt.json").read_text(encoding="utf-8"))
OUT = []
def W(s=""): OUT.append(str(s))

Am = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in A["centers_dec17"]]
Rc = mp.mpf("0.361102963744508672616920293903")   # certified lower end of R_D interval
rad = [mp.sqrt(c[0]**2+c[1]**2) for c in Am]
ang = [mp.atan2(c[1], c[0]) for c in Am]

a, t, b6, b7 = rad[0], rad[3], rad[6], rad[7]
W("### 0. key relations (dps=60)")
W(f"  a = |c_0| = {mp.nstr(a,40)}")
W(f"  t = |c_3| = {mp.nstr(t,40)}")
W(f"  b = |c_6| = {mp.nstr(b6,40)}   b' = |c_7| = {mp.nstr(b7,40)}")
W(f"  R_D = {mp.nstr(Rc,40)}")
W("")
W("  TEST  a = 1 - 2 R_D :")
W(f"     1 - 2 R_D        = {mp.nstr(1-2*Rc,40)}")
W(f"     a                = {mp.nstr(a,40)}   difference = {mp.nstr(a-(1-2*Rc),8)}")
W("  TEST  a = (1-R_D)/2 :")
W(f"     (1-R_D)/2        = {mp.nstr((1-Rc)/2,40)}   difference = {mp.nstr(a-(1-Rc)/2,8)}")
W("  TEST  t = 1 - R_D/1.5 etc (search simple rational relations a,t,b vs R_D):")
for name, val in (("a", a), ("t", t), ("b", b6), ("b'", b7)):
    W(f"     {name}/R_D = {mp.nstr(val/Rc,30)}    {name} = {mp.nstr(val,30)}")
W("")
W("  angular layout after rotating so that c_0 is at angle phi_0 = 0:")
phi0 = ang[0]
W(f"     rotation offset phi_0 = {mp.nstr(phi0*180/mp.pi,30)} deg")
for i in range(12):
    d = (ang[i]-phi0)*180/mp.pi
    d = mp.fmod(d+360, 360)
    W(f"       c{i:2d}: rel_deg = {mp.nstr(d,22):>26}   |c| = {mp.nstr(rad[i],20)}")
W("  => hub {0,1,2} at 0,120,240 ; mid {3,4,5} at 60,180,300 ;")
W("     high {6,8,9} at ~20.891, 140.891, 260.891 ; high {7,10,11} at ~340.891, 100.891, 220.891")
h6 = mp.fmod((ang[6]-phi0)*180/mp.pi+360, 360)
h7 = mp.fmod((ang[7]-phi0)*180/mp.pi+360, 360)
W(f"     measured: c6 rel = {mp.nstr(h6,24)}, c7 rel = {mp.nstr(h7,24)}")
W(f"     DELTA = c6 - c7 - 0    = {mp.nstr(h6-h7,24)}")
W(f"     360 + h7 - h6          = {mp.nstr(360+h7-h6,24)}")
W(f"     compare 40.0 exactly? diff = {mp.nstr(h6-h7-40,10)}")
W(f"     compare 2*asin(?): h6-h7 in rad = {mp.nstr((h6-h7)*mp.pi/180,24)}")
W("")
W("### 1. hole geometry: the two hole radii")
W(f"  |u_2| (tri 0,6,7) = {mp.nstr(mp.sqrt((mp.mpf('-0.3798708762382397509751') if False else mp.mpf('0.6352945626594627541204'))**2+mp.mpf('0.0718496185407470676146')**2),30)}")
u2 = (mp.mpf('0.6352945626594627541204'), mp.mpf('0.0718496185407470676146'))
u3 = (mp.mpf('0.1630259052237826004624'), mp.mpf('0.3740861662920778312081'))
W(f"  |u_2| = {mp.nstr(mp.sqrt(u2[0]**2+u2[1]**2),30)}   arg_deg = {mp.nstr(mp.atan2(u2[1],u2[0])*180/mp.pi,20)}")
W(f"  |u_3| = {mp.nstr(mp.sqrt(u3[0]**2+u3[1]**2),30)}   arg_deg = {mp.nstr(mp.atan2(u3[1],u3[0])*180/mp.pi,20)}")
# exact-ish relations for the holes
W("  TEST |u_2| = d = a + R_D ?")
W(f"     a + R_D = {mp.nstr(a+Rc,30)}   |u_2| = {mp.nstr(mp.sqrt(u2[0]**2+u2[1]**2),30)}"
  f"   diff = {mp.nstr(mp.sqrt(u2[0]**2+u2[1]**2)-(a+Rc),8)}")
W("  TEST |u_3| = t - R_D ?")
W(f"     t - R_D = {mp.nstr(t-Rc,30)}   |u_3| = {mp.nstr(mp.sqrt(u3[0]**2+u3[1]**2),30)}"
  f"   diff = {mp.nstr(mp.sqrt(u3[0]**2+u3[1]**2)-(t-Rc),8)}")
W("  TEST |u_2|^2 = R_D^2 + b^2 - 2 R_D b cos(delta) for the hub angle")
# angle between u_2 and c_6
thu2 = mp.atan2(u2[1], u2[0])
dth2 = (thu2-ang[6])
W(f"     angle(u_2) - angle(c_6) = {mp.nstr(mp.fmod(dth2*180/mp.pi+360,360),24)} deg")
for i in (0, 6, 7):
    dd = mp.sqrt((u2[0]-Am[i][0])**2+(u2[1]-Am[i][1])**2)
    W(f"     |u_2 - c_{i}| = {mp.nstr(dd,30)}   (should equal R_D: diff={mp.nstr(dd-Rc,8)})")
for i in (0, 1, 3):
    dd = mp.sqrt((u3[0]-Am[i][0])**2+(u3[1]-Am[i][1])**2)
    W(f"     |u_3 - c_{i}| = {mp.nstr(dd,30)}   (should equal R_D: diff={mp.nstr(dd-Rc,8)})")
W("")
W("### 2. exact root system: what determines the configuration?")
W("  unknowns (7): R, rho_B, rho_C, rho_D(=rho_C by norm equality), alpha, beta, gamma")
W("  constraints from the 6 active Voronoi vertices:")
W("   (V1) tri{0,6,7}: hole on ray theta_0 (bisector of the two high orbits)")
W("   (V2) tri{0,1,3}: hole on the bisector of the hub pair, at distance R from c_3")
W("   (V3) the hole values equal R (both families)")
W("   (V4) boundary tiling: 9 arcs of the 9 nearest-owned centres tile S1")
W("   (V5) stationarity: R is a local min of the covering radius in this family")
W("")
W("### 3. direct numeric test of V2: the hole u_3 = circumcentre of (c_0,c_1,c_3)")
W(f"  at u_3: |u_3-c_0| = {mp.nstr(mp.sqrt((u3[0]-Am[0][0])**2+(u3[1]-Am[0][1])**2),30)}")
W(f"          |u_3-c_1| = {mp.nstr(mp.sqrt((u3[0]-Am[1][0])**2+(u3[1]-Am[1][1])**2),30)}")
W(f"          |u_3-c_3| = {mp.nstr(mp.sqrt((u3[0]-Am[3][0])**2+(u3[1]-Am[3][1])**2),30)}")
W(f"  so the triangle (c_0,c_1,c_3) has circumradius R_D: it is NOT degenerate (equilateral),")
W(f"  the 3 side lengths are:")
import itertools
for (i, j) in ((0,1),(1,3),(0,3)):
    d = mp.sqrt((Am[i][0]-Am[j][0])**2+(Am[i][1]-Am[j][1])**2)
    W(f"     |c_{i}-c_{j}| = {mp.nstr(d,30)}   d/(2R_D) = {mp.nstr(d/(2*Rc),30)}")
W("")
W("  The relevant INEQUALITY structure (what makes R_D tight):")
W("   * the 6 active triples have circumradius = R_D (equality, active)")
W("   * all other triples whose circumcentre lies in D have circumradius < R_D by >= 5.94e-5")
W("   * the boundary max-min is < R_D by 1.55e-8")
W("  => R_D(C) = maximum over a FINITE set: the 220 triple circumradii whose")
W("     circumcentre lies in D (plus boundary, which is slack).")
(EV / "reduced_system_2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
