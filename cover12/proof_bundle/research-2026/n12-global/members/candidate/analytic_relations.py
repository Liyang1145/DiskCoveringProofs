"""Step 11: analytic re-derivation of the C182 candidate's exact relations.

Frame: rotate by -theta_0 so the hub orbit A={0,1,2} sits at 0,120,240 deg.
Site layout (degrees, relative):
   A = {0,1,2}:  norm a, angles 0, 120, 240
   B = {3,4,5}:  norm t, angles 60, 180, 300
   C = {6,8,9}:  norm b, angles  al, al+120, al+240        (al ~ +20.8909)
   D = {7,10,11}:norm b, angles  be, be+120, be+240        (be ~ -20.8909)

Hypotheses to verify (task: self-consistent geometric representation for root isolation):
 H1  a = 1 - 2R
 H2  t = (1 + R + sqrt(3) R)/2
 H3  hole u2 = circ(c0,c6,c7) satisfies  |u2| = 2R - a   and  |u2 - c0| = R
 H4  be = -al  (by the reflection the literal cannot see, but the ideal cfg may have)
 H5  the closure equation relating al and R
 H6  |u3 - c1| = R automatically (hub branch)
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
Am = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in A["centers_dec17"]]
rad = [mp.sqrt(c[0]**2+c[1]**2) for c in Am]
ang = [mp.atan2(c[1], c[0]) for c in Am]
phi0 = ang[0]
rel = [mp.fmod((ang[i]-phi0)*180/mp.pi+360, 360) for i in range(12)]
OUT = []
def W(s=""): OUT.append(str(s))

R = mp.mpf("0.361102963744508672616920293903")
a_m, t_m, b_m = rad[0], rad[3], rad[6]
al_m = rel[6]
be_m = rel[7] - 360          # ~ -20.8909
W("### measured (relative to c_0 direction)")
W(f"  a = {mp.nstr(a_m,36)}")
W(f"  t = {mp.nstr(t_m,36)}")
W(f"  b = {mp.nstr(b_m,36)}")
W(f"  al = {mp.nstr(al_m,30)} deg     be = {mp.nstr(be_m,30)} deg")
W(f"  al + be = {mp.nstr(al_m+be_m,12)}      [H4: should be 0]")
W("")
W("### H1: a = 1 - 2R ?")
W(f"   1-2R = {mp.nstr(1-2*R,36)}      a = {mp.nstr(a_m,36)}   diff = {mp.nstr(a_m-(1-2*R),8)}")
W("### H2: t = (1 + R + sqrt(3) R)/2 ?")
h2 = (1+R+mp.sqrt(3)*R)/2
W(f"   (1+R+sqrt3 R)/2 = {mp.nstr(h2,36)}   t = {mp.nstr(t_m,36)}   diff = {mp.nstr(t_m-h2,8)}")
W("       (equivalent form t = 1 - R + (sqrt3 R - (1-R))/2 : t = (1+R+R sqrt3)/2)")
W("")
# ---- H3: the u2 hole
h = mp.mpf(0)
def circ(p, q, r):
    ax, ay = p; bx, by = q; cx, cy = r
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d
    return (ux, uy)
def d(p, q): return mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
def nrm(p): return mp.sqrt(p[0]**2+p[1]**2)

# rotate coordinates so c_0 -> (a,0)
cs, sn = mp.cos(-phi0), mp.sin(-phi0)
def rot(p): return (cs*p[0]-sn*p[1], sn*p[0]+cs*p[1])
Ar = [rot(c) for c in Am]
W("### rotated coordinates (c_0 on the x-axis)")
for i in (0, 3, 6, 7, 1, 2, 8, 9, 10, 11, 4, 5):
    W(f"  c{i:2d}: ({mp.nstr(Ar[i][0],22)}, {mp.nstr(Ar[i][1],22)})  |c|={mp.nstr(nrm(Ar[i]),22)}"
      f"  ang={mp.nstr(mp.atan2(Ar[i][1],Ar[i][0])*180/mp.pi,20)}")
u2 = circ(Ar[0], Ar[6], Ar[7])
u3 = circ(Ar[0], Ar[1], Ar[3])
W("")
W("### H3: u2 = circ(c0,c6,c7)")
W(f"   u2 = ({mp.nstr(u2[0],26)}, {mp.nstr(u2[1],26)})  |u2| = {mp.nstr(nrm(u2),34)}")
W(f"   |u2| - (2R - a)      = {mp.nstr(nrm(u2)-(2*R-a_m),8)}")
W(f"   |u2| - (a + R)       = {mp.nstr(nrm(u2)-(a_m+R),8)}")
W(f"   |u2 - c0| - R        = {mp.nstr(d(u2,Ar[0])-R,8)}")
W(f"   |u2 - c6| - R        = {mp.nstr(d(u2,Ar[6])-R,8)}")
W(f"   |u2 - c7| - R        = {mp.nstr(d(u2,Ar[7])-R,8)}")
W(f"   angle(u2) in deg     = {mp.nstr(mp.atan2(u2[1],u2[0])*180/mp.pi,24)}")
W(f"   so the hole u2 lies on the ray -(al+be)/2 = {mp.nstr(-(al_m+be_m)/2,20)} deg  "
  f"[the bisector of c6 and c7]")
W("")
W("### H6: u3 = circ(c0,c1,c3)")
W(f"   u3 = ({mp.nstr(u3[0],26)}, {mp.nstr(u3[1],26)})  |u3| = {mp.nstr(nrm(u3),34)}")
W(f"   |u3| - (t - R)  = {mp.nstr(nrm(u3)-(t_m-R),8)}")
for i in (0, 1, 3):
    W(f"   |u3 - c{i}| - R = {mp.nstr(d(u3,Ar[i])-R,8)}")
W(f"   angle(u3) = {mp.nstr(mp.atan2(u3[1],u3[0])*180/mp.pi,24)} deg (= 60 deg mod 120 by C3)")
W("")
W("### H5: the closure relation between al and R")
W("   Let x = cos(al) and y = sin(al).  Analytic derivation in the rotated frame:")
W("     * c0 = a(1,0), c6 = b(cos al, sin al), c7 = b(cos be, sin be) with be = -al")
W("     * u2 is equidistant: |u2-c6|=|u2-c7| => u2 . (c6-c7) = 0")
W("       c6 - c7 = b(cos al - cos be, sin al - sin be) = 2b sin al (sin al, -cos al)/1 ... ")
W("     * hence u2 is parallel to (sin al, cos al) or its negative; with the data u2 is")
W("       along the direction (sin al*? ) -- use the measured sign.")
u2dir = mp.atan2(u2[1], u2[0])*180/mp.pi
W(f"     measured: angle(u2) = {mp.nstr(u2dir,20)};  al = {mp.nstr(al_m,20)};"
  f"  angle(u2) - (90 - al) = {mp.nstr(u2dir-(90-al_m),10)}")
W(f"                angle(u2) - (al - 90) = {mp.nstr(u2dir-(al_m-90),10)}")
W(f"                angle(u2) - (al+90)   = {mp.nstr(u2dir-(al_m+90),10)}")
W(f"                angle(u2) - (-al)     = {mp.nstr(u2dir-(-al_m),10)}")
W("")
W("   Let theta = angle(u2). From u2 . (c6 - c7) = 0:")
W("     0 = u2.(c6-c7) = |u2| b [cos(th-al) - cos(th-be)]   [since |c6|=|c7|=b]")
W("     => cos(th-al) = cos(th-be) => th = (al+be)/2 (mod 180)")
W(f"     measured (al+be)/2 = {mp.nstr((al_m+be_m)/2,20)} deg ;  angle(u2) mod 180 = "
  f"{mp.nstr(mp.fmod(u2dir,180),20)}")
W("     => th = (al+be)/2 + 180  or  (al+be)/2 .  Data says:")
W(f"        (al+be)/2 = {mp.nstr((al_m+be_m)/2,20)}; (al+be)/2+180 = {mp.nstr((al_m+be_m)/2+180,20)}")
W(f"        actual th = {mp.nstr(u2dir,20)}  -> mod 360 matches "
  f"{mp.nstr((al_m+be_m)/2+180,16)}? diff = {mp.nstr(u2dir-((al_m+be_m)/2+180),10)}")
W("")
W("   |u2 - c0| = R with u2 = s(cos th, sin th), |u2| = s:")
W("     s^2 - 2 s a cos(th) + a^2 = R^2")
W(f"     measured s = |u2| = {mp.nstr(nrm(u2),30)}")
W(f"     measured a = {mp.nstr(a_m,30)}  th = {mp.nstr(u2dir,20)}  R = {mp.nstr(R,30)}")
W(f"     residual s^2 - 2 s a cos(th) + a^2 - R^2 = "
  f"{mp.nstr(nrm(u2)**2 - 2*nrm(u2)*a_m*mp.cos(u2dir*mp.pi/180) + a_m**2 - R**2,8)}")
(EV / "analytic_relations.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
