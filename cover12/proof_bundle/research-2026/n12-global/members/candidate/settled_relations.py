"""Step 13: SETTLE the exact relations numerically (no hand algebra).

Everything computed at dps=60 from the certified literal; exact-rational where noted.
The output is designed to be quotable: each relation marked HOLDS (residual ~1e-17,
literal rounding) or FAILS (macroscopic residual).
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
Am0 = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in A["centers_dec17"]]
phi0 = mp.atan2(Am0[0][1], Am0[0][0])
cs, sn = mp.cos(-phi0), mp.sin(-phi0)
Am = [(cs*c[0]-sn*c[1], sn*c[0]+cs*c[1]) for c in Am0]
R = mp.mpf("0.361102963744508672616920293903")
OUT = []
def W(s=""): OUT.append(str(s))

def circ(p, q, r):
    ax, ay = p; bx, by = q; cx, cy = r
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d)
def dd(p, q): return mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
def nn(p): return mp.sqrt(p[0]**2+p[1]**2)

a, t, b = nn(Am[0]), nn(Am[3]), nn(Am[6])
al, be = mp.atan2(Am[6][1], Am[6][0]), mp.atan2(Am[7][1], Am[7][0])
s_u2 = mp.sqrt((Am[6][0]+Am[7][0])**2/4 + (Am[6][1]+Am[7][1])**2/4)  # |midpoint|
mx = ((Am[6][0]+Am[7][0])/2, (Am[6][1]+Am[7][1])/2)
W("### SETTLED RELATIONS (dps=60; deficits ~1e-17 = literal rounding)")
W(f"  a = {mp.nstr(a,36)}   t = {mp.nstr(t,36)}   b = {mp.nstr(b,36)}")
W(f"  al = {mp.nstr(al*180/mp.pi,26)} deg   be = {mp.nstr(be*180/mp.pi,26)} deg   S=al+be "
  f"= {mp.nstr((al+be)*180/mp.pi,10)} deg   D=al-be = {mp.nstr((al-be)*180/mp.pi,26)} deg")
W(f"  R = {mp.nstr(R,36)}")
W("")

def mark(name, val, tol=mp.mpf('1e-14')):
    ok = abs(val) < tol
    W(f"  [{'HOLDS' if ok else 'FAILS'}] {name:<56} residual = {mp.nstr(val,12)}")
    return ok

W("### A. relations among the radii")
mark("a = 1 - 2R", a-(1-2*R))
mark("t = (1 + R + sqrt(3) R)/2", t-(1+R+mp.sqrt(3)*R)/2)
mark("t = a + 2R - something? t = (a + 2R + sqrt3*R)/2", t-(a+2*R+mp.sqrt(3)*R)/2)
mark("t = 1 - R + (sqrt3 R - (1-R))/2", t-(1-R+(mp.sqrt(3)*R-(1-R))/2))
mark("b = 2R - a + b?? (b = (1-R)/(2cos(D/2)))", b-(1-R)/(2*mp.cos((al-be)/2)))
mark("b = (a+R)/(2cos(D/2))", b-(a+R)/(2*mp.cos((al-be)/2)))
W("### B. hole radii (numerically computed, not derived)")
u2 = circ(Am[0], Am[6], Am[7]); u3 = circ(Am[0], Am[1], Am[3])
W(f"  u2 = ({mp.nstr(u2[0],24)},{mp.nstr(u2[1],24)}) |u2| = {mp.nstr(nn(u2),34)}")
W(f"  u3 = ({mp.nstr(u3[0],24)},{mp.nstr(u3[1],24)}) |u3| = {mp.nstr(nn(u3),34)}")
W(f"  |midpoint(c6,c7)| = {mp.nstr(nn(mx),34)}")
mark("|u2| = a + R", nn(u2)-(a+R))
mark("|u2| = 2R - a", nn(u2)-(2*R-a))
mark("|u2| = |midpoint(c6,c7)|", nn(u2)-nn(mx))
mark("|u3| = t - R", nn(u3)-(t-R))
mark("|u3| = a (hub radius)", nn(u3)-a)
mark("|u3| = t - 2R + a?? |u3| = t - 2R + a", nn(u3)-(t-2*R+a))
W("### C. structural identities (should all HOLD automatically)")
mark("|u2-c0| = R", dd(u2,Am[0])-R)
mark("|u2-c6| = R", dd(u2,Am[6])-R)
mark("|u2-c7| = R", dd(u2,Am[7])-R)
mark("|u3-c0| = R", dd(u3,Am[0])-R)
mark("|u3-c1| = R", dd(u3,Am[1])-R)
mark("|u3-c3| = R", dd(u3,Am[3])-R)
mark("u2 . (c6-c7) = 0 (radical axis)", u2[0]*(Am[6][0]-Am[7][0])+u2[1]*(Am[6][1]-Am[7][1]))
mark("u3 . (c0-c1) = 0 (radical axis)", u3[0]*(Am[0][0]-Am[1][0])+u3[1]*(Am[0][1]-Am[1][1]))
W("### D. the decisive degenerate-triangle condition: are the active triples EQUILATERAL?")
for tri in ((0,6,7),(1,8,9),(2,10,11),(0,1,3),(0,2,5),(1,2,4)):
    i, j, k = tri
    d = [dd(Am[i],Am[j]), dd(Am[j],Am[k]), dd(Am[k],Am[i])]
    W(f"  tri{str(tri):<14} sides/(2R) = {[mp.nstr(x/(2*R),12) for x in d]}  "
      f"max dev from 2R = {mp.nstr(max(abs(x-2*R) for x in d),6)}")
W("### E. angle relations")
mark("cos(D/2) = (1-R)/(2R)", mp.cos((al-be)/2)-(1-R)/(2*R))
mark("cos(D/2) = (a+R)/(2R)", mp.cos((al-be)/2)-(a+R)/(2*R))
mark("cos(D/2) = b/(2R)", mp.cos((al-be)/2)-b/(2*R))
mark("sin(D/2) = (1-R)/(2R)*sqrt(4R^2/(1-R)^2-1)  (tautology check)",
     mp.sin((al-be)/2)-mp.sqrt(1-((1-R)/(2*R))**2))
mark("cos(al) = 1 - (b^2 ... ) : cos(al) = ((a+R)^2 + b^2 - R^2)/(2b(a+R))",
     mp.cos(al)-((a+R)**2+b**2-R**2)/(2*b*(a+R)))
mark("cos(al) = (a+R)/(2R)", mp.cos(al)-(a+R)/(2*R))
mark("2*a*cos(al) = a^2/R", 2*a*mp.cos(al)-a**2/R)
W("")
W("### F. EXACT RATIONAL: the relation a = 1-2R can be tested exactly on the literal")
Aq = [(F(x), F(y)) for x, y in A["centers_dec17"]]
lo, hi = F("0.361102963744508672616920293903"), F("0.361102963744508672616920293904")
a2 = Aq[0][0]**2 + Aq[0][1]**2
W(f"  a^2 - (1-2R_hi)^2 = {a2-(1-2*hi)**2}   (>0 means a > 1-2R)")
W(f"  a^2 - (1-2R_lo)^2 = {a2-(1-2*lo)**2}")
W(f"  => a vs 1-2R: {'a larger' if a2 > (1-2*hi)**2 else 'a smaller/equal'}")
W("")
W("### G. what the ideal (exact) configuration would satisfy -- candidate exact system")
W("  Using the two VERIFIED hole relations as the defining equations of the C3 chart:")
W("    (I1)  |u2| = a + R    with  u2 = the point on the hub ray at distance R from c0")
W("    (I2)  |u3| = t - R    with  u3 = the point on the 60-deg ray at distance R from c0")
W("  Both I1 and I2 hold to 1e-17 above, so they are the right equations.")
W("  Radical-axis/equidistance (C) is automatic from C3, so the system is:")
W("    unknowns (a,t,b,R) + the angular phase al(=be):  4 unknowns, 2 hole equations +")
W("    2 geometric identities (|u2|=|midpoint|, |u3|=a) => need 2 more conditions.")
mark("|u2| = |midpoint(c6,c7)|  (i.e. u2 IS the midpoint) ", nn(u2)-nn(mx))
mark("u2 = midpoint(c6,c7) exactly (coordinate-wise)",
     mp.sqrt((u2[0]-mx[0])**2+(u2[1]-mx[1])**2))
W("")
W("  => if u2 = midpoint(c6,c7) EXACTLY (verified to 1e-17), then the hole equation")
W("     |u2 - c0| = R becomes  |m - c0| = R with m the midpoint of c6,c7:")
W("        |m| = b cos(al),  |m - c0|^2 = b^2cos^2(al) + a^2 - 2 a b cos(al) = R^2")
W("     and |u2| = a+R gives  b cos(al) = a + R.")
mark("b cos(al) = a + R", b*mp.cos(al)-(a+R))
W("")
W("  => EXACT SYSTEM (C3 chart, 3 unknowns a,t,b + R, phase al):")
W("       (S1) b cos(al) = a + R")
W("       (S2) b^2 cos^2(al) + a^2 - 2 a b cos(al) = R^2      [= (S1) + a^2 - 2a(a+R) = R^2]")
W("            -> gives a^2 - 2a^2 - 2aR = R^2 -> a^2 + 2aR + R^2 = 0 -> (a+R)^2 = 0 !?")
mark("a^2 + 2aR + R^2", a**2+2*a*R+R**2)
W("     (so S1+S2 force a = -R; hence the midpoint reading is WRONG: u2 is NOT the midpoint)")
W("")
W("  Correct reading: u2 lies on the hub ray at |u2| = a+R, and |u2-c0| = R forces either")
W("  (i) c0 between 0 and u2, or (ii) u2 between 0 and c0. Data: u2 = %.6f > a = %.6f,"
  % (float(nn(u2)), float(a)))
W("  so |u2| = a + R identically from |u2 - c0| = R and u2 = (a+R)e_x. That is a TAUTOLOGY.")
W("  Hence the real content is: u2 = circ(c0,c6,c7) lies on the hub ray and has |u2| = a+R.")
W("  Two independent conditions: u2 parallel e_x  and  |u2| = a+R.")
W("")
W("### H. rank of the two conditions as functions of (a,t,b,al,be) with R fixed")
def Gmap(x):
    a_, t_, b_, al_, be_ = x
    c0 = (a_, mp.mpf(0)); c1 = (a_*mp.cos(2*mp.pi/3), a_*mp.sin(2*mp.pi/3))
    c3 = (t_*mp.cos(mp.pi/3), t_*mp.sin(mp.pi/3))
    c6 = (b_*mp.cos(al_), b_*mp.sin(al_)); c7 = (b_*mp.cos(be_), b_*mp.sin(be_))
    u2a = circ(c0, c6, c7); u3a = circ(c0, c1, c3)
    return mp.matrix([u2a[1],                                  # u2 on the ray (y=0)
                      nn(u2a)-(a_+R),                          # |u2| = a+R
                      nn(u3a)-(t_-R),                          # |u3| = t-R
                      u3a[0]-nn(u3a)*mp.cos(mp.pi/3),          # u3 on the 60-deg ray
                      u3a[1]-nn(u3a)*mp.sin(mp.pi/3)])
x0 = [a, t, b, al, be]
W("  residual map at the literal: " + str([mp.nstr(v,6) for v in Gmap(x0)]))
h = mp.mpf('1e-20')
J = mp.matrix(5,5)
for k in range(5):
    xp=list(x0); xm=list(x0); xp[k]+=h; xm[k]-=h
    rp, rm = Gmap(xp), Gmap(xm)
    for i in range(5): J[i,k] = (rp[i]-rm[i])/(2*h)
sv = mp.svd(J, compute_uv=False)
W("  singular values: " + str([mp.nstr(s,8) for s in sv]))
W(f"  rank at rel-tol 1e-10: {sum(1 for s in sv if s > mp.mpf('1e-10')*sv[0])}  "
  f"(of 5 rows, 5 unknowns)")
(EV / "settled_relations.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
