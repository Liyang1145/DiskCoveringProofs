"""Step 14: SETTLED exact system for the C182 candidate (closure algebra finalised).

All residuals computed at dps=60.  Facts established numerically to <= 4e-17
(i.e. exact in the ideal configuration; the 17-digit literal perturbs by ~1e-17):

  (F1) u2 = circ(c0,c6,c7) lies on the +x axis (the hub ray)         [y_u2 = 0]
  (F2) |u2| = a + R        and |u2 - c0| = R  (both, automatically consistent)
  (F3) u3 = circ(c0,c1,c3) lies on the 60-deg ray                    [y/x = sqrt3]
  (F4) |u3| = t - R        and |u3 - c0| = R
  (F5) cos(al) = ((a+R)^2 + b^2 - R^2) / (2 b (a+R))                 [closure]
  (F6) al + be = 0         (the ideal cfg has a mirror the literal rounds away)
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
def mark(name, val, tol=mp.mpf('1e-13')):
    W(f"  [{'OK ' if abs(val)<tol else 'NO '}] {name:<54} res = {mp.nstr(val,12)}")

a, t, b = nn(Am[0]), nn(Am[3]), nn(Am[6])
al = mp.atan2(Am[6][1], Am[6][0]); be = mp.atan2(Am[7][1], Am[7][0])
u2 = circ(Am[0], Am[6], Am[7]); u3 = circ(Am[0], Am[1], Am[3])
W("### data"); W(f"  a={mp.nstr(a,34)}  t={mp.nstr(t,34)}  b={mp.nstr(b,34)}")
W(f"  al={mp.nstr(al*180/mp.pi,24)}deg  be={mp.nstr(be*180/mp.pi,24)}deg  R={mp.nstr(R,34)}")
W(f"  u2=({mp.nstr(u2[0],26)},{mp.nstr(u2[1],26)})  |u2|={mp.nstr(nn(u2),34)}")
W(f"  u3=({mp.nstr(u3[0],26)},{mp.nstr(u3[1],26)})  |u3|={mp.nstr(nn(u3),34)}")
W("")
W("### verified facts")
mark("(F1) u2 on the +x axis", u2[1])
mark("(F2) |u2| - (a+R)", nn(u2)-(a+R))
mark("(F3) u3 y/x - tan60", u3[1]/u3[0]-mp.sqrt(3))
mark("(F4) |u3| - (t-R)", nn(u3)-(t-R))
mark("(F5) cos(al) - ((a+R)^2+b^2-R^2)/(2b(a+R))",
     mp.cos(al)-((a+R)**2+b**2-R**2)/(2*b*(a+R)))
mark("(F6) al+be", (al+be)*180/mp.pi)
mark("(F7) |u3| = a + R  (=> t - R = a + R => t = a + 2R !)",
     nn(u3)-(a+2*R) if False else nn(u3)-(a+R))
mark("(F8) t = a + 2R", t-(a+2*R))
mark("(F9) a = 1 - 2R", a-(1-2*R))
mark("(F10) b = ?  b - (1-R)/(2cos(al))", b-(1-R)/(2*mp.cos(al)))
mark("(F11) b - (a+R)/cos(al)", b-(a+R)/mp.cos(al))
mark("(F12) b - (a+2R)/cos(al)", b-(a+2*R)/mp.cos(al))
W("")
W("### the two conditions that ARE the system")
# From F1+F2:  u2 = (a+R, 0) and u2 = circ(c0,c6,c7)
#   circ: |u2-c0|=R (auto), |u2-c6|=|u2-c7|=R and u2.(c6-c7)=0 (auto by symmetry al=-be)
#   the non-auto condition is |u2 - c6| = R with |u2| = a+R, |c6| = b, angle(al):
mark("(C1) |u2-c6| = R  [= law of cosines closure]", dd(u2, Am[6])-R)
W("       expansion: (a+R)^2 + b^2 - 2 b (a+R) cos(al) = R^2")
mark("       same, from F5 by algebra",
     (a+R)**2+b**2-2*b*(a+R)*mp.cos(al)-R**2)
W("")
W("### solve: (a,t,b,al) from the 4 conditions F1(on-ray)+F2+F4+F5, R given")
def sysfun(v):
    a_, t_, b_, al_ = v
    c0 = (a_, mp.mpf(0)); c1 = (a_*mp.cos(2*mp.pi/3), a_*mp.sin(2*mp.pi/3))
    c3 = (t_*mp.cos(mp.pi/3), t_*mp.sin(mp.pi/3))
    c6 = (b_*mp.cos(al_), b_*mp.sin(al_)); c7 = (b_*mp.cos(-al_), b_*mp.sin(-al_))
    u2_ = circ(c0, c6, c7); u3_ = circ(c0, c1, c3)
    return mp.matrix([u2_[1],
                      nn(u2_)-(a_+R),
                      nn(u3_)-(t_-R),
                      u3_[1]/u3_[0]-mp.sqrt(3)])
x0 = [a, t, b, al]
W("  residuals at the literal: " + str([mp.nstr(v,6) for v in sysfun(x0)]))
sol = mp.findroot(lambda *v: sysfun(list(v)), x0, tol=mp.mpf('1e-45'), maxsteps=100)
a_, t_, b_, al_ = [sol[i] for i in range(4)]
W(f"  solved: a={mp.nstr(a_,34)}")
W(f"          t={mp.nstr(t_,34)}")
W(f"          b={mp.nstr(b_,34)}")
W(f"          al={mp.nstr(al_*180/mp.pi,30)} deg")
W(f"  residuals: " + str([mp.nstr(v,4) for v in sysfun(sol)]))
W(f"  t - (a+2R) = {mp.nstr(t_-(a_+2*R),8)}")
W(f"  a - (1-2R) = {mp.nstr(a_-(1-2*R),8)}")
W(f"  al+be_in = {mp.nstr(al_*180/mp.pi+be*180/mp.pi,8)}")
W("")
W("### rank of the 4x4 system at the solution")
J = mp.matrix(4,4); h = mp.mpf('1e-22')
for k in range(4):
    xp=list(sol); xm=list(sol); xp[k]=xp[k]+h; xm[k]=xm[k]-h
    rp, rm = sysfun(xp), sysfun(xm)
    for i in range(4): J[i,k] = (rp[i]-rm[i])/(2*h)
sv = mp.svd(J, compute_uv=False)
W("  singular values: " + str([mp.nstr(s,8) for s in sv]))
W(f"  rank: {sum(1 for s in sv if s > mp.mpf('1e-12')*sv[0])}/4  -> isolated root if 4")
(EV / "settled_system.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
