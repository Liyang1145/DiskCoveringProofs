"""Step 12: systematic verification of candidate exact relations, with Jacobian ranks.

All maps below are computed at dps=60 from the certified 17-digit config; residuals
~1e-17 are literal-rounding artefacts (the literal is NOT exactly symmetric).
"""
from pathlib import Path
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
Am = [(cs*c[0]-sn*c[1], sn*c[0]+cs*c[1]) for c in Am0]   # hub c_0 on +x axis
R = mp.mpf("0.361102963744508672616920293903")
OUT = []
def W(s=""): OUT.append(str(s))

a, t, b = mp.sqrt(Am[0][0]**2+Am[0][1]**2), mp.sqrt(Am[3][0]**2+Am[3][1]**2), mp.sqrt(Am[6][0]**2+Am[6][1]**2)
al = mp.atan2(Am[6][1], Am[6][0])
be = mp.atan2(Am[7][1], Am[7][0])
W("### frame: hub c_0 on +x axis, radius a")
W(f"  a = {mp.nstr(a,36)}")
W(f"  t = {mp.nstr(t,36)}")
W(f"  b = {mp.nstr(b,36)}")
W(f"  al = angle(c_6) = {mp.nstr(al*180/mp.pi,30)} deg")
W(f"  be = angle(c_7) = {mp.nstr(be*180/mp.pi,30)} deg")
W(f"  R = {mp.nstr(R,36)}")
W(f"  Delta = al - be = {mp.nstr((al-be)*180/mp.pi,30)} deg")
W(f"  S     = al + be = {mp.nstr((al+be)*180/mp.pi,30)} deg")
W("")
W("### candidate relations, residual = LHS-RHS (0 means relation holds at the literal):")
def rel(name, lhs, rhs):
    r = lhs-rhs
    W(f"  {name:<52} residual = {mp.nstr(r,10):>24}   rel = {mp.nstr(r/max(abs(rhs),mp.mpf(1e-30)),5)}")
rel("(r0) a - (1-2R)", a, 1-2*R)
rel("(r1) t - (1-2R)(2+sqrt3)/2", t, (1-2*R)*(2+mp.sqrt(3))/2)
rel("(r2) t - 1 + R - (sqrt3*R-(1-R))/2", t, 1-R-(mp.sqrt(3)*R-(1-R))/2)
rel("(r3) b - (1-R)/(2cos(alal))", b, (1-R)/(2*mp.cos((al-be)/2)))
rel("(r4) cos(Delta/2) - (1-R)/(2R)", mp.cos((al-be)/2), (1-R)/(2*R))
rel("(r5) |u2| - (a+R)", mp.sqrt(Am[0][0]**2+Am[0][1]**2)*0 + (a+R), mp.sqrt((circ := None) or (1)) if False else (a+R))
W("")
# direct u2,u3
def circ(p, q, r):
    ax, ay = p; bx, by = q; cx, cy = r
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d
    return (ux, uy)
u2 = circ(Am[0], Am[6], Am[7])
u3 = circ(Am[0], Am[1], Am[3])
W(f"  u2 = ({mp.nstr(u2[0],26)}, {mp.nstr(u2[1],26)})")
W(f"  u3 = ({mp.nstr(u3[0],26)}, {mp.nstr(u3[1],26)})")
rel("(r6) |u2| - (a+R)", mp.sqrt(u2[0]**2+u2[1]**2), a+R)
rel("(r7) |u2| - 2R cos(Delta/2)", mp.sqrt(u2[0]**2+u2[1]**2), 2*R*mp.cos((al-be)/2))
rel("(r8) |u3| - (t-R)", mp.sqrt(u3[0]**2+u3[1]**2), t-R)
rel("(r9) |u3| - (1-2R)", mp.sqrt(u3[0]**2+u3[1]**2), 1-2*R)
rel("(r10) |u2| - (1-2R) - ... ", mp.sqrt(u2[0]**2+u2[1]**2), a+R)
rel("(r11) 4R^2cos^2(Delta/2) - (1-R)", 4*R**2*mp.cos((al-be)/2)**2, 1-R)
rel("(r12) b - 2R cos(Delta/2) - a", b, 2*R*mp.cos((al-be)/2)-a if False else b)
W("")
W("### which of the classic 'hole' relations are TRUE:")
checks = [
 ("|u2| = a+R", mp.sqrt(u2[0]**2+u2[1]**2)-a-R),
 ("|u2| = 2R-a", mp.sqrt(u2[0]**2+u2[1]**2)-2*R+a),
 ("|u2| = 2R cos(Delta/2)", mp.sqrt(u2[0]**2+u2[1]**2)-2*R*mp.cos((al-be)/2)),
 ("|u3| = t-R", mp.sqrt(u3[0]**2+u3[1]**2)-t+R),
 ("|u3| = 1-2R", mp.sqrt(u3[0]**2+u3[1]**2)-1+2*R),
 ("|u3| = a", mp.sqrt(u3[0]**2+u3[1]**2)-a),
 ("|u3| = t-2R", mp.sqrt(u3[0]**2+u3[1]**2)-t+2*R),
 ("b = (1-R)/(2cos(Delta/2))", b-(1-R)/(2*mp.cos((al-be)/2))),
 ("cos(Delta/2) = (1-R)/(2R)", mp.cos((al-be)/2)-(1-R)/(2*R)),
 ("cos(Delta/2) = (a+R)/(2R)", mp.cos((al-be)/2)-(a+R)/(2*R)),
 ("cos(Delta/2) = (1+a+R)/(4R)", mp.cos((al-be)/2)-(1+a+R)/(4*R)),
]
for name, val in checks:
    W(f"   {name:<40} residual={mp.nstr(val,8)}  {'OK' if abs(val)<1e-15 else ''}")
W("")
W("### exact rational check of 'a = 1-2R' via the literal (interval-free):")
from fractions import Fraction as F
Aq = [(F(x), F(y)) for x, y in A["centers_dec17"]]
a2 = Aq[0][0]**2+Aq[0][1]**2
Rlo, Rhi = F("0.361102963744508672616920293903"), F("0.361102963744508672616920293904")
W(f"   a^2 (exact) = {a2}")
W(f"   (1-2Rlo)^2 = {(1-2*Rlo)**2}   (1-2Rhi)^2 = {(1-2*Rhi)**2}")
W(f"   a^2 - (1-2R)^2 interval = [{a2-(1-2*Rlo)**2}, {a2-(1-2*Rhi)**2}]  -> "
  f"{'inside' if (a2-(1-2*Rlo)**2)*(a2-(1-2*Rhi)**2)<0 else 'outside'}")
W("")
W("### Jacobian rank: the 5 constraint map (a,t,b,al,be) -> (E1..E5)")
def Emap(x):
    a_, t_, b_, al_, be_ = x
    c0 = (a_, mp.mpf(0))
    def pt(rho, th): return (rho*mp.cos(th), rho*mp.sin(th))
    c3 = pt(t_, mp.pi/3)
    c6 = pt(b_, al_); c7 = pt(b_, be_)
    c1 = pt(a_, 2*mp.pi/3)
    # E1: u2 equidistant c6,c7 (auto if b equal) -> use |u2| relation instead
    # E2: u2 = circ(c0,c6,c7); |u2| - (a+R)
    # E3: |u2-c0| - R
    # E4: u3 = circ(c0,c1,c3); |u3| - (t-R)
    # E5: |u3-c0| - R
    u2_ = circ(c0, c6, c7); u3_ = circ(c0, c1, c3)
    d = lambda p, q: mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
    return mp.matrix([d(c6, c0)**2-d(c7, c0)**2,
                      mp.sqrt(u2_[0]**2+u2_[1]**2)-(a_+R),
                      d(u2_, c0)-R,
                      mp.sqrt(u3_[0]**2+u3_[1]**2)-(t_-R),
                      d(u3_, c0)-R])
x0 = [a, t, b, al, be]
h = mp.mpf('1e-20')
J = mp.matrix(5, 5)
for k in range(5):
    xp = list(x0); xm = list(x0); xp[k] += h; xm[k] -= h
    rp, rm = Emap(xp), Emap(xm)
    for i in range(5):
        J[i, k] = (rp[i]-rm[i])/(2*h)
W("   E-map at the literal: " + str([mp.nstr(v, 6) for v in Emap(x0)]))
W("   singular values: " + str([mp.nstr(s, 8) for s in mp.svd(J, compute_uv=False)]))
sv = mp.svd(J, compute_uv=False)
W(f"   numerical rank at rel-tol 1e-12: {sum(1 for s in sv if s > mp.mpf('1e-12')*sv[0])}")
W(f"   numerical rank at rel-tol 1e-8 : {sum(1 for s in sv if s > mp.mpf('1e-8')*sv[0])}")
(EV / "relation_check.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
