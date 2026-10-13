"""Step 20: verify the lead's simplified system (F,G,H,T) and isolate its root exactly.

  b = (1+a+r)/2,  S = b^2 + w^2/3,  A = 3b^2 - w^2 - 2 b w
  F = a^2 + a r - a t - 2 r t + t^2
  G = S*(1 + t^2 - r^2) - t*(3b^2 - w^2)          [the lead's G, cleared of denominators]
  H = -12 r^2 + 4 w^2 + 3(1-a-r)^2
  T = w*S^2*(2a - t + r)*(1 - t^2 - r^2) + (S - b)*(2t - 2r - a)*t^2*A
Plus the independent stress-recurrence check (all link weights must be > 0).
"""
from pathlib import Path
from fractions import Fraction as Fr
import json, math
import sympy as sp
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
Jcal = json.loads((ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
OUT = []
def W(s=""): OUT.append(str(s))
a_, t_, r_, w_ = [mp.mpf(s) for s in Jcal["root"]]

b = (1+a_+r_)/2
S = b**2 + w_**2/3
A = 3*b**2 - w_**2 - 2*b*w_
W("### lead's simplified system (F,G,H,T) at the calibrated numeric root")
F = a_**2 + a_*r_ - a_*t_ - 2*r_*t_ + t_**2
G = S*(1 + t_**2 - r_**2) - t_*(3*b**2 - w_**2)
H = -12*r_**2 + 4*w_**2 + 3*(1-a_-r_)**2
T = (w_*S**2*(2*a_ - t_ + r_)*(1 - t_**2 - r_**2)
     + (S - b)*(2*t_ - 2*r_ - a_)*t_**2*A)
for n, v in (('F', F), ('G', G), ('H', H), ('T', T)):
    W(f"  {n} = {mp.nstr(v, 8)}")
W("")
W("### derived quantities")
W(f"  b = (1+a+r)/2 = {mp.nstr(b,40)}")
W(f"  S = b^2+w^2/3 = {mp.nstr(S,40)}")
W(f"  A = 3b^2-w^2-2bw = {mp.nstr(A,40)}")
W(f"  v = w/sqrt3 = {mp.nstr(w_/mp.sqrt(3),40)}")
W(f"  check S = b^2+v^2 : {mp.nstr(S-(b**2+w_**2/3),6)}")
W(f"  check v^2 = r^2-(1-a-r)^2/4 : {mp.nstr(w_**2/3-(r_**2-(1-a_-r_)**2/4),8)}")
W("")
W("### stress recurrence (lead's formulas) at the root -- all weights must be > 0")
sv = {}
sv['p'] = mp.mpf(1)
sv['q'] = 2*(1-b)/r_
sv['u'] = sv['q']*r_/(2*a_-(t_-r_))
sv['j'] = sv['u']*(2*t_-2*r_-a_)/r_
alpha = mp.asin((3*b**2-w_**2-2*b*w_)/(2*mp.sqrt(3)*S))
sv['z'] = sv['j']*r_/(2*(mp.cos(alpha)-t_))
sv['x'] = -b*r_**2/(S-b)
sv['y'] = (b-1)*S/(S-b)
W(f"  alpha = {mp.nstr(alpha*180/mp.pi,20)} deg   (compared with asin = {mp.nstr(mp.asin((3*b**2-w_**2-2*b*w_)/(2*mp.sqrt(3)*S))*180/mp.pi,20)})")
for k in ('p', 'q', 'u', 'j', 'z', 'x', 'y'):
    W(f"  {k} = {mp.nstr(sv[k],14)}   positive: {sv[k] > 0}")
W(f"  lead reported: x=2.14052584 y=2.77987047 z=3.61663195 p=1 q=.9987605 u=2.43000956 j=3.61968487")
W("")
W("### residual of the transition torque-balance (the lead's T in the y*v = z*t*sin(alpha) form)")
W(f"  y*v = {mp.nstr(sv['y']*(w_/mp.sqrt(3)),20)}")
W(f"  z*t*sin(alpha) = {mp.nstr(sv['z']*t_*mp.sin(alpha),20)}")
W(f"  difference = {mp.nstr(sv['y']*(w_/mp.sqrt(3)) - sv['z']*t_*mp.sin(alpha),8)}")
W("")
W("### exact-rational Krawczyk for (F,G,H,T)")
aa, tt, rr, ww = sp.symbols('a t r w')
bb = (1+aa+rr)/2
SS = bb**2 + ww**2/3
AA = 3*bb**2 - ww**2 - 2*bb*ww
Fsp = aa**2 + aa*rr - aa*tt - 2*rr*tt + tt**2
Gsp = sp.expand(SS*(1+tt**2-rr**2) - tt*(3*bb**2-ww**2))
Hsp = -12*rr**2 + 4*ww**2 + 3*(1-aa-rr)**2
Tsp = sp.expand(ww*SS**2*(2*aa-tt+rr)*(1-tt**2-rr**2) + (SS-bb)*(2*tt-2*rr-aa)*tt**2*AA)
eqs2 = (Fsp, Gsp, Hsp, Tsp)
vars2 = (aa, tt, rr, ww)
sub = {aa: a_, tt: t_, rr: r_, ww: w_}
W("  exact residuals (mpmath 60d):")
for n, e in zip('FGHT', eqs2):
    W(f"    {n} = {mp.nstr(mp.mpf(str(sp.N(e.subs(sub), 60))), 8)}")
Jm = sp.Matrix(4, 4, lambda i, j: sp.diff(eqs2[i], vars2[j]))
Jnum = mp.matrix(4, 4)
for i in range(4):
    for j in range(4):
        Jnum[i, j] = mp.mpf(str(sp.N(Jm[i, j].subs(sub), 60)))
sv_ = mp.svd(Jnum, compute_uv=False)
W("  4x4 Jacobian singular values: " + str([mp.nstr(s, 8) for s in sv_]))
W(f"  rank: {sum(1 for s in sv_ if s > mp.mpf('1e-20')*sv_[0])}/4   |det| = {mp.nstr(abs(mp.det(Jnum)),10)}")
(EV / "simplified_system.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
