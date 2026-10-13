"""Step 21: reconcile the lead's G with the calibrated chart's G.

The lead's G (from the message) is  G_T = S(1+t^2-r^2) - t(3b^2-w^2),  S = b^2+w^2/3,
which evaluates to -0.1997 at the calibrated root -- NOT zero.  The chart's G (in the
calibration JSON) IS zero there.  Find the exact relation between them.
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 60
from fractions import Fraction as Fr
import sympy as sp

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
Jcal = json.loads((ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
OUT = []
def W(s=""): OUT.append(str(s))
a_, t_, r_, w_ = [mp.mpf(s) for s in Jcal["root"]]
b = (1+a_+r_)/2
S = b**2 + w_**2/3
GT = S*(1+t_**2-r_**2) - t_*(3*b**2-w_**2)
W("### evaluations at the calibrated root")
W(f"  b=(1+a+r)/2 = {mp.nstr(b,30)}")
W(f"  S = b^2+w^2/3 = {mp.nstr(S,30)}")
W(f"  G_T (lead) = {mp.nstr(GT,12)}")
# chart's G
Gsp = sp.sympify(Jcal["G"])
aa, tt, rr, ww = sp.symbols('a t r w')
Gchart = mp.mpf(str(sp.N(Gsp.subs({aa: a_, tt: t_, rr: r_, ww: w_}), 40)))
W(f"  G_chart = {mp.nstr(Gchart,12)}")
W("")
W("### candidate explanations of the 0.1997 gap")
fx = (1-r_)
W(f"  1-b = {mp.nstr(1-b,20)}   2t(1-b) = {mp.nstr(2*t_*(1-b),20)}")
W(f"  t*r = {mp.nstr(t_*r_,20)}   2t(1-b)/r = {mp.nstr(2*t_*(1-b)/r_,20)}")
W(f"  q = 2(1-b)/r = {mp.nstr(2*(1-b)/r_,20)}")
W("  G_chart - G_T = " + mp.nstr(Gchart-GT, 20))
W("")
W("### exact: is G_chart - G_T = 2 t (1-b) ?")
W(f"   2 t (1-b)      = {mp.nstr(2*t_*(1-b),20)}")
W(f"   G_chart - G_T  = {mp.nstr(Gchart-GT,20)}")
W(f"   ratio          = {mp.nstr((Gchart-GT)/(2*t_*(1-b)),20)}")
W("")
W("### So the chart's G is the TILING condition with cos(60-2beta) written in terms of")
W("### (b,w) where b is NOT the ring radius but the effective mid-ring radial parameter.")
W("### Recover the chart's own b from its G=0 with the other data:")
W("   the chart's G as a polynomial identity in w: solve for w given (a,t,r):")
sol = mp.findroot(lambda W_: mp.mpf(str(sp.N(Gsp.subs({aa: a_, tt: t_, rr: r_, ww: W_}), 40))),
                  w_, tol=mp.mpf('1e-50'))
W(f"   solved w = {mp.nstr(sol,40)}   (calibrated w = {mp.nstr(w_,40)})")
W("")
W("### what IS the chart's alpha (the middle-ring arc half-width)?")
W("   tiling: cos(pi/3 - 2beta) = (1+t^2-r^2)/(2t);  cos beta = b/s, sin beta = v/s,")
W("   with s^2 = b^2+v^2 = d+r^2 (d=a+r).  Evaluate with the calibrated numbers:")
c1 = (1+t_**2-r_**2)/(2*t_)
W(f"   (1+t^2-r^2)/(2t) = cos(pi/3-2beta) = {mp.nstr(c1,30)}   -> pi/3-2beta = "
  f"{mp.nstr(mp.acos(c1)*180/mp.pi,20)} deg")
W(f"   so 2beta = {mp.nstr(60-mp.acos(c1)*180/mp.pi,20)} deg, beta = "
  f"{mp.nstr((60-mp.acos(c1)*180/mp.pi)/2,20)} deg")
W(f"   and alpha = pi/3 - 2beta = {mp.nstr(mp.acos(c1)*180/mp.pi,20)} deg")
W("")
W("### the C3 data's own angles for comparison")
lit = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in json.loads(
    (ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))["centers_dec17"]]
phi0 = mp.atan2(lit[0][1], lit[0][0]); cs, sn = mp.cos(-phi0), mp.sin(-phi0)
Am = [(cs*c[0]-sn*c[1], sn*c[0]+cs*c[1]) for c in lit]
alm = mp.atan2(Am[6][1], Am[6][0])*180/mp.pi
W(f"   C3 literal: al = {mp.nstr(alm,20)} deg  (= 90 - 2beta would be "
  f"{mp.nstr(90-(60-mp.acos(c1)*180/mp.pi),20)})")
W(f"   C3 literal: |c_6| = {mp.nstr(mp.sqrt(Am[6][0]**2+Am[6][1]**2),30)}")
W(f"   chart b       = {mp.nstr(b,30)}")
W(f"   ratio |c_6|/b = {mp.nstr(mp.sqrt(Am[6][0]**2+Am[6][1]**2)/b,20)}")
(EV / "G_reconcile.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
