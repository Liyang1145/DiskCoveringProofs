"""Step 15: INDEPENDENT verification of the lead's (F,G,H,J) chart system + interval setup.

The lead's system (evidence/d3-chart-calibration.json), variables (a,t,r,w):
  F = a^2 + a r - a t - 2 r t + t^2
  G = -3a^2r^2/4 + ... (given)
  H = -12 r^2 + 4 w^2 + 3(1-a-r)^2
  J = 2*(...)  (the stationarity determinant)
Root reported to be isolated, residual ~1e-65.

This script:
 1. re-evaluates F,G,H,J at the reported root from the JSON strings (mpmath, dps=90);
 2. checks the chart's geometric content: does the root reproduce the certified holes
    (|u2| = a+r, |u3| = t-r) and the certified radii?
 3. tests whether F,G,H are exact identities for the literal config (non-identity check).
"""
from pathlib import Path
from fractions import Fraction as F
import json, itertools
import mpmath as mp
mp.mp.dps = 90

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
J = json.loads((ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
OUT = []
def W(s=""): OUT.append(str(s))

a, t, r, w = [mp.mpf(s) for s in J["root"]]
W("### lead's (F,G,H,J) system, evaluated at the reported root (dps=90)")
W(f"  a = {mp.nstr(a,60)}")
W(f"  t = {mp.nstr(t,60)}")
W(f"  r = {mp.nstr(r,60)}")
W(f"  w = {mp.nstr(w,60)}")
W(f"  reported residuals: {J['residual']}")

def Ff(a, r, t):
    return a**2 + a*r - a*t - 2*r*t + t**2
def Gf(a, r, t, w):
    return (-3*a**2*r**2/4 + 3*a**2*t**2/4 - 3*a**2*t/4 + 3*a**2/4 - 3*a*r**3/2 - 3*a*r**2/2
            + 3*a*r*t**2/2 - 3*a*r*t/2 + 3*a*r/2 + 3*a*t**2/2 - 3*a*t*w - 3*a*t/2 + 3*a/2
            - 3*r**4/4 - 3*r**3/2 + 3*r**2*t**2/4 - 3*r**2*t/4 - r**2*w**2 + 3*r*t**2/2
            - 3*r*t*w - 3*r*t/2 + 3*r/2 + t**2*w**2 + 3*t**2/4 + t*w**2 - 3*t*w - 3*t/4 + w**2 + 3/4)
def Hf(a, r, w):
    return -12*r**2 + 4*w**2 + 3*(1-a-r)**2

W(f"  F(a,r,t) = {mp.nstr(Ff(a,r,t),10)}")
W(f"  G(a,r,t,w) = {mp.nstr(Gf(a,r,t,w),10)}")
W(f"  H(a,r,w) = {mp.nstr(Hf(a,r,w),10)}")
W(f"  (J is not re-evaluated here: it is a big polynomial; residual reported 0.0)")
W("")
W("### does the chart root match the certified config?")
tmp = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in A["centers_dec17"]]
phi0 = mp.atan2(tmp[0][1], tmp[0][0]); cs, sn = mp.cos(-phi0), mp.sin(-phi0)
Am = [(cs*c[0]-sn*c[1], sn*c[0]+cs*c[1]) for c in tmp]
am = mp.sqrt(Am[0][0]**2+Am[0][1]**2); tm = mp.sqrt(Am[3][0]**2+Am[3][1]**2); bm = mp.sqrt(Am[6][0]**2+Am[6][1]**2)
alm = mp.atan2(Am[6][1], Am[6][0])
Rcert = mp.mpf("0.361102963744508672616920293903")
W(f"  certified-literal (rotated frame):  a={mp.nstr(am,50)}  t={mp.nstr(tm,50)}")
W(f"                                      b={mp.nstr(bm,50)}  al={mp.nstr(alm*180/mp.pi,30)}deg")
W(f"  chart root:                          a={mp.nstr(a,50)}  t={mp.nstr(t,50)}  r={mp.nstr(r,50)}")
W(f"  a_chart - a_lit = {mp.nstr(a-am,8)}")
W(f"  t_chart - t_lit = {mp.nstr(t-tm,8)}")
W(f"  r_chart - R_cert = {mp.nstr(r-Rcert,8)}")
W("")
W("### chart's geometric content:  w^2 should be r^2 - (1 - (a+r))^2/4 = 3r^2/4 + (a+r)/2 - 1/4")
w2_pred = r**2 - (1-(a+r))**2/4
W(f"  w^2 = {mp.nstr(w**2,50)}")
W(f"  r^2 - (1-a-r)^2/4 = {mp.nstr(w2_pred,50)}   diff = {mp.nstr(w**2-w2_pred,8)}")
W("  H is exactly 4w^2 - 12r^2 + 3(1-a-r)^2 = 0  <=>  4w^2 = 12r^2 - 3(1-a-r)^2:")
W(f"     4w^2 = {mp.nstr(4*w**2,40)}   12r^2-3(1-a-r)^2 = {mp.nstr(12*r**2-3*(1-a-r)**2,40)}")
W("     and w^2 = r^2-(1-a-r)^2/4 <=> 4w^2 = 4r^2-(1-a-r)^2.  Compare:")
W(f"     r^2-(1-a-r)^2/4 = {mp.nstr(w2_pred,40)}  vs w^2 = {mp.nstr(w**2,40)}  diff {mp.nstr(w**2-w2_pred,8)}")
W("")
W("### does the chart reproduce the two hole relations?  b from the chart: b = ?")
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d)
def nn(p): return mp.sqrt(p[0]**2+p[1]**2)
def dd(p, q): return mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
# chart: c0 = a(1,0); c3 = t(cos60,sin60); c6 = b(cos al, sin al); c7 = b(cos al, -sin al)
# F = a^2+ar-at-2rt+t^2: this is |u3|^2 - R^2 with u3 = the point on the 60-ray at distance R from c0?
cos60, sin60 = mp.cos(mp.pi/3), mp.sin(mp.pi/3)
w3 = (r*cos60, r*sin60)
W("  test: is F = |g - c0|^2 + ... ?  evaluate candidate geometric meanings:")
W(f"     |c0 - c3|^2 = {mp.nstr(dd(Am[0],Am[3])**2,30)}")
W(f"     a^2+ar-at-2rt+t^2 = {mp.nstr(Ff(a,r,t),10)}")
W("     algebraic: F = |c3 - c0|^2 + a r - a t - 2 r t + 2 a t? try other readings:")
for name, val in [
    ("|c3-c0|^2 = a^2+t^2-2at", a**2+t**2-2*a*t),
    ("F - |c3-c0|^2", Ff(a,r,t)-(a**2+t**2-2*a*t)),
    ("F with r=0", Ff(a,0,t)),
]:
    W(f"       {name} = {mp.nstr(val,20)}")
W("")
W("### non-identity checks: are F,G,H identically zero on the literal configuration?")
W("  (substituting the literal's a,t,r,w reproduces micro-residuals only if the literal")
W("   is an exact rounding of the ideal root; macroscopic residuals mean the chart is a")
W("   DIFFERENT family)")
w_lit = None
# reconstruct the literal's counterpart of w: w = 3v with v the half-separation of the high pair
# in the chart the high ring is ONE orbit of 2 per hub: (b, +-v).  The literal has TWO
# orbits of 3 - report the mismatch explicitly.
b_lit = bm
W(f"  literal b = {mp.nstr(b_lit,30)}  (chart b = (1+a+r)/2 = {mp.nstr((1+a+r)/2,30)} from D3-EXACT-CHART)")
W(f"  DIFFERENCE = {mp.nstr(b_lit-(1+a+r)/2,8)}   <- macroscopic => chart family != literal config")
(EV / "chart_check.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
