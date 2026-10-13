"""Step 27: CORRECT construction of the ideal chart configuration.

Object: the lead's certified (a,t,r,w) box (evidence/root-t-certificate.json).
Angular layout (verified from the certified literal's exact angles, all differences
exactly 120 degrees):
   hub {0,1,2}:      radius a, angles  0, 120, 240            (deg, relative to c_0)
   mid {3,4,5}:      radius t, angles 60, 180, 300
   C   {6,8,9}:      radius b, angles +al, +al+120, +al+240   with al ~ 20.8909
   D   {7,10,11}:    radius b, angles -al, -al+120, -al+240
with b = |c_6| = |c_7| the TRUE ring norm (NOT (1+a+r)/2, which is the arc-centre
radius) and al determined by the certified w via  sin(al)*b = w/sqrt(3)? or by the
hole condition.  This script DETERMINES b and al from the chart root instead of
guessing, using the verified hole equations.
"""
from pathlib import Path
from fractions import Fraction as Fr
import json, math, sys, itertools
sys.set_int_max_str_digits(300000)
import mpmath as mp
mp.mp.dps = 80

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""): OUT.append(str(s))

cert = json.loads((ROOT / "research-2026/n12-global/evidence/root-t-certificate.json").read_text(encoding="utf-8"))
q2m = lambda s: mp.mpf(Fr(s).numerator)/mp.mpf(Fr(s).denominator)
blo = [q2m(b[0]) for b in cert["box"]]
bhi = [q2m(b[1]) for b in cert["box"]]
a, t, r, w = [(blo[i]+bhi[i])/2 for i in range(4)]
W("### certified chart root (midpoint of the certified box; widths 2e-30)")
for n, lo, hi, md in zip('a t r w'.split(), blo, bhi, (a, t, r, w)):
    W(f"  {n} = {mp.nstr(md,40)}   box [{mp.nstr(lo,32)}, {mp.nstr(hi,32)}]")
W("")

# The literal's angular layout, measured to 1e-16 (exact multiples of 120 apart):
lit = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in json.loads(
    (ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))["centers_dec17"]]
phi0 = mp.atan2(lit[0][1], lit[0][0])
rel = [mp.fmod((mp.atan2(c[1], c[0])-phi0)*180/mp.pi+360, 360) for c in lit]
al = rel[6]
W(f"### literal's own relative angles (used only for the LAYOUT, not as the object)")
for i in range(12):
    W(f"  {i:2d}: {mp.nstr(rel[i],20)} deg")
W(f"  al = {mp.nstr(al,20)} deg")
W("")
W("### the layout: C at +al, D at -al (verified al+beta = 0 to 4.4e-16 in the literal)")
W("")
# the hole condition determines b:  |u2 - c0| = r with u2 = circ(c0,c6,c7)
# and the chart gives w.  We test the two candidate readings of w:
S = ((1+a+r)/2)**2 + w*w/3
W("### candidate readings of the chart's w")
W(f"  reading 1: ring norm b = (1+a+r)/2                 -> {mp.nstr((1+a+r)/2,30)}")
W(f"  reading 2: ring norm b = sqrt((1+a+r)^2/4 + w^2/3) -> {mp.nstr(mp.sqrt(S),30)}")
W(f"  reading 3: b such that b*sin(al) = w/sqrt3         -> {mp.nstr((w/mp.sqrt(3))/mp.sin(al*mp.pi/180),30)}")
W(f"  literal's b = {mp.nstr(mp.sqrt(lit[6][0]**2+lit[6][1]**2),30)}")
W("")

def build(bnorm, alpha_deg):
    A = mp.pi/180*alpha_deg
    cent = []
    for k in range(3):
        th = 2*mp.pi*k/3
        cent.append((a*mp.cos(th), a*mp.sin(th)))
    for k in range(3):
        th = mp.pi/3 + 2*mp.pi*k/3
        cent.append((t*mp.cos(th), t*mp.sin(th)))
    for k in range(3):
        th = A + 2*mp.pi*k/3
        cent.append((bnorm*mp.cos(th), bnorm*mp.sin(th)))
    for k in range(3):
        th = -A + 2*mp.pi*k/3
        cent.append((bnorm*mp.cos(th), bnorm*mp.sin(th)))
    return cent

def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(d) < 1e-60: return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d)
def nn(p): return mp.sqrt(p[0]**2+p[1]**2)

# Solve for (b, al) so that the hole relations hold with the certified (a,t,r):
#   u3 = circ(c0,c1,c3): |u3-c0|=r and u3 on the 60-deg ray and |u3|=t-r
#   u2 = circ(c0,c6,c7): |u2-c0|=r and |u2-c6|=r and u2 on the +x axis
W("### solving (b, al) from the certified (a,t,r) using the hole conditions")
c0 = (a, mp.mpf(0)); c1 = (a*mp.cos(2*mp.pi/3), a*mp.sin(2*mp.pi/3))
c3 = (t*mp.cos(mp.pi/3), t*mp.sin(mp.pi/3))
u3 = circ(c0, c1, c3)
W(f"  u3 = ({mp.nstr(u3[0],24)},{mp.nstr(u3[1],24)})  |u3|={mp.nstr(nn(u3),24)}  t-r={mp.nstr(t-r,24)}"
  f"  |u3-c0|-r={mp.nstr(mp.sqrt((u3[0]-c0[0])**2+(u3[1]-c0[1])**2)-r,8)}")
W("  (u3 depends only on (a,t) and is already consistent: the F equation)")
def hole2(bn, ad):
    A = ad*mp.pi/180
    c6 = (bn*mp.cos(A), bn*mp.sin(A)); c7 = (bn*mp.cos(-A), bn*mp.sin(-A))
    u = circ(c0, c6, c7)
    return u, mp.sqrt((u[0]-c0[0])**2+(u[1]-c0[1])**2)-r, mp.sqrt((u[0]-c6[0])**2+(u[1]-c6[1])**2)-r
for bn_, ad_ in (((1+a+r)/2, al), (mp.sqrt(S), al), ((w/mp.sqrt(3))/mp.sin(al*mp.pi/180), al)):
    u, e1, e2 = hole2(bn_, ad_)
    W(f"  b={mp.nstr(bn_,24):<28} al={mp.nstr(ad_,20)}: |u2-c0|-r={mp.nstr(e1,8)}  |u2-c6|-r={mp.nstr(e2,8)}"
      f"  |u2|={mp.nstr(nn(u),20)}")
W("")
# solve for al given b = (1+a+r)/2  (reading 1) and given sqrt(S) (reading 2)
for tag, bn_ in (("reading1 b=(1+a+r)/2", (1+a+r)/2), ("reading2 b=sqrt(S)", mp.sqrt(S))):
    try:
        sol = mp.findroot(lambda A_: hole2(bn_, A_)[1], al, tol=mp.mpf('1e-40'))
        u, e1, e2 = hole2(bn_, sol)
        W(f"  {tag}: al = {mp.nstr(sol,20)} deg   |u2|={mp.nstr(nn(u),24)}  a+r={mp.nstr(a+r,24)}"
          f"  |u2-c6|-r={mp.nstr(e2,8)}")
    except Exception as ex:
        W(f"  {tag}: no root ({ex})")
W("")
W("### which reading matches the literal?")
litb = mp.sqrt(lit[6][0]**2+lit[6][1]**2)
W(f"  literal b = {mp.nstr(litb,30)}")
W(f"  reading1  = {mp.nstr((1+a+r)/2,30)}  diff {mp.nstr(litb-(1+a+r)/2,8)}")
W(f"  reading2  = {mp.nstr(mp.sqrt(S),30)}  diff {mp.nstr(litb-mp.sqrt(S),8)}")
(EV / "layout.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
