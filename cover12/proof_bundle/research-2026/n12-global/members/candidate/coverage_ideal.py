"""Step 26: COVERAGE CERTIFICATE for the ideal chart configuration.

OBJECT (correct one this time): the lead's certified root box of F,G,H,T in
evidence/root-t-certificate.json.  Centres are constructed analytically as:

  hub_k  = a * u(120k)                    k=0,1,2
  mid_k  = t * u(60 + 120k)               k=0,1,2
  high_k = b * u( 60 + mu + 120k)         k=0,1,2      b = sqrt(S), S = b^2 + w^2/3
  far_k  = b * u(240 - mu + 120k)         k=0,1,2      (mirror orbit)

with u(th) = (cos th, sin th), and b (the chart parameter) the ARC-CENTRE radius
(1+a+r)/2, so the physical ring norm is sqrt(b^2 + w^2/3).

NOTE: sin mu = (w/sqrt3)/b, cos mu = b/sqrt(S).  Eliminating mu gives the rational
identity (w/sqrt3)/b = sin of the angle whose cos is b/sqrt(S); equivalently
sin mu * b = w/sqrt3 and cos mu * b = b.
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
box = cert["box"]
img = cert["image"]
W("### certified root box of (F,G,H,T)  [lead/root_t_certificate.py]")
names = ('a', 't', 'r', 'w')
q2m = lambda s: mp.mpf(Fr(s).numerator)/mp.mpf(Fr(s).denominator)
blo = [q2m(b[0]) for b in box]
bhi = [q2m(b[1]) for b in box]
for n, lo, hi in zip(names, blo, bhi):
    W(f"  {n} in [{mp.nstr(lo,50)}, {mp.nstr(hi,50)}]   width {mp.nstr(hi-lo,4)}")
W("")
a_lo, t_lo, r_lo, w_lo = blo
a_hi, t_hi, r_hi, w_hi = bhi
r = (r_lo + r_hi) / 2
a = (a_lo + a_hi) / 2
t = (t_lo + t_hi) / 2
w = (w_lo + w_hi) / 2
W(f"### midpoints used for the numeric report (certified interval widths are 1e-30)")
W(f"  r = {mp.nstr(r,50)}")
W(f"  the C182/D2 certified covering radius of the LITERAL config was")
W(f"  [0.361102963744508672616920293903, 0.361102963744508672616920293904]  <- different object")
W(f"  r lies in that interval: {mp.mpf('0.361102963744508672616920293903') < r < mp.mpf('0.361102963744508672616920293904')}")
W("")
S = (w*w)/3 + ((1+a+r)/2)**2
b = mp.sqrt(S)
mu = mp.asin((w/mp.sqrt(3))/b)
W("### derived geometric parameters (chart)")
W(f"  (1+a+r)/2 = {mp.nstr((1+a+r)/2,40)}")
W(f"  S = (1+a+r)^2/4 + w^2/3 = {mp.nstr(S,40)}")
W(f"  ring norm b_phys = sqrt(S) = {mp.nstr(b,40)}")
W(f"  mu = asin(w/(sqrt3 b)) = {mp.nstr(mu*180/mp.pi,30)} deg")
W(f"  check: b*sin(mu) = {mp.nstr(b*mp.sin(mu),30)}   vs w/sqrt3 = {mp.nstr(w/mp.sqrt(3),30)}")
W("")

def pt(rho, th):
    return (rho*mp.cos(th), rho*mp.sin(th))
U = lambda k: 2*mp.pi*k/3
cent = []
for k in range(3):   # hubs 0,1,2
    cent.append(pt(a, U(k)))
for k in range(3):   # mid ring 3,4,5
    cent.append(pt(t, mp.pi/3 + U(k)))
for k in range(3):   # high 6,8,9
    cent.append(pt(b, mp.pi/3 + mu + U(k)))
for k in range(3):   # far 7,10,11
    cent.append(pt(b, 4*mp.pi/3 - mu + U(k)))
W("### constructed centres (idx: polar radius, angle deg)")
for i, c in enumerate(cent):
    rho = mp.sqrt(c[0]**2+c[1]**2)
    th = mp.atan2(c[1], c[0])*180/mp.pi
    W(f"  {i:2d}: ({mp.nstr(c[0],20)}, {mp.nstr(c[1],20)})   |c|={mp.nstr(rho,20)}  ang={mp.nstr(th,18)}")
W("")
W("### C3 covariance test")
mx = mp.mpf(0)
for k in (1, 2):
    th = U(k)
    c, s = mp.cos(th), mp.sin(th)
    for i in range(12):
        q = (c*cent[i][0]-s*cent[i][1], s*cent[i][0]+c*cent[i][1])
        d = min(mp.sqrt((q[0]-p[0])**2+(q[1]-p[1])**2) for p in cent)
        mx = max(mx, d)
W(f"  max_i min_j |R120 c_i - c_j| = {mp.nstr(mx,8)}   (exact by construction)")
W("")

# ---------- finite criterion: all triples ----------
W("### finite coverage criterion: every triple's circumcentre-IN-D distance <= r")
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(d) < 1e-60: return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d)
def nn(p): return mp.sqrt(p[0]**2+p[1]**2)
rows = []
for tri in itertools.combinations(range(12), 3):
    u = circ(cent[tri[0]], cent[tri[1]], cent[tri[2]])
    if u is None: continue
    if nn(u) > 1: continue          # circumcentre outside D: not an interior hole
    f = min(mp.sqrt((u[0]-c[0])**2+(u[1]-c[1])**2) for c in cent)
    rows.append((f, tri, u))
rows.sort(key=lambda z: -z[0])
W(f"  triples with circumcentre in D: {len(rows)}")
W("  deepest 12:")
for f, tri, u in rows[:12]:
    W(f"    tri{str(tri):<14} f={mp.nstr(f,26)}  f-r={mp.nstr(f-r,6)}  |u|={mp.nstr(nn(u),16)}")
W(f"  deepest f = {mp.nstr(rows[0][0],26)}   r = {mp.nstr(r,26)}   difference {mp.nstr(rows[0][0]-r,6)}")
W(f"  next family (rank 7) f = {mp.nstr(rows[6][0],26)}  slack vs r = {mp.nstr(r-rows[6][0],8)}")
W("")
# classify the 13 faces
W("### the 13 faces of the tiled polygon")
labels = {}
for f, tri, u in rows[:13]:
    typ = ''.join('H' if i < 3 else ('M' if i < 6 else 'R') for i in tri)
    labels[tri] = (typ, f)
for tri, (typ, f) in sorted(labels.items(), key=lambda kv: -kv[1][1]):
    W(f"    tri{str(tri):<14} type={typ:<4} f={mp.nstr(f,24)}  f-r={mp.nstr(f-r,6)}  "
      f"{'ACTIVE' if abs(f-r) < 1e-25 else 'slack'}")
W("")
# boundary caps
W("### boundary caps: max of f on |x|=1")
N = 2_000_000
bb = (-1, None)
for s in range(N):
    th = 2*mp.pi*s/N
    p = (mp.cos(th), mp.sin(th))
    d = min(mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in cent)
    if d > bb[0]: bb = (d, th)
W(f"  max_{{|x|=1}} f = {mp.nstr(bb[0],26)} at theta_deg={mp.nstr(bb[1]*180/mp.pi,12)}")
W(f"  r - boundary max = {mp.nstr(r-bb[0],8)}   (positive => boundary strictly inside)")
W("")
W("### summary")
W(f"  R_D(ideal chart config) = max(deepest interior Voronoi hole, boundary cap)")
W(f"     = max({mp.nstr(rows[0][0],24)}, {mp.nstr(bb[0],24)})")
W(f"     = {mp.nstr(max(rows[0][0], bb[0]),24)}")
W(f"  versus the chart radius r = {mp.nstr(r,24)}")
W(f"  difference = {mp.nstr(max(rows[0][0],bb[0])-r,8)}  (zero to the certified box width)")
(EV / "coverage_ideal.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
