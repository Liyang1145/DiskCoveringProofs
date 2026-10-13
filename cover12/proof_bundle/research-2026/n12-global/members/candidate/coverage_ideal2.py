"""Step 28: COVERAGE CERTIFICATE for the ideal chart configuration (CORRECT object).

Construction (all data certified by lead/root_t_certificate.py, exact rational box):
   a,t,r,w from evidence/root-t-certificate.json
   b = sqrt( (1+a+r)^2/4 + w^2/3 )            <- the ring NORM (reading 2, verified)
   alpha from the hole condition |u2 - c0| = r,  u2 = circ(c0,c6,c7)
   centres:  hubs a*u(0,120,240);  mid t*u(60,180,300);
             C  b*u(+alpha,+alpha+120,+alpha+240);  D  b*u(-alpha,-alpha+120,-alpha+240)
Then R_D = max over Voronoi holes inside D of the circumradius, and the boundary cap max.
Criterion: every case <= r, with equality exactly on the active family.
"""
from pathlib import Path
from fractions import Fraction as Fr
import json, math, sys, itertools
sys.set_int_max_str_digits(300000)
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""): OUT.append(str(s))

cert = json.loads((ROOT / "research-2026/n12-global/evidence/root-t-certificate.json").read_text(encoding="utf-8"))
q2m = lambda s: mp.mpf(Fr(s).numerator)/mp.mpf(Fr(s).denominator)
blo = [q2m(x[0]) for x in cert["box"]]
bhi = [q2m(x[1]) for x in cert["box"]]
a, t, r, w = [(blo[i]+bhi[i])/2 for i in range(4)]
W("### certified chart root (midpoint of the certified +/-1e-30 box)")
for n, md in zip('a t r w'.split(), (a, t, r, w)):
    W(f"  {n} = {mp.nstr(md,42)}")
S = ((1+a+r)/2)**2 + w**2/3
b = mp.sqrt(S)
alpha = mp.asin((w/mp.sqrt(3))/b)
W(f"  b = sqrt((1+a+r)^2/4 + w^2/3) = {mp.nstr(b,42)}")
W(f"  alpha = asin(w/(sqrt3 b)) = {mp.nstr(alpha*180/mp.pi,30)} deg")
W("")

def build(a, t, b, al):
    c = []
    for k in range(3): c.append((a*mp.cos(2*mp.pi*k/3), a*mp.sin(2*mp.pi*k/3)))
    for k in range(3): c.append((t*mp.cos(mp.pi/3+2*mp.pi*k/3), t*mp.sin(mp.pi/3+2*mp.pi*k/3)))
    for k in range(3): c.append((b*mp.cos(al+2*mp.pi*k/3), b*mp.sin(al+2*mp.pi*k/3)))
    for k in range(3): c.append((b*mp.cos(-al+2*mp.pi*k/3), b*mp.sin(-al+2*mp.pi*k/3)))
    return c
cent = build(a, t, b, alpha)
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(d) < 1e-60: return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d)
nn = lambda p: mp.sqrt(p[0]**2+p[1]**2)

W("### centres")
for i, c in enumerate(cent):
    W(f"  {i:2d}: |c|={mp.nstr(nn(c),24)}  ang={mp.nstr(mp.atan2(c[1],c[0])*180/mp.pi,20)}")
W("")
W("### hole sanity: the deepest holes should be at distance exactly r")
u2 = circ(cent[0], cent[6], cent[7]); u3 = circ(cent[0], cent[1], cent[3])
W(f"  u2 = circ(c0,c6,c7) = ({mp.nstr(u2[0],22)},{mp.nstr(u2[1],22)})  |u2|={mp.nstr(nn(u2),24)}  a+r={mp.nstr(a+r,24)}")
W(f"     |u2-c0|-r = {mp.nstr(mp.sqrt((u2[0]-cent[0][0])**2+(u2[1]-cent[0][1])**2)-r,6)}")
W(f"     |u2-c6|-r = {mp.nstr(mp.sqrt((u2[0]-cent[6][0])**2+(u2[1]-cent[6][1])**2)-r,6)}")
W(f"  u3 = circ(c0,c1,c3) = ({mp.nstr(u3[0],22)},{mp.nstr(u3[1],22)})  |u3|={mp.nstr(nn(u3),24)}  t-r={mp.nstr(t-r,24)}")
W(f"     |u3-c0|-r = {mp.nstr(mp.sqrt((u3[0]-cent[0][0])**2+(u3[1]-cent[0][1])**2)-r,6)}")
W("")
W("### FINITE CRITERION: all triples whose circumcentre lies in D")
rows = []
for tri in itertools.combinations(range(12), 3):
    u = circ(cent[tri[0]], cent[tri[1]], cent[tri[2]])
    if u is None or nn(u) > 1: continue
    f = min(mp.sqrt((u[0]-c[0])**2+(u[1]-c[1])**2) for c in cent)
    rows.append((f, tri, u))
rows.sort(key=lambda z: -z[0])
W(f"  triples with circumcentre in D: {len(rows)}")
W("  deepest 16:")
for f, tri, u in rows[:16]:
    typ = ''.join('H' if i < 3 else ('M' if i < 6 else 'R') for i in tri)
    W(f"    tri{str(tri):<14} {typ:<4} f={mp.nstr(f,24)}  f-r={mp.nstr(f-r,6)}  |u|={mp.nstr(nn(u),14)}")
W("")
worst = rows[0][0]
W(f"  deepest interior hole f_max = {mp.nstr(worst,26)}")
W(f"  vs certified r             = {mp.nstr(r,26)}")
W(f"  difference f_max - r       = {mp.nstr(worst-r,8)}")
W("")
# boundary
W("### boundary caps: max_{|x|=1} min_i |x - c_i|")
N = 8_000_000
bb = (-1, None)
for s in range(N):
    th = 2*mp.pi*s/N
    p = (mp.cos(th), mp.sin(th))
    d = min(mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in cent)
    if d > bb[0]: bb = (d, th)
W(f"  f_max(boundary) = {mp.nstr(bb[0],26)} at theta_deg={mp.nstr(bb[1]*180/mp.pi,12)}")
W(f"  r - f_max(boundary) = {mp.nstr(r-bb[0],8)}")
W("")
W("### also: which centres are ever nearest on S1 (boundary-active)")
own = set()
for s in range(400000):
    th = 2*mp.pi*s/400000
    p = (mp.cos(th), mp.sin(th))
    ds = [mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in cent]
    own.add(ds.index(min(ds)))
W(f"  nearest owners on S1: {sorted(own)}   ({len(own)} centres)")
W(f"  => boundary-ACTIVE disks: {len(own)}; the hub orbit {{0,1,2}} is interior")
W("")
W("### SUMMARY")
W(f"  R_D(ideal chart config) = max(interior deepest hole, boundary cap max)")
W(f"     = max({mp.nstr(worst,24)}, {mp.nstr(bb[0],24)}) = {mp.nstr(max(worst,bb[0]),24)}")
W(f"  certified chart radius r  = {mp.nstr(r,24)}")
W(f"  difference               = {mp.nstr(max(worst,bb[0])-r,6)}")
(EV / "coverage_ideal2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
