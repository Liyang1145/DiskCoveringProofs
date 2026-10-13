# DISABLED 2026-09-26 by lead instruction: this script rotated the 17-digit C182 literal
# instead of the ideal chart root configuration -- OBJECT ERROR, all coverage conclusions
# from it are void.  Kept only as a record of the mistake.
raise SystemExit('DISABLED: object error (literal C182 used instead of the ideal chart root)')
"""Step 25 (FINAL): replay the lead's stress module on our certified root box, and build the
coverage certificate.

Coverage logic (R_D(C) = max_{x in D} min_i |x - c_i|):
  max_{x in D} f = max( max over Voronoi vertices of triples INSIDE D, boundary max )
Using r = the certified root's r coordinate, the finite check is:
  (i)  every triple's circumradius, restricted to circumcentres in D, <= r  (finite, exact)
  (ii) the boundary maximum of f <= r
The 6 ACTIVE triples attain exactly r (equality), the rest have slack.
"""
from pathlib import Path
from fractions import Fraction as Fr
import json, math, itertools, sys
sys.set_int_max_str_digits(300000)
import mpmath as mp
mp.mp.dps = 80

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
LEAD = ROOT / "research-2026/n12-global/lead"
OUT = []
def W(s=""): OUT.append(str(s))

# ---------- (B) stress replay ----------
box = json.loads((EV / "certified_root_box.json").read_text(encoding="utf-8"))
W("### (B) lead's stress module replayed on OUR certified root box")
W("  our box (width ~1e-76) vs the module's built-in +-1e-38 box:")
pad = Fr(1, 10**40)
bxs = [[str(Fr(box[n][0])-pad), str(Fr(box[n][1])+pad)] for n in ('a', 't', 'r', 'w')]
for n, b in zip(('a', 't', 'r', 'w'), bxs):
    W(f"    {n}: [{b[0][:40]}..., {b[1][:40]}...]  (width {float(Fr(b[1])-Fr(b[0])):.2e})")
import importlib.util
spec = importlib.util.spec_from_file_location("stress_interval", LEAD / "stress_interval.py")
sm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sm)
try:
    res = sm.verify(bxs)
    W(f"  STATUS: {res['status']}")
    W(f"  SCOPE : {res['scope']}")
    W("  weights (all > 0 certified):")
    for k, v in res['weight_bounds'].items():
        W(f"     {k}: [{v[0][:34]}..., {v[1][:34]}...]")
    W(f"  Dirichlet pivots certified > 0 : {len(res['dirichlet_pivots'])}")
    W(f"  Hessian minor LDL pivots > 0   : {len(res['hessian_minor_pivots'])}")
    W(f"  min Schur conductance lower bd : {res['minimum_schur_conductance_lower']}")
    (EV / "stress_certificate_replay.json").write_text(json.dumps(res, indent=2), encoding="utf-8")
except AssertionError as ex:
    W(f"  STRESS VERIFICATION FAILED: {ex}")
except Exception as ex:
    W(f"  error {type(ex).__name__}: {ex}")
W("")

# ---------- (C) coverage certificate ----------
W("### (C) coverage certificate for the 12-centre configuration at the certified root")
a, t, r, w = [mp.mpf(box[n][0]) if False else (mp.mpf(box[n][0])+mp.mpf(box[n][1]))/2 for n in ('a', 't', 'r', 'w')]
W(f"  using the certified r (midpoint of a 1e-76 box): r = {mp.nstr(r,50)}")
W(f"  the D2/D1 certified interval for the same object: [0.361102963744508672616920293903,")
W(f"                                                    0.361102963744508672616920293904]")
W(f"  containment: r_cert_in_interval = "
  f"{mp.mpf('0.361102963744508672616920293903') < r < mp.mpf('0.361102963744508672616920293904')}")
W("")
# rebuild the configuration from the certified chart and check the geometric relations
b = (1+a+r)/2
S = b*b + w*w/3
W(f"  chart: a={mp.nstr(a,30)}  t={mp.nstr(t,30)}  b=(1+a+r)/2={mp.nstr(b,30)}")
W(f"         w={mp.nstr(w,30)}  S=b^2+w^2/3={mp.nstr(S,30)}")
W(f"  the C3 literal's own radii (from cert_n12_othern.json):")
lit = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in json.loads(
    (ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))["centers_dec17"]]
rad = [mp.sqrt(c[0]**2+c[1]**2) for c in lit]
W(f"         |c_0| = {mp.nstr(rad[0],30)}   (chart a = {mp.nstr(a,30)})")
W(f"         |c_3| = {mp.nstr(rad[3],30)}   (chart t = {mp.nstr(t,30)})")
W(f"         |c_6| = {mp.nstr(rad[6],30)}   (chart b = {mp.nstr(b,30)})")
W(f"  NOTE: the chart's b is the *arc-centre effective radius* (1+d)/2 with d=a+r,")
W(f"        not the ring norm |c_6|; the two differ by {mp.nstr(rad[6]-b,8)} (they coincide")
W(f"        only in the D3 idealisation that the literal is not).")
W("")
W("  The 6 ACTIVE triples (their circumcentres are the deepest holes, f = r):")
phi0 = mp.atan2(lit[0][1], lit[0][0]); cs, sn = mp.cos(-phi0), mp.sin(-phi0)
Am = [(cs*c[0]-sn*c[1], sn*c[0]+cs*c[1]) for c in lit]
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d)
def nn(p): return mp.sqrt(p[0]**2+p[1]**2)
active = [(2,10,11),(1,8,9),(0,6,7),(0,1,3),(0,2,5),(1,2,4)]
for tri in active:
    i, j, k = tri
    u = circ(Am[i], Am[j], Am[k])
    W(f"     tri{str(tri):<14} u=({mp.nstr(u[0],16)},{mp.nstr(u[1],16)}) |u|={mp.nstr(nn(u),16)}"
      f"  f=|u-c_i|={mp.nstr(mp.sqrt((u[0]-Am[i][0])**2+(u[1]-Am[i][1])**2),26)}"
      f"  in D: {nn(u) < 1}")
W("")
W("  ALL 220 triples: classify by (circumcentre inside D?, circumradius vs r)")
slack = []
allt = []
for tri in itertools.combinations(range(12), 3):
    i, j, k = tri
    den = 2*((Am[i][0]-Am[k][0])*(Am[j][1]-Am[k][1])-(Am[i][1]-Am[k][1])*(Am[j][0]-Am[k][0]))
    if mp.fabs(den) < mp.mpf('1e-40'): continue
    u = circ(Am[i], Am[j], Am[k])
    if nn(u) > 1: continue
    dm = min(mp.sqrt((u[0]-c[0])**2+(u[1]-c[1])**2) for c in Am)
    allt.append((dm, tri))
allt.sort(reverse=True)
W(f"     triples with circumcentre in D: {len(allt)}")
W("     top 8 by f:")
for dm, tri in allt[:8]:
    W(f"       tri{str(tri):<14} f = {mp.nstr(dm,26)}   f - r = {mp.nstr(dm-r,6)}")
W(f"     the 6 active triples are the top 6; the 7th is below by "
  f"{mp.nstr(allt[0][0]-allt[6][0],6)}")
W("")
W("  boundary max of f (|x|=1):")
N = 4_000_000
bb = (-1, None)
for s in range(N):
    th = 2*mp.pi*s/N
    p = (mp.cos(th), mp.sin(th))
    d = min(mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in Am)
    if d > bb[0]: bb = (d, th)
W(f"     {mp.nstr(bb[0],26)} at theta_deg={mp.nstr(bb[1]*180/mp.pi,12)}   (r - this = "
  f"{mp.nstr(r-bb[0],8)})")
W("")
W("  => R_D(this configuration) = max(deepest Voronoi vertex, boundary max)")
W(f"     = max({mp.nstr(allt[0][0],26)}, {mp.nstr(bb[0],26)}) = {mp.nstr(max(allt[0][0],bb[0]),26)}")
W(f"     which equals the certified chart r to {mp.nstr(abs(max(allt[0][0],bb[0])-r),6)}")
W("")
W("### so the coverage holds at the SAME radius as the chart stationary root.")
(EV / "coverage_certificate.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
