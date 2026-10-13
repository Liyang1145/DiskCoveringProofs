"""Step 6: definitive bottleneck + local-optimality structure for the literal cfg.

R_D(C) = max_{x in D} min_i |x-c_i|.  Certified interval (D2 replay):
   [0.3611029637445086726169202939, 0.36110296374450867261692029394]
Global max of f = max over Voronoi vertices inside D and over boundary arcs.
"""
from pathlib import Path
from fractions import Fraction as F
import json, math, itertools
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
cen = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in A["centers_dec17"]]
n = 12
Rlo = mp.mpf("0.3611029637445086726169202939")
Rhi = mp.mpf("0.36110296374450867261692029394")
OUT = []
def W(s=""): OUT.append(str(s))

W("### f(x) = min_i |x - c_i|  on D (covering-radius function of this configuration)")
W(f"certified R_D(C) interval: [{mp.nstr(Rlo,32)}, {mp.nstr(Rhi,32)}]")

# --- deep-hole (Voronoi vertex) enumeration, mpmath
holes = []
for i, j, k in itertools.combinations(range(n), 3):
    ax, ay = cen[i]; bx, by = cen[j]; cx, cy = cen[k]
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if mp.fabs(den) < mp.mpf('1e-40'): continue
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den
    if ux*ux+uy*uy > 1: continue
    dd = [(mp.sqrt((ux-c[0])**2+(uy-c[1])**2), t) for t, c in enumerate(cen)]
    dd.sort()
    holes.append({"tri": (i, j, k), "u": (ux, uy), "|u|": mp.sqrt(ux*ux+uy*uy),
                  "f": dd[0][0], "nearest": [t for _, t in dd[:4]],
                  "gap43": dd[3][0]-dd[0][0]})
holes.sort(key=lambda h: -h["f"])
W("\n### Voronoi vertices (deep holes) inside D, top 16 by f:")
for h in holes[:16]:
    W(f"  tri{str(h['tri']):<16} u=({mp.nstr(h['u'][0],18)},{mp.nstr(h['u'][1],18)}) |u|={mp.nstr(h['|u|'],16)}"
      f"  f={mp.nstr(h['f'],26)}  f-Rlo={mp.nstr(h['f']-Rlo,6)}  nn={h['nearest']}")
W(f"\n  max f over interior Voronoi vertices = {mp.nstr(holes[0]['f'],30)} on tri{holes[0]['tri']}")
# distinct deepest values
W("\n### distinct deep-hole values f (grouped to 1e-25):")
seen = []
for h in holes:
    for s in seen:
        if mp.fabs(s[0]-h['f']) < mp.mpf('1e-25'):
            s[1].append(h['tri']); break
    else:
        seen.append((h['f'], [h['tri']]))
for val, tris in seen[:10]:
    W(f"  f={mp.nstr(val,30)}  n_triples={len(tris)}  {tris}")
W("")
W("### boundary max-min f on |x|=1  (local max of min-dist on S1):")
N = 400_000
best = (-1, None)
for t in range(N):
    th = 2*mp.pi*t/N
    p = (mp.cos(th), mp.sin(th))
    d = min(mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in cen)
    if d > best[0]: best = (d, th)
W(f"  N={N}: max f = {mp.nstr(best[0],26)} at theta_deg={mp.nstr(best[1]*180/mp.pi,16)}"
  f"   vs Rlo: {mp.nstr(best[0]-Rlo,6)}")

W("")
W("### f at the origin (upper bound on 'hole with 12 neighbours'):")
f0 = min(mp.sqrt(c[0]**2+c[1]**2) for c in cen)
W(f"  f(0) = min_i |c_i| = {mp.nstr(f0,30)}   (far above R)")

# --- local optimality data at the deepest hole: which perturbations are blocked
W("")
W("### local optimality data at the deepest hole:")
h = holes[0]; u = h["u"]; tri = h["tri"]
W(f"  hole tri={tri} u=({mp.nstr(u[0],20)},{mp.nstr(u[1],20)})  f={mp.nstr(h['f'],26)}")
for t in range(N):
    d = mp.sqrt((u[0]-cen[t][0])**2+(u[1]-cen[t][1])**2)
    if d < Rhi + mp.mpf('1e-3'):
        W(f"    c{t:2d}: |u-c_t| - Rlo = {mp.nstr(d-Rlo,10)}   (dir from u: "
          f"{mp.nstr(mp.atan2(cen[t][1]-u[1], cen[t][0]-u[0])*180/mp.pi,12)} deg)")

# --- C3 orbit structure test at high precision
W("")
W("### C3 action test (exact rationals of the literal config)")
Aq = [(F(x), F(y)) for x, y in A["centers_dec17"]]
def rotq(p, k):
    # exact rational rotation by 2*pi*k/3 using cube roots of unity: represent
    # rotation by (x,y) -> (x cos - y sin, x sin + y cos) with cos=-1/2, sin=+-sqrt3/2
    # => NOT rational.  Instead report the algebraic displacement symbolically.
    return None
for k in (1, 2):
    W(f"  rot{k*120}deg: im(c_i) matched to nearest c_j with residual:")
    mx = mp.mpf(0); arg = None
    for i in range(n):
        th = 2*mp.pi*k/3
        q = (mp.cos(th)*cen[i][0]-mp.sin(th)*cen[i][1], mp.sin(th)*cen[i][0]+mp.cos(th)*cen[i][1])
        d, j = min((mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2), t) for t, c in enumerate(cen))
        if d > mx: mx, arg = d, (i, j)
    W(f"    max_i min_j = {mp.nstr(mx,20)}   worst (i->j) = {arg}")
W("  reflection tests:")
for phi_deg in (0, 30, 60, 90, 120, 150):
    ph = mp.pi*phi_deg/180
    c2, s2 = mp.cos(2*ph), mp.sin(2*ph)
    mx = mp.mpf(0)
    for i in range(n):
        q = (c2*cen[i][0]+s2*cen[i][1], s2*cen[i][0]-c2*cen[i][1])
        d = min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in cen)
        mx = max(mx, d)
    W(f"    axis{phi_deg:4d}deg: max_i min_j = {mp.nstr(mx,18)}")

(EV / "deep_holes.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
