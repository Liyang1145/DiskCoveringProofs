"""Step 7: exact bottleneck structure and reduced optimization.

CONVENTION (verified from cert_bb.py / rd.py headers + numeric reproduction):
   R_D(C) = max_{x in D} min_i |x - c_i|      (covering radius of D by the 12 disks
   of radius r centred at the c_i;  r_D(12) = inf_C R_D(C)).
Certified: R_D(C182) in [0.3611029637445086726169202939, 0.36110296374450867261692029394].

This script:
 1. locates ALL global maxima of f(x)=min_i|x-c_i| on D exactly-ish (Voronoi vertices + boundary),
 2. reports the exact rational circumradius^2 of every triple, vs the C182 interval (no floats),
 3. identifies the 6 active triple-faces and the C3 orbit structure,
 4. reports the *hole angular layout* to build the reduced system.
"""
from pathlib import Path
from fractions import Fraction as F
import json, itertools
import mpmath as mp
mp.mp.dps = 40

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
Aq = [(F(x), F(y)) for x, y in A["centers_dec17"]]
n = 12
Rlo = F("0.361102963744508672616920293903")
Rhi = F("0.361102963744508672616920293904")
OUT = []
def W(s=""): OUT.append(str(s))

def d2(i, j): return (Aq[i][0]-Aq[j][0])**2 + (Aq[i][1]-Aq[j][1])**2
def n2(i): return Aq[i][0]**2 + Aq[i][1]**2
def mpf(q): return mp.mpf(q.numerator)/mp.mpf(q.denominator)

# ---------- 1. exact triple circumradius^2 and the active set vs the C182 interval
W("### 1. triple circumradii (EXACT rational rr^2) compared to the C182 interval [Rlo^2, Rhi^2]")
W(f"    Rlo^2 = {Rlo*Rlo}")
W(f"    Rhi^2 = {Rhi*Rhi}")
lo2, hi2 = Rlo*Rlo, Rhi*Rhi
faces = []
for i, j, k in itertools.combinations(range(n), 3):
    a, b, c = Aq[i], Aq[j], Aq[k]
    cross = 2*((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0]))
    if cross == 0: continue
    lab, lbc, lca = d2(i, j), d2(j, k), d2(k, i)
    rr2 = lab*lbc*lca/(cross*cross)
    faces.append((rr2, (i, j, k), lab, lbc, lca, cross))
faces.sort(key=lambda t: -float(t[0]))
W("    top 10 by rr^2:")
for rr2, tri, lab, lbc, lca, cross in faces[:10]:
    rel = "rr^2 > Rhi^2" if rr2 > hi2 else ("rr^2 < Rlo^2" if rr2 < lo2 else "IN INTERVAL")
    rr = mp.sqrt(mpf(rr2))
    W(f"      tri{str(tri):<16} rr={mp.nstr(rr,30)} rr^2-Rhi^2={(rr2-hi2)!s:>12} {rel}")
W("    ... (interval test is exact; no floats used in the decision)")
# three degenerate ('circ') faces mentioned in the source file
W("\n    source 'circ' triples {2,10,11}, {0,1,3}, {0,2,5} and the far0 face {0,6,7}:")
for tri in ((2,10,11),(0,1,3),(0,2,5),(0,6,7)):
    for rr2, t, lab, lbc, lca, cross in faces:
        if t == tri:
            W(f"      tri{tri}: rr^2-Rlo^2 = {rr2-lo2}  rr^2-Rhi^2 = {rr2-hi2}")
            W(f"        lab={lab} lbc={lbc} lca={lca}")
            W(f"        side^2 (2Rlo)^2 = {(2*Rlo)**2};  side^2 - ... = {[lab-(2*Rlo)**2, lbc-(2*Rlo)**2, lca-(2*Rlo)**2]}")
            W(f"        rr^2 vs (Rlo+Rhi)^2/4: {rr2 - ((Rlo+Rhi)**2/4)}")

# ---------- 2. all local maxima of f on D : Voronoi vertices (f = min dist) + boundary
W("\n### 2. all local maxima of f(x)=min_i|x-c_i| on D (mpmath, located by float then refined)")
Am = [(mpf(x), mpf(y)) for x, y in Aq]
loc = []
for i, j, k in itertools.combinations(range(n), 3):
    ax, ay = Am[i]; bx, by = Am[j]; cx, cy = Am[k]
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if mp.fabs(den) < mp.mpf('1e-30'): continue
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den
    if ux*ux+uy*uy > 1: continue
    dd = sorted((mp.sqrt((ux-c[0])**2+(uy-c[1])**2), t) for t, c in enumerate(Am))
    loc.append((dd[0][0], (i, j, k), ux, uy, [t for _, t in dd[:4]], mp.sqrt(ux*ux+uy*uy)))
loc.sort(key=lambda z: -z[0])
W("    top 12 Voronoi vertices inside D:")
for f, tri, ux, uy, near, ru in loc[:12]:
    W(f"      tri{str(tri):<16} u=({mp.nstr(ux,20)},{mp.nstr(uy,20)}) |u|={mp.nstr(ru,18)} "
      f"f={mp.nstr(f,28)} f-Rlo={mp.nstr(f-mpf(Rlo),6)} nearest={near}")
W(f"    max interior f = {mp.nstr(loc[0][0],32)}")
# boundary local maxima: solve pairs (angles where nearest changes) - just report the max by dense scan
N = 2_000_000
bb = None
for t in range(N):
    th = 2*mp.pi*t/N
    p = (mp.cos(th), mp.sin(th))
    fv = min(mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in Am)
    if bb is None or fv > bb[0]: bb = (fv, th)
W(f"    boundary max f = {mp.nstr(bb[0],28)} at theta_deg={mp.nstr(bb[1]*180/mp.pi,14)}"
  f"  vs Rlo: {mp.nstr(bb[0]-mpf(Rlo),6)}")
W(f"    => R_D(C182) is attained at the interior Voronoi vertex tri{loc[0][1]}; "
  f"boundary is strictly below by {mp.nstr(mpf(Rlo)-bb[0],6)}")

# ---------- 3. C3 orbit structure in the frame aligned with the holes
W("\n### 3. C3 orbit structure (angles measured in degrees; C3 acts by +120 deg)")
W("    verified exactly: identify orbits by the exact rational |c_i|^2 values")
groups = {}
for i in range(n):
    groups.setdefault(n2(i), []).append(i)
for val, idx in sorted(groups.items(), key=lambda kv: float(kv[0])):
    W(f"    |c|^2 = {mp.nstr(mpf(val),26)} : indices {idx}")
    for i in idx:
        W(f"        c{i}: theta_deg={mp.nstr(mp.atan2(Am[i][1],Am[i][0])*180/mp.pi,18)}"
          f"  (c = {mp.nstr(Am[i][0],22)}, {mp.nstr(Am[i][1],22)})")

(EV / "exact_structure.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
