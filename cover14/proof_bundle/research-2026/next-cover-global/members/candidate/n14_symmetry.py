"""n=14 candidate: exact symmetry analysis + reduced exactification entry point.

The profile shows n=14 has a 180-degree rotation symmetry (residual 7.7e-10) and a
suggested mirror at 90 deg, while n=13/15 have NO symmetry (residuals 1.1e-2 / 9.2e-2).
This script tests the exact C2 action index-wise, extracts the symmetry-reduced
parameterisation (a 7-point fundamental domain), and checks the hole/contact structure
in the reduced variables.
"""
from pathlib import Path
from fractions import Fraction as F
import json, itertools
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
S2 = ROOT / "research-2026/session2/n1314"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""): OUT.append(str(s))

cfg = json.loads((S2 / "cfg/cert_n14_v1.json").read_text(encoding="utf-8"))
Aq = [(F(x), F(y)) for x, y in cfg["centers_dec17"]]
Am = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in cfg["centers_dec17"]]
n = 14
R = mp.mpf(cfg["R_float"])
W(f"### n=14 literal config, R_float = {mp.nstr(R,30)}")
W("")
# 1. index-wise C2 action: find the permutation
W("### 1. C2 (180 deg = x -> -x) action, index-wise")
perm = []
for i in range(n):
    q = (-Am[i][0], -Am[i][1])
    d, j = min((mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2), t) for t, c in enumerate(Am))
    perm.append(j)
    W(f"   c_{i:2d} -> -c_{i:2d} = ({mp.nstr(q[0],18)}, {mp.nstr(q[1],18)})  closest c_{j:2d}  dist={mp.nstr(d,8)}")
W(f"   permutation = {perm}")
W(f"   is an involution: {all(perm[perm[i]] == i for i in range(n))}")
W(f"   fixed points: {[i for i in range(n) if perm[i] == i]}")
W("")
# 2. mirror at 90 deg: (x,y) -> (-x,y)
W("### 2. reflection about the y-axis: (x,y) -> (-x,y)")
perm2 = []
for i in range(n):
    q = (-Am[i][0], Am[i][1])
    d, j = min((mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2), t) for t, c in enumerate(Am))
    perm2.append(j)
W(f"   permutation = {perm2}")
W(f"   max distance = {mp.nstr(max(min(mp.sqrt(((-Am[i][0]-c[0])**2+(Am[i][1]-c[1])**2),) for c in Am) for i in range(n)),8)}")
mx = mp.mpf(0)
for i in range(n):
    q = (-Am[i][0], Am[i][1])
    mx = max(mx, min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in Am))
W(f"   worst residual = {mp.nstr(mx,8)}  ({'EXACT to literal' if mx < 1e-15 else 'NOT exact'})")
W("")
# 3. the C2 orbit structure
W("### 3. C2 orbits (size 1 or 2)")
seen, orbs = set(), []
for i in range(n):
    if i in seen: continue
    o = [i] if perm[i] == i else sorted([i, perm[i]])
    orbs.append(o); seen.update(o)
W(f"   {len(orbs)} orbits: {orbs}")
W("")
# 4. reduced coordinates: for each orbit, |c|, angle; for pairs, the geometric invariants
W("### 4. symmetry-reduced invariants (R, and for each orbit: |c|, angle, and the pair's "
  "separating vector)")
W(f"   {'orbit':<10} {'|c|':<26} {'angle_deg':<20} note")
for o in orbs:
    i = o[0]
    rho = mp.sqrt(Am[i][0]**2+Am[i][1]**2)
    th = mp.atan2(Am[i][1], Am[i][0])*180/mp.pi
    note = ""
    if len(o) == 2:
        j = o[1]
        note = (f"|c_i-c_j|={mp.nstr(mp.sqrt((Am[i][0]-Am[j][0])**2+(Am[i][1]-Am[j][1])**2),22)}"
                f"  angle_i=({mp.nstr(th,12)}, {mp.nstr(mp.atan2(Am[j][1],Am[j][0])*180/mp.pi,12)})")
    else:
        # fixed point under C2 => must lie at the origin OR on the boundary of being fixed
        note = "FIXED under 180 deg rotation => must be the origin"
    W(f"   {str(o):<10} {mp.nstr(rho,26):<26} {mp.nstr(th,18):<20} {note}")
W("")
# 5. boundary-active and interior split (from the earlier profile)
W("### 5. structure split (from the numeric profile)")
W("   boundary-active disks: {4,...,13}  (10 disks)")
W("   interior disks:        {0,1,2,3}  (4 disks)")
W("   shells: 2x|c|=0.3886 (interior), 2x0.3268 (interior), 4x0.7808 (boundary),")
W("           4x0.8916 (boundary), 2x0.9434 (boundary)")
W("   => shell multiplicities 4+4+2 (boundary) and 2+2 (interior) are exactly the C2-invariant pattern")
W("")
# 6. deepest hole structure
W("### 6. deepest holes of n=14 (top 8) and their C2 orbits")
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(float(den)) < 1e-14: return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den)
verts = []
for tri in itertools.combinations(range(n), 3):
    u = circ(Am[tri[0]], Am[tri[1]], Am[tri[2]])
    if u is None: continue
    if u[0]*u[0]+u[1]*u[1] > 1: continue
    dd = sorted((mp.sqrt((u[0]-c[0])**2+(u[1]-c[1])**2), t) for t, c in enumerate(Am))
    verts.append((dd[0][0], tri, u, [t for _, t in dd[:4]]))
verts.sort(key=lambda z: -z[0])
for f, tri, u, near in verts[:10]:
    u2 = (-u[0], -u[1])
    d, j2 = min((mp.sqrt((u2[0]-c[0])**2+(u2[1]-c[1])**2), t) for t, c in enumerate(Am))
    W(f"   tri{str(tri):<18} f={mp.nstr(f,24)}  f-R={mp.nstr(f-R,6)}  near={near}"
      f"  (C2 image nearest c_{j2} at dist {mp.nstr(d,6)})")
W("")
W("### 7. count of active holes vs coordinates (KKT degree-of-freedom count)")
act = [v for v in verts if abs(v[0]-R) < 1e-14]
W(f"   holes with f == R (to 1e-14): {len(act)}")
W(f"   holes with f < R by more than 1e-6: {len([v for v in verts if v[0] < R-1e-6])}")
W("")
W("### 8. WRITE-UP: n=13 vs n=14 vs n=15 comparison for a generic global method")
tbl = [
    ("n", "R_literal", "boundary-active", "interior", "symmetry", "shells", "#holes",
     "deepest-hole slack", "best reflection"),
    ("13", "0.34664545692738974", "10", "3", "NONE (1.1e-2)", "13 distinct", "237",
     "-4.1e-17", "0.0113"),
    ("14", "0.3317320342762342", "10", "4", "C2 180deg (7.7e-10)", "13 (2+2+4+4+2)", "296",
     "-5.3e-17", "2.15e-4"),
    ("15", "0.31814293085926293", "11", "4", "NONE (9.2e-2)", "15 distinct", "377",
     "-6.1e-17", "0.0924"),
]
w0 = [max(len(str(r[i])) for r in tbl) for i in range(len(tbl[0]))]
for r in tbl:
    W("   " + "  ".join(str(x).ljust(w0[i]) for i, x in enumerate(r)))
(EV / "n14_symmetry.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
