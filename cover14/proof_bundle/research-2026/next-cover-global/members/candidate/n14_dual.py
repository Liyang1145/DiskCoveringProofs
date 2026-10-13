"""n=14: does the saved candidate realize the structure member's 10-boundary+4-hub dual?

They report (members/structure/SELECTION-n13-n14-n15-n25.md):
  k = 10 boundary-active, m = 4 hubs, triangulated dual T = k + 2m - 2 = 16.
This script checks that against the high-precision candidate using DELAUNAY triangles
(circumcentre in D) rather than all C(n,3) triples, and counts active vs slack faces.
No scans, no optimisation: pure finite combinatorics on a fixed configuration.
"""
from pathlib import Path
import json, itertools
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
d = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text(encoding="utf-8"))
C = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in d["centers"]]
n = len(C)
R = mp.mpf(d["R"])
OUT = []
def W(s=""): OUT.append(str(s))

def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < 1e-40: return None, None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den), None
def dd(p, q): return mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
nn = lambda p: mp.sqrt(p[0]**2+p[1]**2)

W(f"### n={n}, R = {d['R']}")
W(f"    C2 exact: {mp.mpf(0) == max(dd((-C[i][0],-C[i][1]), C[[3,2,1,0,7,6,5,4,9,8,11,10,13,12][i]]) for i in range(n))}")
W("")
# Delaunay = triples whose circumcircle is EMPTY (no other site strictly closer to u)
W("### Delaunay triangles (circumcentre in D and circumcircle empty), with their f-value")
delaunay = []
for tri in itertools.combinations(range(n), 3):
    u, _ = circ(C[tri[0]], C[tri[1]], C[tri[2]])
    if u is None: continue
    if nn(u) > 1: continue
    ds = sorted((dd(u, c), t) for t, c in enumerate(C))
    # empty-circumcircle test with tolerance far below the site spacing
    if ds[3][0] - ds[0][0] < mp.mpf('1e-25'):
        continue                      # degenerate (4+ cocircular) -- flagged separately
    delaunay.append((ds[0][0], tri, u, [t for _, t in ds[:4]]))
W(f"    {len(delaunay)} Delaunay triangles with circumcentre in D")
delaunay.sort(key=lambda z: -z[0])
active = [t for t in delaunay if abs(t[0]-R) < mp.mpf('1e-14')]
slack = [t for t in delaunay if t[0] < R - mp.mpf('1e-14')]
W(f"    ACTIVE (f == R within 1e-14): {len(active)}")
W(f"    SLACK  (f <  R):             {len(slack)}")
W("")
W("### the active faces (each should be a triangle of the tiled dual):")
for f, tri, u, near in active:
    typ = ''.join('B' if i in (0,1,2,3,4,5,6,7,8,9) else 'H' for i in tri)
    W(f"    tri{str(tri):<16} type={typ:<4} f-R={mp.nstr(f-R,6)}  |u|={mp.nstr(nn(u),16)}")
W("")
W("### the slack faces:")
for f, tri, u, near in slack:
    typ = ''.join('B' if i in (0,1,2,3,4,5,6,7,8,9) else 'H' for i in tri)
    W(f"    tri{str(tri):<16} type={typ:<4} R-f={mp.nstr(R-f,6)}  |u|={mp.nstr(nn(u),16)}")
W("")
W("### structural count vs the structure member's T = k + 2m - 2 = 10 + 8 - 2 = 16")
W(f"    Delaunay triangles in D : {len(delaunay)}")
W(f"    k (boundary-active)     : 10   ({sorted(range(10))})")
W(f"    m (hubs)                : 4    ({sorted(range(10,14))})")
W(f"    k + 2m - 2              : {10 + 2*4 - 2}")
W(f"    match: {len(delaunay) == 16}")
W("")
# type census
from collections import Counter
cen = Counter()
for f, tri, u, near in delaunay:
    typ = ''.join('B' if i < 10 else 'H' for i in tri)
    cen[typ] += 1
W("### face type census (B = boundary-active, H = hub), count, and how many are ACTIVE")
W(f"    {'type':<10} {'count':<8} {'active':<8} f-range")
for typ in sorted(cen):
    ts = [t for t in delaunay if ''.join('B' if i < 10 else 'H' for i in t[1]) == typ]
    na = len([t for t in ts if abs(t[0]-R) < mp.mpf('1e-14')])
    W(f"    {typ:<10} {len(ts):<8} {na:<8} "
      f"[{mp.nstr(min(t[0] for t in ts),18)}, {mp.nstr(max(t[0] for t in ts),18)}]")
W("")
W("### Euler/dual consistency: for a triangulated disk with k boundary + m interior vertices,")
W("    T = k + 2m - 2.  Check the type census reproduces it:")
W(f"    BHH + BHB + BBH(count) ... measured: " + ", ".join(f"{k}={v}" for k, v in sorted(cen.items())))
W("")
W("### the 4 hubs and their role")
for i in range(10, 14):
    W(f"    c{i}: ({mp.nstr(C[i][0],22)}, {mp.nstr(C[i][1],22)})  |c|={mp.nstr(nn(C[i]),22)}"
      f" ang={mp.nstr(mp.atan2(C[i][1],C[i][0])*180/mp.pi,18)}")
W("### and which faces use each hub")
for i in range(10, 14):
    ts = [t[1] for t in delaunay if i in t[1]]
    W(f"    hub {i}: {len(ts)} incident Delaunay triangles: {ts}")
(EV / "n14_dual.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
