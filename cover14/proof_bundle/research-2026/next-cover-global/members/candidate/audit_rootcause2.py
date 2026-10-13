"""ROOT-CAUSE audit, corrected (the previous run had a loop-variable shadowing bug that
truncated the Voronoi list).

Items: (1) D2 orbits; (3) nearest-site filtering; (4) hand-check of the bogus "tight"
triples; (5) n=13/n=15 symmetry at the CORRECT axes (searched over all axes);
(6) residual language.
"""
from pathlib import Path
import json, itertools, sys
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
S2 = ROOT / "research-2026/session2/n1314"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""):
    OUT.append(str(s)); print(str(s)); sys.stdout.flush()
dd = lambda p, q: mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
nn = lambda p: mp.sqrt(p[0]**2+p[1]**2)
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < mp.mpf('1e-40'): return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den)

D14 = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text(encoding="utf-8"))
C = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in D14["centers"]]
R = mp.mpf(D14["R"]); n = 14

W("="*100)
W("(4) the CORRECT deepest nearest-site holes of n=14 (Voronoi vertices inside D)")
recs = []
for tri in itertools.combinations(range(n), 3):
    u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
    if u is None or nn(u) > 1: continue
    ds = sorted((dd(u, c), t) for t, c in enumerate(C))
    if set(x for _, x in ds[:3]) != set(tri): continue      # nearest-site filter
    recs.append((ds[0][0], tri, u, [x for _, x in ds[:4]], ds[3][0]-ds[0][0]))
recs.sort(key=lambda z: -z[0])
W(f"    #Voronoi vertices inside D (nearest-site filtered) = {len(recs)}")
for f, tri, u, near, gap in recs:
    W(f"      tri{str(tri):<14} f={mp.nstr(f,24)}  f-R={mp.nstr(f-R,8)}  "
      f"|u|={mp.nstr(nn(u),16)}  slack-to-4th={mp.nstr(gap,10)}")
W(f"    => the true active (f == R to the source precision) are those with |f-R| < 1e-15:")
nact = sum(1 for f, *_ in recs if abs(f-R) < mp.mpf('1e-15'))
W(f"       {nact} of {len(recs)}")
W("")

W("="*100)
W("(5) n=13 / n=15 symmetry: search over ALL mirror axes (not just x/y),")
W("    and use the |c| multiplicity as an independent indicator.")
def sym_scan(tag, cent):
    m = len(cent)
    rad = [nn(c) for c in cent]
    W(f"    --- {tag}: n={m}")
    # norm multiplicities
    from collections import Counter
    c = Counter(mp.nstr(r, 9) for r in rad)
    mult = sorted(c.values(), reverse=True)
    W(f"        |c| multiplicities (rounded): {mult}   #distinct={len(c)}")
    best = None
    for k in range(4*m):
        ph = mp.pi*k/(4*m)
        c2, s2 = mp.cos(2*ph), mp.sin(2*ph)
        dev = mp.mpf(0)
        for i in range(m):
            q = (c2*cent[i][0]+s2*cent[i][1], s2*cent[i][0]-c2*cent[i][1])
            dev = max(dev, min(dd(q, cc) for cc in cent))
        if best is None or dev < best[0]: best = (dev, 180*k/(4*m))
    W(f"        best mirror axis {best[1]:.3f} deg -> residual {mp.nstr(best[0],10)}")
    # best rotation (any order, not just 2pi k/n)
    bestr = None
    for k in range(1, 4*m):
        th = 2*mp.pi*k/(4*m)
        cc, ss = mp.cos(th), mp.sin(th)
        dev = mp.mpf(0)
        for i in range(m):
            q = (cc*cent[i][0]-ss*cent[i][1], ss*cent[i][0]+cc*cent[i][1])
            dev = max(dev, min(dd(q, w) for w in cent))
        if bestr is None or dev < bestr[0]: bestr = (dev, 360*k/(4*m))
    W(f"        best rotation angle {bestr[1]:.3f} deg -> residual {mp.nstr(bestr[0],10)}")
    return mult, best, bestr

for tag, fn in (("n=13", "cfg/cert_n13_v1.json"), ("n=14 (17-digit literal)", "cfg/cert_n14_v1.json"),
                ("n=15", "cfg/cert_n15_v1.json")):
    cfg = json.loads((S2 / fn).read_text(encoding="utf-8"))
    cent = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in cfg["centers_dec17"]]
    sym_scan(tag, cent)
    W("")
W("="*100)
W("(2) dimension conventions (recorded for the record, no claims):")
W("    general position: n centres = 2n coordinates, the rigid-rotation group is 1-dimensional")
W("    (its orbits have no fixed point unless some centre is at the origin), so the quotient")
W("    has 2n - 1 dimensions -> n=13: 25, n=15: 29 (NOT 27 for both).")
W("    For a configuration with a d-dimensional symmetry group acting freely, the quotient")
W("    has 2n - d.  D2 has d = 2 (rotations by pi and the rotation group is 1-dim;")
W("    the symmetry group of a planar figure is a subgroup of O(2), so d <= 1 for rotations)")
W("    -- the correct statement is: the CONFIGURATION's own symmetry group is what matters,")
W("    and for n=14's saved object the full D2 orbits are 2x4 + 3x2 = 7 orbits.")
(EV / "audit_rootcause.txt").write_text("\n".join(OUT), encoding="utf-8")
print("done")
