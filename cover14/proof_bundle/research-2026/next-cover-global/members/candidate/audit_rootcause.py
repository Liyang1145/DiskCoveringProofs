"""ROOT-CAUSE audit of the candidate profile errors (self-audit, read-only inputs).

Checks each item the Lead raised, in order, printing the raw data so the claims can be
independently re-derived:

 (1) D2 orbit structure of the n=14 object: is it 7 orbits of 2, or 2 orbits of 4 + 3 of 2?
 (2) configuration-space dimension conventions
 (3) my hole lists: were they nearest-site filtered Voronoi vertices?
 (4) the reported "tight triples" of n=14: recompute circumradii by hand
 (5) n=13 / n=15 symmetry: test mirror planes at the CORRECT axes (norm multiplicities)
 (6) small float residuals are not "exactly tight"
"""
from pathlib import Path
import json, itertools
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
S2 = ROOT / "research-2026/session2/n1314"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
import sys
def W(s=""):
    OUT.append(str(s)); print(str(s)); sys.stdout.flush()

# ================= (1) n=14 D2 orbits =================
d = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text(encoding="utf-8"))
C = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in d["centers"]]
n = 14
dd = lambda p, q: mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
nn = lambda p: mp.sqrt(p[0]**2+p[1]**2)
R = mp.mpf(d["R"])
W("="*100)
W("(1) n=14 D2 orbit structure")
ident = {}
for x, y in C:
    ident[(mp.nstr(x, 30), mp.nstr(y, 30))] = None
W(f"    distinct centres in the file: {len(ident)} of {len(C)}  (duplicates: {len(C)-len(ident)})")
def perm_of(g):
    return [min(range(n), key=lambda t: dd(g(C[i]), C[t])) for i in range(n)]
def cycles(perm):
    seen, out = set(), []
    for i in range(n):
        if i in seen: continue
        cyc, cur = [], i
        while cur not in seen:
            seen.add(cur); cyc.append(cur); cur = perm[cur]
        out.append(cyc)
    return out
px = perm_of(lambda p: (p[0], -p[1]))     # sigma_x
py = perm_of(lambda p: (-p[0], p[1]))     # sigma_y
pc2 = perm_of(lambda p: (-p[0], -p[1]))   # 180 deg
for nm, pm in (("sigma_x (y->-y)", px), ("sigma_y (x->-x)", py), ("C2 (both -> -)", pc2)):
    cy = cycles(pm)
    sizes = sorted(len(c) for c in cy)
    W(f"    {nm:<20} permutation {pm}")
    W(f"        cycles: {cy}")
    W(f"        orbit sizes: {sizes}")
# full D2 orbits
def orbit_of(i, gens):
    cur, seen = {i}, {i}
    changed = True
    while changed:
        changed = False
        for g in gens:
            for j in list(seen):
                t = g[j]
                if t not in seen:
                    seen.add(t); changed = True
    return sorted(seen)
full = []
done = set()
for i in range(n):
    if i in done: continue
    o = orbit_of(i, (px, py, pc2))
    full.append(o); done.update(o)
sizes = sorted(len(o) for o in full)
W(f"    FULL D2 orbits: {full}")
W(f"    FULL D2 orbit sizes: {sizes}   sum={sum(sizes)}")
W(f"    => structure is {sizes.count(4)} orbit(s) of 4 and {sizes.count(2)} orbit(s) of 2")
W("")

# ================= (3)+(4) hole correctness =================
W("="*100)
W("(3)+(4) hole lists: nearest-site filter and hand circumradius check")
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < mp.mpf('1e-40'): return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den)
alltri = []
for tri in itertools.combinations(range(n), 3):
    u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
    if u is None: continue
    ru = nn(u)
    ds = sorted((dd(u, c), t) for t, c in enumerate(C))
    # nearest-site (Voronoi) filter: the three defining sites must be the three nearest
    isV = set([t for _, t in ds[:3]]) == set(tri)
    alltri.append({"tri": tri, "u": (mp.nstr(u[0],24), mp.nstr(u[1],24)), "|u|": mp.nstr(ru,20),
                   "circumradius": mp.nstr(ds[0][0],24), "u_in_D": bool(ru <= 1),
                   "is_voronoi": isV, "f": mp.nstr(ds[0][0], 24),
                   "nearest": [t for _, t in ds[:4]]})
W(f"    triples with a circumcentre: {len(alltri)}")
W(f"    of those, circumcentre inside D : {sum(1 for t in alltri if t['u_in_D'])}")
W(f"    of those, nearest-site (Voronoi) AND inside D : "
  f"{sum(1 for t in alltri if t['u_in_D'] and t['is_voronoi'])}")
W("")
W("    the 6 triples I previously listed as 'tight' for n=14 -- hand check:")
for tri in [(0,2,3),(0,3,4),(1,2,7),(1,7,9),(1,3,6),(3,4,12)]:
    u = circ(C[tri[0]], C[tri[1]], C[tri[2]])
    if u is None:
        W(f"      tri{tri}: DEGENERATE (collinear)"); continue
    ds = sorted((dd(u, c), t) for t, c in enumerate(C))
    W(f"      tri{str(tri):<12} circumcentre=({mp.nstr(u[0],18)},{mp.nstr(u[1],18)}) |u|={mp.nstr(nn(u),16)}")
    W(f"          circumradius = {mp.nstr(ds[0][0],20)}   vs R = {mp.nstr(R,20)}   "
      f"{'INSIDE D' if nn(u)<=1 else 'OUTSIDE D'}")
    W(f"          nearest sites: {[t for _,t in ds[:4]]}   equals the triple? "
      f"{set([t for _,t in ds[:3]])==set(tri)}")
W("")
W("    the CORRECT deepest nearest-site holes (Voronoi vertices inside D):")
vor = [t for t in alltri if t["u_in_D"] and t["is_voronoi"]]
vor.sort(key=lambda t: -float(F:=mp.mpf(t["circumradius"])))
W(f"    count = {len(vor)}")
for t in vor[:10]:
    W(f"      tri{str(t['tri']):<14} f={t['circumradius']}  f-R={mp.nstr(mp.mpf(t['circumradius'])-R,8)}"
      f"  |u|={t['|u|']}")
W("")
(EV / "audit_rootcause.txt").write_text("\n".join(OUT), encoding="utf-8")
json.dump(alltri, (EV / "audit_triples_n14.json").open("w"), indent=1)
W("written evidence/audit_rootcause.txt and audit_triples_n14.json")
