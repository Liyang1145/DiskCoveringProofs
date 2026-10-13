"""n=14 object fix, step 2: tolerance JOIN of
   (i)  the authoritative `th` expansion (verify_c407_lead.py L185-195), and
   (ii) json['centers'] (truncated decimal floats in the file), and
   (iii) the lead's independently computed vertices (lead/n14-actual-vertices-numeric.json).

Then recompute the 16 nearest-site Voronoi vertices inside D in the AUTHORITATIVE indexing
and join per-triple against the lead's list.

WHY the earlier join failed: the literals in json['centers'] are TRUNCATED (e.g.
0.6350958630468461 vs the exact th[0] = 0.6350958630468460467...), so exact rational
matching finds nothing.  Matching must be done at a tolerance that sits between the
truncation error (~5e-17) and the inter-centre separation (~0.48).
"""
from pathlib import Path
from fractions import Fraction as F
import json, itertools, hashlib, sys
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
SRC = ROOT / "research-2026/session2/type14/out/hprec_sol.json"
LEADR = ROOT / "research-2026/next-cover-global/lead/n14-actual-vertices-numeric.json"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""):
    OUT.append(str(s)); print(str(s)); sys.stdout.flush()

sha = hashlib.sha256(SRC.read_bytes()).hexdigest()
sha_lead = hashlib.sha256(LEADR.read_bytes()).hexdigest()
W("### sources")
W(f"  primary  {SRC.relative_to(ROOT)}")
W(f"           sha256 = {sha}")
W(f"  lead     {LEADR.relative_to(ROOT)}")
W(f"           sha256 = {sha_lead}")
W("")

js = json.loads(SRC.read_text(encoding="utf-8"))
th = [F(s) for s in js["th"]]
# authoritative expansion
Cx = []
for j in (0, 2):
    for s in (-1, 1):
        for t in (-1, 1):
            Cx.append((s*th[j], t*th[j+1]))
for j in (4, 5):
    Cx.extend([(th[j], F(0)), (-th[j], F(0))])
Cx.extend([(F(0), th[6]), (F(0), -th[6])])
assert len(Cx) == 14

def m(q): return mp.mpf(q.numerator)/mp.mpf(q.denominator)
CA = [(m(x), m(y)) for x, y in Cx]                       # authoritative (high precision)
CF = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in js["centers"]]   # file floats
dd = lambda p, q: mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
nn = lambda p: mp.sqrt(p[0]**2+p[1]**2)

# ---- (a) tolerance join  authoritative <-> file ----
TOL = mp.mpf('1e-12')
W("### (a) ORDER MAPPING  (script index -> file index), tolerance 1e-12")
mapping = []
for i in range(14):
    cands = [k for k in range(14) if dd(CA[i], CF[k]) < TOL]
    mapping.append(cands)
    W(f"  script {i:2d} ({mp.nstr(CA[i][0],20):>22},{mp.nstr(CA[i][1],20):>22})"
      f"  ->  file {cands}"
      f"   residual={mp.nstr(dd(CA[i], CF[cands[0]]),6) if len(cands)==1 else 'AMBIGUOUS'}")
perm = [c[0] for c in mapping]
W(f"  permutation (script->file) = {perm}")
W(f"  is the identity? {perm == list(range(14))}")
W(f"  max residual over the join = {mp.nstr(max(dd(CA[i], CF[perm[i]]) for i in range(14)),6)}"
  f"   (this IS the file's truncation error)")
W("")
W("### (a2) why the earlier exact join failed: truncation magnitude per centre")
for i in range(14):
    W(f"  script {i:2d}: exact x = {mp.nstr(CA[i][0],30)}")
    W(f"              file  x = {mp.nstr(CF[perm[i]][0],30)}   |diff| = {mp.nstr(abs(CA[i][0]-CF[perm[i]][0]),4)}")
W("")

# ---- (b) recompute the nearest-site Voronoi vertices inside D, authoritative indexing ----
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < mp.mpf('1e-50'): return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den)
mines = []
for tri in itertools.combinations(range(14), 3):
    u = circ(CA[tri[0]], CA[tri[1]], CA[tri[2]])
    if u is None or nn(u) > 1: continue
    ds = sorted((dd(u, c), t) for t, c in enumerate(CA))
    if set(x for _, x in ds[:3]) != set(tri): continue
    mines.append({"sites": list(tri), "q": [mp.nstr(u[0], 22), mp.nstr(u[1], 22)],
                  "radius": mp.nstr(ds[0][0], 22), "|q|": mp.nstr(nn(u), 20)})
mines.sort(key=lambda z: -float(mp.mpf(z["radius"])))
W(f"### (b) my nearest-site Voronoi vertices inside D (authoritative indexing): {len(mines)}")
for z in mines:
    W(f"  sites {str(z['sites']):<14} q=({z['q'][0]}, {z['q'][1]})  radius={z['radius']}  |q|={z['|q|']}")
W("")

# ---- (c) JOIN against the lead's list ----
lead = json.loads(LEADR.read_text(encoding="utf-8"))
Lc = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in lead["centers"]]
W("### (c1) centre-list join: lead's centres vs my authoritative expansion")
for i in range(14):
    best = min(range(14), key=lambda k: dd(CA[i], Lc[k]))
    W(f"  mine {i:2d} -> lead {best:2d}   residual {mp.nstr(dd(CA[i], Lc[best]),6)}")
W("")
W("### (c2) per-triple join of the vertex lists")
W(f"  lead 'actual' count = {len(lead['actual'])},  'tight' count = {len(lead['tight'])}")
mkey = {}
for z in mines:
    mkey[tuple(sorted(z["sites"]))] = z
W(f"  my count = {len(mines)}")
W("")
W("  {'lead sites':<16} {'my sites':<16} {'lead q':<44} {'my q':<44} {'|dq|':<12} {'lead r':<22} {'my r':<22}")
for z in lead["actual"]:
    key = tuple(sorted(z["sites"]))
    lq = (mp.mpf(str(z["q"][0])), mp.mpf(str(z["q"][1])))
    lr = mp.mpf(str(z["radius"]))
    mine = mkey.get(key)
    if mine is None:
        # try nearest-site-triple match by coordinates
        best = None
        for k2, zz in mkey.items():
            dq = dd(lq, (mp.mpf(zz["q"][0]), mp.mpf(zz["q"][1])))
            if best is None or dq < best[0]: best = (dq, k2, zz)
        W(f"  {str(z['sites']):<16} NO TRIPLE MATCH; nearest q: {str(best[1]):<16}"
          f" dq={mp.nstr(best[0],6)}")
        continue
    mq = (mp.mpf(mine["q"][0]), mp.mpf(mine["q"][1]))
    W(f"  {str(z['sites']):<16} {str(mine['sites']):<16}"
      f" ({mp.nstr(lq[0],18)},{mp.nstr(lq[1],18)})"
      f"  ({mp.nstr(mq[0],18)},{mp.nstr(mq[1],18)})"
      f"  {mp.nstr(dd(lq,mq),6):<12} {mp.nstr(lr,18):<22} {mine['radius']:<22}")
W("")
W("### (c3) summary statistics of the join")
ok = 0; tot = 0
for z in lead["actual"]:
    key = tuple(sorted(z["sites"]))
    if key in mkey:
        tot += 1
        dq = dd((mp.mpf(str(z['q'][0])), mp.mpf(str(z['q'][1]))),
                (mp.mpf(mkey[key]['q'][0]), mp.mpf(mkey[key]['q'][1])))
        if dq < mp.mpf('1e-12'): ok += 1
W(f"  lead entries matched by the same site triple: {tot}/{len(lead['actual'])}")
W(f"  of those, q agrees to 1e-12: {ok}")
W("")
json.dump({"sha256_primary": sha, "sha256_lead": sha_lead,
           "expansion_rule": "verify_c407_lead.py L185-195",
           "script_to_file_permutation": perm,
           "join_residual_max": mp.nstr(max(dd(CA[i], CF[perm[i]]) for i in range(14)), 6),
           "my_vertices": mines,
           "lead_vertices_count": {"actual": len(lead["actual"]), "tight": len(lead["tight"])}},
          (EV / "n14_join.json").open("w"), indent=2)
W("written evidence/n14_join.json")
