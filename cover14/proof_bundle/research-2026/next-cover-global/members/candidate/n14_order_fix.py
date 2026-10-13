"""STRICT reconstruction of the n=14 candidate from hprec_sol.json 'th', using the
authoritative expansion in research-2026/lead/verify_c407_lead.py lines 185-195:

    th = [F(s) for s in js['th']]                       # 7 parameters
    C = []
    for j in (0, 2):
        for s in (-1, 1):
            for t in (-1, 1):
                C.append((s * th[j], t * th[j + 1]))    # 8 points: 2 rectangles
    for j in (4, 5):
        C.extend([(th[j], F(0)), (-th[j], F(0))])       # 4 points: two x-pairs
    C.extend([(F(0), th[6]), (F(0), -th[6])])           # 2 points: one y-pair
    # => 14 centres, indices 0..13 in this order

Then: (a) diff against the json's own 'centers' array (ORDER MAPPING),
      (b) recompute the 16 nearest-site Voronoi vertices inside D,
      (c) JOIN against the lead's n14-actual-vertices-numeric.json (per-coordinate and
          per-triple), and record source SHA-256.
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
W(f"### source SHA-256")
W(f"  {SRC.relative_to(ROOT)} : {sha}")
W(f"  {LEADR.relative_to(ROOT)} : {sha_lead}")
W("")
js = json.loads(SRC.read_text(encoding="utf-8"))
th = [F(s) for s in js["th"]]
W("### th (exact rationals from the decimal literals)")
for i, v in enumerate(th):
    W(f"  th[{i}] = {v}")
W(f"  th_names = {js['th_names']}")
W("")

# ---- authoritative expansion ----
Ct = []
for j in (0, 2):
    for s in (-1, 1):
        for t in (-1, 1):
            Ct.append((th[j], th[j+1], s, t))
W("### authoritative expansion (indices 0..13, before applying signs)")
for k, (x, y, s, t) in enumerate(Ct):
    W(f"  pre-idx {k:2d}: th[{0 if k < 4 else 2}], th[{1 if k < 4 else 3}] with (s,t)=({s:+d},{t:+d})")
W("")
Cx = []          # exact rational 14 centres in the AUTHORITATIVE order
k = 0
for j in (0, 2):
    for s in (-1, 1):
        for t in (-1, 1):
            Cx.append((s*th[j], t*th[j+1]))
for j in (4, 5):
    Cx.extend([(th[j], F(0)), (-th[j], F(0))])
Cx.extend([(F(0), th[6]), (F(0), -th[6])])
assert len(Cx) == 14, len(Cx)
W("### 14 centres in the AUTHORITATIVE expansion order (exact rationals)")
for i, (x, y) in enumerate(Cx):
    W(f"  C_script[{i:2d}] = ({x}, {y})")
W("")

# ---- (a) order mapping vs the json's own 'centers' array ----
sj = [(F(str(x)), F(str(y))) for x, y in js["centers"]]
W("### ORDER MAPPING: json['centers'] (file order) vs authoritative expansion")
W("    for each file-order index, the matching authoritative index")
mapping = []
for i, (x, y) in enumerate(sj):
    matches = [j for j, (u, v) in enumerate(Cx) if u == x and v == y]
    mapping.append(matches)
    W(f"  file_index {i:2d} = ({float(x):+.16f},{float(y):+.16f})  ->  script_index {matches}"
      f"   {'UNIQUE' if len(matches)==1 else 'AMBIGUOUS/ABSENT'}")
inv = {}
for i, ms in enumerate(mapping):
    if len(ms) == 1: inv[ms[0]] = i
W("")
W("    inverse (script index -> file index):")
for j in range(14):
    W(f"      script {j:2d} -> file {inv.get(j, 'ABSENT')}"
      f"   ({Cx[j][0]}, {Cx[j][1]})   |C|={mp.nstr(mp.sqrt(mp.mpf(F(Cx[j][0]))**2+mp.mpf(F(Cx[j][1]))**2) if False else mp.mpf(Cx[j][0].numerator)/mp.mpf(Cx[j][0].denominator),22)}")
W("")
json.dump({"sha256_primary": sha, "sha256_lead": sha_lead,
           "th": [str(v) for v in th],
           "expansion": "verify_c407_lead.py L185-195",
           "script_order_centers": [[str(x), str(y)] for x, y in Cx],
           "file_to_script_index": mapping},
          (EV / "n14_order_mapping.json").open("w"), indent=2)
W("written evidence/n14_order_mapping.json")
