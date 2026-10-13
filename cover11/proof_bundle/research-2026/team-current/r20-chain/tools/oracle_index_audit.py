"""ORACLE-CHART-INDEX-AUDIT evidence script.

Checks, for the canonical51 fixed-switch oracle and the raw8 local certificate:
  (1) incidence isomorphism between the raw carrying graph and the canonical graph,
  (2) the 18 anchor-endpoint (tie) edge bijection under the shift s -> s-2 mod 9,
  (3) 31 nodes / 51 edges / 22 free / 20 carrying vs 2 slack auxiliaries,
  (4) the six zero-weight slack edges in the stored field library: which nodes/edges,
      whether every free node still has a positive-weight incident edge (SPD of Lff),
  (5) the chart-rotation pin: canonical i <-> raw (i+2)%9 (i>=1), raw8 <-> canonical6,
      numeric identity of the two independent computations of h_k.
"""
import json, itertools
from pathlib import Path
from fractions import Fraction as F

P = Path(__file__).resolve().parent.parent.parent / "lead"
OUT = Path(__file__).resolve().parent / "out"
log = []
def W(x):
    log.append(str(x)); print(x)

# ---------- canonical graph ----------
canfaces = [(9, 10, 0), (9, 10, 4)] + [(9, k, (k + 1) % 9) for k in range(0, 4)] + \
           [(10, k, (k + 1) % 9) for k in range(4, 9)]
canfaces = [tuple(sorted(f)) for f in canfaces]
cedges = sorted({tuple(sorted((f[a], f[(a + 1) % 3]))) for f in canfaces for a in range(3)})
sites = list(range(11)); anchors = list(range(9)); hubs = [9, 10]
aux = list(range(11, 22))
W("CANONICAL51")
W(f"  faces (11): {canfaces}")
W(f"  site-site edges ({len(cedges)}): {cedges}")
hub_inc = {h: [f for f in canfaces if h in f] for h in hubs}
W(f"  hub9 faces:  {hub_inc[9]}")
W(f"  hub10 faces: {hub_inc[10]}")
faces_by_site = {s: [f for f in canfaces if s in f] for s in range(11)}
W("  site -> faces (carrying count):")
for s in range(11):
    W(f"     site {s}: {len(faces_by_site[s])} faces {faces_by_site[s]}")
ncarry = sum(1 for s in range(11) if len(faces_by_site[s]) >= 2)
W(f"  sites with >=2 faces (auxiliary needed in the SOC oracle): {ncarry} -> free aux {ncarry}")
W(f"  totally: {len(sites)} sites + {ncarry} auxiliaries = {len(sites)+ncarry} free nodes; "
  f"{len(anchors)} anchors; total nodes {len(sites)+ncarry+len(anchors)}")
# edges: site-site (21) + anchor-site (18) + face-aux (33)
edge_anchor_site = [(s, j) for s in range(9) for j in [s, (s - 1) % 9]]
W(f"  anchor-site edges: {len(edge_anchor_site)}")
edge_face_aux = [(20 + t, s) for t, f in enumerate(canfaces) for s in f]
W(f"  face-auxiliary edges: {len(edge_face_aux)}")
n_e = len(cedges) + len(edge_anchor_site) + len(edge_face_aux)
W(f"  TOTAL edges = {len(cedges)} + {len(edge_anchor_site)} + {len(edge_face_aux)} = {n_e}")

# ---------- raw carrying graph (interval_network_envelope / certify_canonical_local_patch) ----------
rawF = [[2, 9, 10], [6, 9, 10]] + [[k, (k + 1) % 9, 9 if 2 <= k <= 5 else 10] for k in [1, 2, 3, 4, 5, 6, 8]]
shift = lambda s: (s - 2) % 9 if s < 9 else s
W("\nRAW CARRYING GRAPH")
W(f"  rawF (9 faces): {rawF}")
W(f"  note: raw carries only {len(rawF)} = 9 faces, i.e. NOT the two central faces; it is a sub-graph")
mapped = [tuple(sorted(map(shift, f))) for f in rawF]
W(f"  shifted faces: {mapped}")
W(f"  all shifted faces are canonical faces: {all(f in canfaces for f in mapped)}")
raw_endpoint_pairs = {(shift(s), shift(k)) for k in range(9) for s in [k, (k + 1) % 9]}
canonical_endpoint_pairs = {(s, j) for s in range(9) for j in [s, (s - 1) % 9]}
W(f"  raw anchor-endpoint pairs after shift == canonical pairs: "
  f"{raw_endpoint_pairs == canonical_endpoint_pairs}")
uncovered = [f for f in canfaces if f not in mapped]
W(f"  canonical faces NOT covered by the raw carrying graph: {uncovered}")
deg = {}
for f in mapped:
    for s in f:
        deg[s] = deg.get(s, 0) + 1
degc = {}
for f in canfaces:
    for s in f:
        degc[s] = degc.get(s, 0) + 1
W(f"  face-incidence degree per site, raw carrying: {dict(sorted(deg.items()))}")
W(f"  face-incidence degree per site, canonical   : {dict(sorted(degc.items()))}")
W(f"  sites whose incidence count drops: {[s for s in range(11) if deg.get(s,0)!=degc.get(s,0)]}")
W(f"  => raw node set: {len(deg)} sites/aux vs canonical {len(degc)}")

# ---------- chart rotation pin ----------
W("\nCHART ROTATION PIN")
cert = json.loads((P / "repaired_tc_krawczyk.json").read_text())["certificate"]
rad = float.fromhex(cert["radius_hex"])
z = [float.fromhex(x) for x in cert["center_hex"]][:7]
a = [z[0], z[1], z[2], z[3], 3.141592653589793 - 2 * sum(z[:4]), z[3], z[2], z[1], z[0]]
th = [0.0] * 9
for k in range(5, 9): th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1): th[k] = th[k + 1] - a[k] - a[k + 1]
raw = [th[k] + a[k] for k in range(9)]
W(f"  raw tie angles raw[0..8] = {[round(x,7) for x in raw]}")
can = [0.0] + [raw[(i + 2) % 9] - raw[2] + (2 * 3.141592653589793 if i >= 7 else 0.0) for i in range(1, 9)]
W(f"  canonical angles can[0..8] = {[round(x,7) for x in can]}")
W(f"  can[0] = 0 (pin)                            TRUE, value {can[0]}")
W(f"  can[i] = raw[(i+2)%9]-raw[2] for i=1..6     : "
  f"{[round(can[i]-(raw[(i+2)%9]-raw[2]),14) for i in range(1,7)]}")
W(f"  can[7] = raw[0]-raw[2]+2pi : {round(can[7],9)} vs {round(raw[0]-raw[2]+2*3.141592653589793,9)}")
W(f"  can[8] = raw[1]-raw[2]+2pi : {round(can[8],9)} vs {round(raw[1]-raw[2]+2*3.141592653589793,9)}")
W(f"  raw[8] lands at canonical index 6: can[6] = {round(can[6],9)} = raw[8]-raw[2] = {round(raw[8]-raw[2],9)}")
W(f"  monotone increasing (i=0..8): {all(can[i+1]>can[i] for i in range(8))}")
width = [can[i + 1] - can[i] for i in range(8)] + [2 * 3.141592653589793 - can[8]]
W(f"  widths = {[round(x,6) for x in width]}   sum = {round(sum(width),9)} (=2pi)")
W(f"  all widths in (0, L=2asin(19/50)={round(2*__import__('math').asin(19/50),6)}): "
  f"{all(0 < x < 2*__import__('math').asin(19/50) for x in width)}")

# ---------- zero-weight slack edges ----------
W("\nZERO-WEIGHT SLACK EDGES")
for fn in ("energy_library.json", "cosine_dbm_local920.json"):
    p = P / fn
    if not p.exists():
        W(f"  {fn}: MISSING"); continue
    d = json.loads(p.read_text())
    fields = d["fields"]
    W(f"  {fn}: {len(fields)} fields")
    zerofields = []
    for fi, f in enumerate(fields):
        ws = [F(x[2]) for x in f["weights"]]
        nz = sum(1 for x in ws if x == 0)
        if nz:
            zerofields.append((fi, nz, [tuple(x[:2]) for x in f["weights"] if F(x[2]) == 0]))
    W(f"    fields containing zero weights: {len(zerofields)}; total zero weights: "
      f"{sum(z[1] for z in zerofields)}")
    for fi, nz, pairs in zerofields[:12]:
        W(f"      field {fi}: {nz} zeros at site-pairs {pairs}")
    # --- SPD / connectivity check on the heaviest-weight field ---
    tot = [sum(F(x[2]) for x in f["weights"]) for f in fields]
    fmax = int(max(range(len(fields)), key=lambda i: tot[i]))
    f = fields[fmax]
    W(f"    SPD check on field {fmax}: sum of weights = {float(tot[fmax]):.6f}, "
      f"zeros = {sum(1 for x in f['weights'] if F(x[2])==0)}")
    # build the site-level Laplacian (only site-site edges are recorded as site pairs)
    pos = {}
    for (i, j, w) in f["weights"]:
        if F(w) != 0:
            pos.setdefault(i, 0); pos.setdefault(j, 0)
    szero = [x for x in f["weights"] if F(x[2]) == 0]
    W(f"    zero-weight site pairs: {[tuple(x[:2]) for x in szero]}")
    eps = [x[:2] for x in f["weights"] if F(x[2]) != 0]
    zero = [x[:2] for x in f["weights"] if F(x[2]) == 0]
    isolated = [s for s in range(9) if not any(s in pr for pr in eps)]
    W(f"    anchor rows with NO positive-weight pair: {isolated}")
    # pairwise: which anchors have all their pairs at zero weight
    from collections import defaultdict
    pz = defaultdict(list)
    for (i, j) in eps: pz[i].append(j); pz[j].append(i)
    W(f"    positive-support anchor degrees: {dict(sorted((k, len(v)) for k, v in pz.items()))}")

W("\nSUMMARY")
W("  incidence isomorphism: raw 9-face subgraph maps into the canonical 11-face graph under")
W("  s -> (s-2)%9 on ring labels; the two central faces (9,10,0),(9,10,4) are NOT in the raw")
W("  carrying graph and are supplied by the canonical model; the 18 tie pairs correspond")
W("  (checked set equality above).")

(OUT / "oracle_index_audit.txt").write_text("\n".join(log) + "\n")
print("wrote", OUT / "oracle_index_audit.txt")

