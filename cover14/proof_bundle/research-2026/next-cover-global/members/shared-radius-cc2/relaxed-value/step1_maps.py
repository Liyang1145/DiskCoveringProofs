"""Interface audit step 1: build the RELAXED problem's retained sets and the
anchor-connectivity graph, from the literal data. No optimization yet.

Outputs (JSON) for inspection:
  - face index maps: probe faces vs stress-barycentric faces
  - zero-weight faces (from stress-barycentric weights)
  - the two slack faces (probe-appended)
  - retained faces (8) with their site triples
  - retained anchor edges (20): (site, anchor) pairs of the retained faces
  - anchors per retained face, and for each anchor the list of retained faces
    incident to it  -> tells us whether an anchor is a TERMINAL of exactly one
    retained face (candidate free terminal) or SHARED by >=2.
"""
import json
import math
import numpy as np
from pathlib import Path
from fractions import Fraction

P = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")
out = {}

G = json.loads((P / "stress-barycentric-result.json").read_text())
D = json.loads((P / "improved-upper-test.json").read_text())
PROBE = json.loads((P / "fixed-anchor-convex-probe.json").read_text())

C = np.array([[float(Fraction(x)) for x in p] for p in D["centers"]])
A = np.array([[math.cos(float(a["theta"])), math.sin(float(a["theta"]))]
              for a in G["anchors"]])
probe_faces = PROBE["runs"][0]["faces"]
probe_owners = PROBE["runs"][0]["owners"]
sb_faces = [f["ids"] for f in G["faces"]]
weights = G["weights"]

# ---- mapping between the two face orderings (lead warned they differ)
mapped = {}
for i, f in enumerate(sb_faces):
    j = next((k for k, pf in enumerate(probe_faces) if pf == f), None)
    mapped[i] = j
out["sb_to_probe_face_index"] = mapped
out["sb_face_site_triples"] = sb_faces
out["probe_face_site_triples"] = probe_faces
out["n_sb_faces"] = len(sb_faces)
out["n_probe_faces"] = len(probe_faces)

# ---- which stress weights correspond to what: print all weight rows
out["sb_weights_rows_len"] = len(weights)
out["sb_weights_first"] = weights[0] if weights else None
print("sb faces:", sb_faces, flush=True)
print("probe faces:", probe_faces, flush=True)
print("weights[0] len:", len(weights[0]) if weights else None, flush=True)
print("weights[0]:", weights[0] if weights else None, flush=True)

# the zero-weight entries inside the first weight row appear at positions
# 1,4,7,10,13,15 -> identify which index those are in the producer's layout
w0 = np.array(weights[0], float)
zeros_idx = [i for i, v in enumerate(w0) if abs(v) < 1e-12]
out["zero_weight_positions_row0"] = zeros_idx
print("zero weight positions:", zeros_idx, flush=True)

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\relaxed-value\interface_maps.json", "w") as fh:
    json.dump(out, fh, indent=1)
print("wrote interface_maps.json")
