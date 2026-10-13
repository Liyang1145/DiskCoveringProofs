"""Step 2: relaxed problem data + interface audit (pure numpy, no scipy)."""
import json
import math
import numpy as np
from pathlib import Path
from fractions import Fraction

P = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")
OUT = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\relaxed-value")

G = json.loads((P / "stress-barycentric-result.json").read_text())
D = json.loads((P / "improved-upper-test.json").read_text())
PR = json.loads((P / "fixed-anchor-convex-probe.json").read_text())

C0 = np.array([[float(Fraction(x)) for x in p] for p in D["centers"]])
anchors = [(float(a["theta"]), list(a["owners"])) for a in G["anchors"]]
A0 = np.array([[math.cos(t), math.sin(t)] for t, _ in anchors])
owners = [list(o) for _, o in anchors]
faces = [list(f) for f in PR["runs"][0]["faces"]]
r_star = float(PR["runs"][0]["radius"])
w = np.array(G["weights"], float)
n, nf = C0.shape[0], len(faces)

out = {}
out["r_star"] = r_star
out["anchors_theta_deg"] = [round(math.degrees(t), 6) for t, _ in anchors]
out["owners"] = owners
out["faces"] = faces
out["n_faces"] = nf
out["n_sites"] = n

# face -> site triples already; identify X (max arc width) and central pairs
X = [8, 9]
central = [i for i, f in enumerate(faces) if set(f) >= {10, 11}]
x_faces = [i for i, f in enumerate(faces) if (8 in f) or (9 in f)]
zero_faces = sorted(set(x_faces) | set(central))
slack_faces = [14, 15]
removed = sorted(set(zero_faces) | set(slack_faces))
kept = [i for i in range(nf) if i not in removed]
out["X_sites"] = X
out["x_adjacent_faces"] = x_faces
out["central_faces"] = central
out["zero_faces"] = zero_faces
out["slack_faces"] = slack_faces
out["removed_faces"] = removed
out["kept_faces"] = kept
out["kept_face_triples"] = [faces[i] for i in kept]
out["removed_face_triples"] = [faces[i] for i in removed]

# the producer's zero-weight slots (row 0 of weights)
zero_slots = [i for i, v in enumerate(w) if abs(v) < 1e-12]
out["producer_zero_weight_slots_row0"] = zero_slots

# ---------------- INTERFACE: which sites/anchors bridge removed vs kept ----
site_in_removed = {s: any(s in faces[i] for i in removed) for s in range(n)}
site_in_kept = {s: any(s in faces[i] for i in kept) for s in range(n)}
out["sites_only_in_removed"] = [s for s in range(n) if site_in_removed[s] and not site_in_kept[s]]
out["sites_only_in_kept"] = [s for s in range(n) if site_in_kept[s] and not site_in_removed[s]]
out["sites_in_both"] = [s for s in range(n) if site_in_kept[s] and site_in_removed[s]]

# anchor bridging: an anchor owns two sites (its "owners" list).  It bridges if
# one owned site is removed-only and another kept(-also) etc.
bridge = []
for j, ow in enumerate(owners):
    kinds = set()
    for s in ow:
        if site_in_removed[s] and site_in_kept[s]:
            kinds.add("both")
        elif site_in_removed[s]:
            kinds.add("removed_only")
        elif site_in_kept[s]:
            kinds.add("kept_only")
    out.setdefault("anchor_site_kinds", {})[j] = sorted(kinds)
    if "removed_only" in kinds and ("kept_only" in kinds or "both" in kinds):
        bridge.append(j)
out["anchors_bridging_removed_to_kept"] = bridge

# per kept face: which anchors, which sites
out["kept_face_anchors"] = {str(i): [j for j, ow in enumerate(owners)
                                     if any(s in ow for s in faces[i])] for i in kept}
out["kept_face_sites"] = {str(i): faces[i] for i in kept}

# how many retained witness edges and anchor edges
out["kept_witness_edges"] = int(sum(len(faces[i]) for i in kept))
out["kept_anchor_edges"] = int(sum(len(faces[i]) for i in kept))
out["removed_witness_edges"] = int(sum(len(faces[i]) for i in removed))

print(json.dumps({k: v for k, v in out.items()
                  if k not in ("owners", "faces", "anchor_site_kinds")}, indent=1)[:4000])
(OUT / "relaxed_data.json").write_text(json.dumps(out, indent=1))
print("wrote relaxed_data.json")
