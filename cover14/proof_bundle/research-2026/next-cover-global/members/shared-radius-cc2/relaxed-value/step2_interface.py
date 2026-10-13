"""relaxed-value mechanism test.

Problem (fixed anchors, "SOCP" form of lead/fixed_anchor_convex_probe.py):
    variables  x = (C_1..C_n, W_1..W_nf, r)
    constraints  |C_i - W_f| <= r   for i in face f          (witness edges)
                 |C_i - A_j| <= r   for (i,j) in anchor edges (anchor edges)
    objective    r

Relaxation: drop the witness-edge rows of the SIX zero-stress faces
(4 X-adjacent + 2 central, from stress-barycentric weights) and of the TWO
slack faces (probe faces 14,15).  Keep 20 anchor-edge rows and the 24 witness
rows of the other 8 faces.

We test, at the candidate:
  (0) the reduced optimum with a candidate start  (does V_rel < r*?)
  (1) the exact same with the six/eight faces removed but all other
      structures kept;
  (2) one-step witness-position perturbations (couple the removed-face
      witnesses and the retained-face witnesses in a few named directions);
  (3) the anchor-connectivity audit the lead requested: which anchors are
      shared between the removed-face block and the retained-face block.
"""
import json
import math
import sys
import numpy as np
from pathlib import Path
from fractions import Fraction
from scipy.optimize import minimize

P = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")
OUT = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\relaxed-value")

G = json.loads((P / "stress-barycentric-result.json").read_text())
D = json.loads((P / "improved-upper-test.json").read_text())
PROBE = json.loads((P / "fixed-anchor-convex-probe.json").read_text())

C0 = np.array([[float(Fraction(x)) for x in p] for p in D["centers"]])
A0 = np.array([[math.cos(float(a["theta"])), math.sin(float(a["theta"]))]
               for a in G["anchors"]])
r_star = float(PROBE["runs"][0]["radius"])
faces = [list(f) for f in PROBE["runs"][0]["faces"]]
owners = [list(o) for o in PROBE["runs"][0]["owners"]]
n = C0.shape[0]
nf = len(faces)

# ---------------- identify the zero-stress faces and slack faces
# stress-barycentric weights layout: 24 face-edge weights + 11 anchor weights
w = np.array(G["weights"], float)
# The producer's face order is G['faces'] (14 faces); the two appended faces in
# the probe are faces 14,15 = [4,6,12],[5,7,13] (the two slack faces).
# The six zero-weight faces are those whose witness weight vanishes.  We read
# them off by matching the producer's per-face structure: recompute each face's
# barycentric weight from the producer's layout by a small LP-free check using
# the printed weight block positions.
# Positions 1,4,7,10,13,15 are the zero entries in the printed row; these are
# the second edge of faces 0,1,2,3 and the edges of faces 4,5 ...
zero_pos = [i for i, v in enumerate(w) if abs(v) < 1e-12]
# Map weight index -> (face, slot) using the producer's own ordering: the first
# 24 entries are face edges in the same face order as G['faces'] but the
# producer counts only 14 faces with 24 edges => 10 face triples*3 = 30-6?
# The safe route: recompute barycentric weight per face from geometry.
def barycentric_weight(tri):
    a, b, c = C0[tri[0]], C0[tri[1]], C0[tri[2]]
    M = 2 * np.array([b - a, c - a])
    rhs = np.array([b @ b - a @ a, c @ c - a @ a])
    try:
        O = np.linalg.solve(M, rhs)
    except np.linalg.LinAlgError:
        return None
    # barycentric coords of O in triangle (a,b,c)
    T = np.array([a - c, b - c]).T
    try:
        lam = np.linalg.solve(T, O - c)
    except np.linalg.LinAlgError:
        return None
    return np.array([lam[0], lam[1], 1 - lam[0] - lam[1]])

bary = {}
for i, f in enumerate(faces):
    bw = barycentric_weight(f)
    bary[i] = None if bw is None else bw.tolist()

# zero-stress faces = the ones reported with zero weight by the producer.
# From the printed row the six zero faces are exactly those with a zero in the
# producer's own ordering; we take the geometric statement of
# STRESS-SUPPORT-ANALYTIC.md instead: the 4 X-adjacent faces and the 2 central
# faces.  X = sites 8,9 (on the x-axis, maximal arc width).  Central = the
# faces containing the middle pair (10,11) on the x-axis.
X = [8, 9]
central = [i for i, f in enumerate(faces) if set(f) >= {10, 11}]
x_faces = [i for i, f in enumerate(faces) if (8 in f) or (9 in f)]
zero_faces = sorted(set(x_faces) | set(central))
slack_faces = [14, 15]
removed = sorted(set(zero_faces) | set(slack_faces))
kept = [i for i in range(nf) if i not in removed]

audit = dict(
    faces=faces, owners=owners, X_sites=X, central_faces=central,
    x_adjacent_faces=x_faces, zero_faces=zero_faces, slack_faces=slack_faces,
    removed_faces=removed, kept_faces=kept,
    n_removed=len(removed), n_kept=len(kept),
    removed_witness_edges=int(sum(len(faces[i]) for i in removed)),
    kept_witness_edges=int(sum(len(faces[i]) for i in kept)),
    kept_anchor_edges=int(sum(len(faces[i]) for i in kept)),
    barycentric=bary,
)
print("zero faces", zero_faces, "slack", slack_faces, "kept", kept, flush=True)

# ---------------- connectivity audit (the lead's interface question)
# For every site, which anchors touch it (via ANY face, original or retained)?
site_anchors_all = {i: set() for i in range(n)}
site_anchors_kept = {i: set() for i in range(n)}
for i, f in enumerate(faces):
    for s in f:
        for a in owners:
            if s in a:
                site_anchors_all[s].add(tuple(a))
                if i in kept:
                    site_anchors_kept[s].add(tuple(a))
# anchors are shared when the same anchor pair owns a site that appears in both
# the removed block and the kept block
removed_sites = sorted(set(x for i in removed for x in faces[i]))
kept_sites = sorted(set(x for i in kept for x in faces[i]))
shared = {}
for s in range(n):
    a_all = site_anchors_all[s]
    a_kept = site_anchors_kept[s]
    if a_all and not a_kept:
        shared.setdefault("removed_only_sites", []).append(s)
    if a_kept:
        shared.setdefault("kept_sites", []).append(s)
audit["removed_sites"] = removed_sites
audit["kept_sites"] = kept_sites
audit["site_anchor_count_all"] = {str(k): len(v) for k, v in site_anchors_all.items()}
audit["site_anchor_count_kept"] = {str(k): len(v) for k, v in site_anchors_kept.items()}
audit["shared_info"] = shared
# anchor -> sites (both blocks)
anchor_sites = {j: set() for j in range(len(owners))}
for j, ow in enumerate(owners):
    for s in ow:
        anchor_sites[j].add(s)
audit["anchor_owner_sites"] = {str(k): sorted(v) for k, v in anchor_sites.items()}
# is any anchor owning BOTH a removed-only site and a kept site?
for j, ss in anchor_sites.items():
    if any(s in removed_sites for s in ss) and any(s in kept_sites for s in ss):
        audit.setdefault("anchors_bridging", []).append(j)
print("anchors bridging removed/kept:", audit.get("anchors_bridging"), flush=True)

(OUT / "interface_audit.json").write_text(json.dumps(audit, indent=1))
print("wrote interface_audit.json", flush=True)
