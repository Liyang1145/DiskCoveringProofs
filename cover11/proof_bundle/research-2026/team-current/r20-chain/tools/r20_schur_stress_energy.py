"""r20 Schur/stress energy mechanism for the fixed-switch network (lead task).

Writes ../out/r20_schur_stress_energy.txt once the alpha export lands (see INPUT below).
READ-ONLY elsewhere; this is a NUMERIC PROPOSAL, not an interval certificate: an .npy/float input
plus ordinary inversion is NOT an interval computation, so nothing here may be called "strict".

GRAPH (lead's correction: active edges = 18 + 9*3 = 45, the 6 slack-face edges have alpha = 0)
  nodes:  9 boundary switches U_i  +  11 sites c_j  +  11 face auxiliaries z_f      (31 nodes)
  edges:  18 endpoint constraints  (c_i,u) -> node indices (site i, switch)          [always active]
          33 face constraints      (c, z_f)  -> of which 9 faces are active (27 edges) and
                                              2 faces slack (6 edges with alpha = 0)
  weights alpha_e >= 0, sum_e alpha_e = 1   (stress/dual lift, frozen)

MECHANISM (independent derivation, written up in BRIEF §5.14)
  (D1) any primal feasible point has every edge length <= r, hence
           sum_e alpha_e |X_v - X_w|^2 <= r^2 sum_e alpha_e = r^2     (the trivial direction);
  (D2) the useful object is the MINIMUM over the free nodes (sites + auxiliaries) at fixed switch
       data U: E(U) := min_{c,z} sum_e alpha_e |X_v-X_w|^2 = sum_{i,j} Lambda_{ij} <U_i, U_j>,
       where Lambda is the boundary Schur complement of the weighted graph Laplacian
           Lambda = L_bb - L_bf L_ff^+ L_fb
       (pseudoinverse: zero-alpha edges may disconnect the graph, so we never invert the full block;
       for each connected component with alpha>0 the component Schur complement is used);
       Lambda is a "weighted boundary Laplacian": off-diagonal <= 0 (Schur complements of weighted
       graph Laplacians keep the M-matrix sign pattern; per component).
  (D3) the candidate's force balance makes every free site harmonic, so the candidate attains the
       minimum: E(U*) = R*^2 (complementary slackness: only active edges carry alpha>0).
  (D4) hence if min over the admissible switch data of E(U) >= R*^2 then r >= R* for every cover —
       the main lower bound — with equality at the candidate (sharpness).
  (D5) angular Hessian: with U_i = (cos theta_i, sin theta_i) and E(theta) = sum_{i!=j}Lambda_{ij}
       cos(theta_i-theta_j),
           d_i d_j E = +Lambda_{ij} cos(theta_i-theta_j)   (i != j),
           d_i^2 E   = -sum_{j!=i} Lambda_{ij} cos(theta_i-theta_j),
       i.e. H = 2 x (signed Laplacian with weights Lambda_{ij} cos(theta_i-theta_j)) up to the
       overall sign convention.  For FAR pairs cos < 0, so the signed weights are negative and the
       usual block/row-positivity arguments FAIL: PSD (modulo the global rotation kernel) must be
       decided numerically at the candidate.
  DECISION RULE (lead): if H has a negative eigenvalue on the rotation quotient, the frozen-stress
  lower bound is NOT globally sharp along that direction and only this route fails; report it there
  and do not invest in more sampling.

INPUT (alternative is exporting): a JSON with the 51 alpha values and the positions, e.g.
  {"alpha": [...51...], "C": [[x,y]x11], "Z": [[x,y]x11], "U": [[x,y]x9], "R": float,
   "edge_order": "(c_i,U)+(c_j,U) for i=0..8 then (c,z_f) for f=0..10"}
The loader below accepts that schema and also a flat {"edges":[[v,w,alpha],...]} form.
"""
import json
import sys
from pathlib import Path
import numpy as np

OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def build_graph(alpha, C, Z, U):
    """nodes: 0..8 switches U, 9..19 sites C, 20..30 aux Z; edges (v,w,alpha).

    GUARD (lead's correction, 2026-09-25f): the synthetic pattern `(f+j) % 11` is WRONG — the 11
    face site-lists are NONCONSECUTIVE, so face edges must come from the exported `incidence_map`
    (entries `(kind, site, q)`: 'endpoint' -> switch q, otherwise -> aux index q).  Preferred runner:
    `tools/run_export_schur.py` (loads r20-alternative/socp_anchor_export.json, same conventions).
    UNIFIED CONVENTION: alpha = 2*r*lambda (51, norm form); H_ij = 2*Lam_ij*cos(theta_i-theta_j)
    for i != j and H_ii = -sum_{j!=i} H_ij.
    """
    incidence_map = None
    if not incidence_map:
        raise SystemExit("build_graph: refusing synthetic face indexing (f+j)%11 — pass the actual "
                         "incidence_map, or run tools/run_export_schur.py")
    edges = []
    for k, (kind, site, q) in enumerate(incidence_map):
        if kind == "endpoint":
            edges.append((9 + int(site), int(q), alpha[k]))
        else:
            edges.append((9 + int(site), 20 + int(q), alpha[k]))
    return edges, len(edges)


def schur_boundary(edges, nnode=31, nbound=9):
    """Lambda = L_bb - L_bf L_ff^+ L_fb, assembled component-wise on alpha>0 edges."""
    L = np.zeros((nnode, nnode))
    for (v, w, a) in edges:
        if a == 0:
            continue
        L[v, v] += a; L[w, w] += a
        L[v, w] -= a; L[w, v] -= a
    bb = L[:nbound, :nbound]; bf = L[:nbound, nbound:]
    fb = L[nbound:, :nbound]; ff = L[nbound:, nbound:]
    # component-wise elimination on the free block: use pseudoinverse (never invert the full block)
    Lam = bb - bf @ np.linalg.pinv(ff, rcond=1e-12) @ fb
    return Lam, L


def main():
    P("=" * 100)
    P("SCHUR/STRESS ENERGY MECHANISM — NUMERIC PROPOSAL (NOT an interval certificate)")
    src = None
    for cand in (OUT.parent / "in" / "switch_alpha.json", OUT / "switch_alpha.json"):
        if cand.exists():
            src = cand
            break
    if src is None:
        P("  alpha export not found yet.  Looked for:")
        P("    %s" % (OUT.parent / "in" / "switch_alpha.json"))
        P("    %s" % (OUT / "switch_alpha.json"))
        P("  Waiting for alternative's export (51 alpha + C, Z, U).  Mechanism and graph are ready:")
        P("    nodes 31 = 9 switches + 11 sites + 11 aux ; edges 51 = 18 endpoint + 33 face")
        P("    active edges expected 45 = 18 + 27 (6 slack-face edges with alpha = 0)")
        (OUT / "r20_schur_stress_energy.txt").write_text("\n".join(LOG) + "\n")
        return
    d = json.loads(src.read_text())
    if "edges" in d:
        edges = [tuple(e) for e in d["edges"]]
    else:
        alpha = list(map(float, d["alpha"]))
        C = d["C"]; Z = d["Z"]; U = d["U"]
        edges, k = build_graph(alpha, C, Z, U)
        P("  edge count from builder: %d (expect 51)" % k)
    nz = sum(1 for e in edges if e[2] > 0)
    P("  edges: %d ; alpha>0: %d (expect 45) ; sum alpha = %.12f" % (len(edges), nz, sum(e[2] for e in edges)))
    Lam, L = schur_boundary(edges)
    U = np.asarray(d["U"], dtype=float)
    R = float(d.get("R", 0.37998385311983870905))
    E = sum(Lam[i, j]*float(U[i] @ U[j]) for i in range(9) for j in range(9))
    P("  E(U*) = %.15f ; R^2 = %.15f ; difference = %+.3e" % (E, R*R, E - R*R))
    P("  Lambda: off-diagonal max = %+.3e (should be <= 0 up to rounding)" % Lam[~np.eye(9, dtype=bool)].max())
    th = np.arctan2(U[:, 1], U[:, 0])
    cs = np.cos(th[:, None] - th[None, :])
    H = np.zeros((9, 9))
    for i in range(9):
        for j in range(9):
            if i != j:
                H[i, j] = 2*Lam[i, j]*cs[i, j]
        H[i, i] = -sum(H[i, j] for j in range(9) if j != i)
    ev = np.linalg.eigvalsh(H)
    P("  angular Hessian eigenvalues (ascending): %s" % ["%.6e" % x for x in ev])
    rot = np.ones(9)/3.0
    P("  rotation kernel check <H,rot,rot> = %.6e ; second-smallest eigenvalue = %.6e"
      % (float(rot @ H @ rot), ev[1]))
    P("  VERDICT (numeric proposal): H is %s on the rotation quotient."
      % ("PSD" if ev[1] >= -1e-12 else "NEGATIVE-DIRECTION (frozen-stress bound not globally sharp)"))
    P("")
    P("  CAVEAT: npy/float inputs + ordinary inverse = NOT an interval computation; numbers are a")
    P("  numeric proposal only.  Bearing object remains the worker's interval enclosure.")
    (OUT / "r20_schur_stress_energy.txt").write_text("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
