"""Audit: resolve the ACTUAL index mapping of the lead's q0 scripts.

Read-only on lead/. Writes ../out/audit_lead_q0_map.txt.

Question raised by the lead-order handover (2026-09-25):
  * check_r20_chain_variance.py builds `roots[i]` = min-norm root of the node edge (i,i+1),
    i = 0..8, and then uses ids = [4,6,8] with `h = c[10]`.
  * `c` itself comes from q0_exact_closure_radius.py:
        C = [rings sorted by atan2] + [row 0, row 2]
        c = C[ [(i+shift)%9 for i in range(9)] + ([10,9] if swap else [9,10]) ]
    selected by matching Delaunay(c).simplices to q0_graphs.json[2]['faces'].

So BOTH the ring rotation (shift) and the hub order (swap) are decided by that Delaunay test.
This script prints the unique selection, the object-row origin of every lead index, the exact
coordinates of c[4], c[6], c[8], c[9], c[10], the pins roots[4], roots[6], roots[8], their
distances to both hubs, the barycentric weights and the variance V = sum_{i<j} lam_i lam_j d_ij^2.

No optimisation, no claim registration.
"""
import json, math
import numpy as np
from pathlib import Path
from scipy.spatial import Delaunay

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
ROOT = HERE.parents[3]                        # .../ai4math2
LEAD = ROOT / "research-2026" / "team-current" / "lead"
OBJ = ROOT / "n11" / "upper" / "certified_object.json"
OBJ2 = ROOT / "research-2026" / "team-current" / "cline2-sharp-fan" / "out" / "certified_object_copy.json"

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def main():
    raw = json.loads(OBJ.read_text(encoding="utf-8-sig"))
    C0 = np.array([[int(v) / 1e17 for v in a] for a in raw["centers_scaled_1e17"]])
    # cross-check the two copies of the object agree bit for bit (scaled integers)
    raw2 = json.loads(OBJ2.read_text(encoding="utf-8"))
    C0b = np.array([[int(v) / 1e17 for v in a] for a in raw2["centers_scaled_1e17"]])
    P("objects agree (n11/upper/certified_object.json vs cline2-sharp-fan/.../certified_object_copy.json):",
      bool(np.array_equal(C0, C0b)))

    rings = sorted([i for i in range(11) if i not in (0, 2)], key=lambda i: math.atan2(C0[i, 1], C0[i, 0]))
    P("\npolar order of the nine ring rows about the origin:", rings)
    P("  (row 0 = hub A, row 2 = hub B;  rows kept in C = rings + [0, 2])")

    C = C0[rings + [0, 2]]                      # C[9] = hub A, C[10] = hub B
    faces = json.loads((LEAD / "q0_graphs.json").read_text())[2]["faces"]
    target = {tuple(sorted(f)) for f in faces}
    P("\nq0_graphs.json[2]: span =", json.loads((LEAD / "q0_graphs.json").read_text())[2]["span"],
      " faces =", faces)

    matches = []
    for shift in range(9):
        for swap in range(2):
            c = C[[(i + shift) % 9 for i in range(9)] + ([10, 9] if swap else [9, 10])]
            sim = {tuple(sorted(f)) for f in Delaunay(c).simplices}
            if sim == target:
                matches.append((shift, swap))
    P("\n(shift, swap) selections whose Delaunay(c) equals the target face set:", matches)
    assert matches, "no mapping reproduces the target Delaunay complex"

    for (shift, swap) in matches:
        P("\n===================== selected (shift=%d, swap=%d) =====================" % (shift, swap))
        idx = [(i + shift) % 9 for i in range(9)] + ([10, 9] if swap else [9, 10])
        c = C[idx]
        # origin label of each lead index
        lab = []
        for i in idx:
            if i < 9:
                lab.append("ring row %d" % rings[i])
            else:
                lab.append("hub %s" % ("B(row2)" if i == 9 else "A(row0)"))
        # careful: in C, index 9 = row 0 = A ; index 10 = row 2 = B
        lab = []
        for i in idx:
            if i < 9:
                lab.append("ring_row_%d" % rings[i])
            else:
                lab.append("row_%d(%s)" % ((0 if i == 9 else 2), ("hubA" if i == 9 else "hubB")))
        for j in range(11):
            P("  c[%2d] = (%+.12f, %+.12f)  <- %s  |c| = %.12f"
              % (j, c[j, 0], c[j, 1], lab[j], np.linalg.norm(c[j])))

        r = 0.3799838531198388
        # the lead's roots: min-norm root of node edge (i,i+1)
        roots, meta = [], []
        for i in range(9):
            a, b = c[i], c[(i + 1) % 9]
            m = (a + b) / 2
            d = float(np.linalg.norm(b - a))
            n = np.array([-(b - a)[1], (b - a)[0]]) / d
            k = math.sqrt(r * r - d * d / 4)
            cand = [m + k * n, m - k * n]
            pin = min(cand, key=np.linalg.norm)
            roots.append(pin)
            meta.append((i, d, k, float(np.linalg.norm(pin))))
        P("\n  lead pins roots[i] = min-norm root of node edge (c[i], c[i+1]):")
        for (i, d, k, npin) in meta:
            P("    roots[%d] = (%+.12f, %+.12f)  edge len %.9f  k %.9f  |pin| %.9f"
              % (i, roots[i][0], roots[i][1], d, k, npin))

        ids = [4, 6, 8]
        p = np.array([roots[i] for i in ids])
        h = c[10]
        lam = np.linalg.solve(np.vstack([p.T, np.ones(3)]), np.r_[h, 1])
        P("\n  lead ids            = %s" % (ids,))
        P("  their edge origins  = %s" % [("(%s,%s)" % (lab[i], lab[(i + 1) % 9])) for i in ids])
        P("  h = c[10]           = (%+.12f, %+.12f)  |h| = %.12f   <- %s" % (h[0], h[1], np.linalg.norm(h), lab[10]))
        P("  c[9]                = (%+.12f, %+.12f)  |c9| = %.12f  <- %s" % (c[9][0], c[9][1], np.linalg.norm(c[9]), lab[9]))
        for t, i in enumerate(ids):
            P("  pin[%d] = roots[%d] dist to c[10] = %.15f  (r - d = %+.3e)   dist to c[9] = %.15f"
              % (t, i, np.linalg.norm(p[t] - c[10]), r - np.linalg.norm(p[t] - c[10]),
                 np.linalg.norm(p[t] - c[9])))
        P("  barycentric weights lam = (%s)" % ", ".join("%+.15f" % v for v in lam))
        lp = lam @ p
        P("  weights . pins = (%+.12f, %+.12f) ; c[10] = (%+.12f, %+.12f) ; |weights.pins - c[10]| = %.3e"
          % (lp[0], lp[1], h[0], h[1], float(np.linalg.norm(lp - h))))
        P("  |weights . pins - c[9]| = %.12f" % float(np.linalg.norm(lp - c[9])))
        V = sum(lam[i] * lam[j] * float(np.sum((p[i] - p[j]) ** 2)) for i in range(3) for j in range(i))
        P("  V = sum_{i<j} lam_i lam_j |p_i-p_j|^2 = %.18f" % V)
        P("  V - r^2 = %+.6e" % (V - r * r))
        # distances of all nine pins to both hubs, with activity margins
        P("\n  ALL pins vs both hubs (margin = dist - r; negative = active):")
        for i in range(9):
            da = float(np.linalg.norm(roots[i] - c[9]))
            db = float(np.linalg.norm(roots[i] - c[10]))
            P("    edge (%2d,%2d): d(c9)=%.12f  margin=%+.3e |  d(c10)=%.12f  margin=%+.3e"
              % (i, (i + 1) % 9, da, da - r, db, db - r))

    (OUT / "audit_lead_q0_map.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "audit_lead_q0_map.txt"))


if __name__ == "__main__":
    main()
