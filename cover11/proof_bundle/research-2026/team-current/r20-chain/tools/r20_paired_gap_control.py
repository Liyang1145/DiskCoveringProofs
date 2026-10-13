"""Short control for PAIRED-GAP-NECESSITY.md (one bounded calibration; no global scan).

Writes ../out/paired_gap_necessity_control.txt.  Read-only elsewhere.  No STATUS/DEAD edits.

Checks (all on the explicit exported incidence, not a synthetic pattern):
  C1  two-edge-path bound calibration: for every adjacent anchor pair the middle site gives
      V >= |chord|/2 = sin(Delta_i/2); print the per-gap values at the candidate and the max.
  C2  threshold necessity: V < R*  =>  max_i sin(Delta_i/2) < R*  =>  all Delta_i < 2asin(R*);
      instantiate with R* (exported) and with L = 2asin(19/50); report the shrink L - 2asin(R*).
      Consistency: the candidate's own gaps must all satisfy the necessity cap.
  C3  structural premise for the 3-anchor route: count anchors adjacent to each site and to each
      aux node; verify NO free node is adjacent to >=3 anchors (no Steiner/Y node), so the
      closed-form minimal-enclosing-disk bound is NOT available on this graph.
  C4  adjacent-pair (4-edge path) closed form sin((Delta_i+Delta_{i+1})/2)/2 vs the best single
      two-edge bound, showing the path form of the paired route is weaker.
"""
import json, collections
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def main():
    E = json.loads((ROOT / "team-current/r20-alternative" /
                    "socp_anchor_export.json").read_text())
    inc = E["incidence_map"]
    U = np.array(E["U"], float)
    R = float(E.get("R_star", E.get("r_solution")))
    edges = []
    for (kind, site, q) in inc:
        edges.append((9 + int(site), int(q)) if kind == "endpoint" else (9 + int(site), 20 + int(q)))
    adj = collections.defaultdict(set)
    for v, w in edges:
        adj[v].add(w); adj[w].add(v)
    P("=" * 96)
    P("PAIRED-GAP NECESSITY — bounded control (numeric proposal; no interval claims)")
    P("edges %d ; anchors 0..8 ; R* = %.15f ; L = 2asin(19/50) = %.9f" % (len(edges), R, 2*np.arcsin(19/50)))

    th = [float(np.arctan2(U[i][1], U[i][0])) for i in range(9)]
    gaps = [((th[(i+1) % 9] - th[i]) % (2*np.pi)) for i in range(9)]
    s2 = [np.sin(g/2) for g in gaps]
    P("")
    P("C1  two-edge bound V >= sin(Delta_i/2)   (middle site, uniform alpha = 1/2)")
    for i, (g, s) in enumerate(zip(gaps, s2)):
        P("   gap %d: Delta = %.6f  bound sin(Delta/2) = %.6f" % (i, g, s))
    P("   max bound over adjacent pairs = %.6f   (R* = %.6f ; max < R* : %s)"
      % (max(s2), R, max(s2) < R))

    P("")
    P("C2  threshold necessity: V < R*  =>  every Delta_i < 2asin(R*)")
    capR = 2*np.arcsin(R)
    P("   2asin(R*) = %.9f ; L = %.9f ; shrink L - 2asin(R*) = %.3e" % (capR, 2*np.arcsin(19/50),
                                                                       2*np.arcsin(19/50) - capR))
    P("   candidate gaps max = %.6f < %.9f : %s (necessity consistent at the candidate)"
      % (max(gaps), capR, max(gaps) < capR))
    P("   (with a certified upper bound R_hi for R*, use L' = 2asin(R_hi); supply R_hi to instantiate.)")

    P("")
    P("C3  structural premise: sites see exactly two anchors; no free node sees three")
    site_anchor = {j: [a for a in range(9) if a in adj[9+j]] for j in range(11)}
    P("   anchors per site: %s" % {j: len(v) for j, v in site_anchor.items()})
    three = [n for n in range(9, 31) if len([a for a in adj[n] if a < 9]) >= 3]
    P("   free nodes adjacent to >=3 anchors: %s  =>  Steiner/Y node exists: %s"
      % (three, bool(three)))
    P("   consequence: the closed-form minimal-enclosing-disk / Steiner bound V >= MEC(U_i,U_j,U_k)")
    P("   is NOT available on this graph; a 3-anchor bound must use aux-mediated sub-networks and")
    P("   be computed, not quoted in closed form.")

    P("")
    P("C4  adjacent-pair (4-edge path) closed form vs best single two-edge bound")
    for i in range(9):
        v = np.sin((gaps[i] + gaps[(i+1) % 9])/2)/2
        P("   pair (%d,%d): sin((D_i+D_{i+1})/2)/2 = %.6f   vs  max single = %.6f  -> %s"
          % (i, (i+1) % 9, v, max(s2[i], s2[(i+1) % 9]),
             "weaker" if v < max(s2[i], s2[(i+1) % 9]) else "stronger"))
    P("")
    P("SCOPE: float, numeric proposal only; bounded control (no scan); path family NOT declared dead.")
    (OUT / "paired_gap_necessity_control.txt").write_text("\n".join(LOG) + "\n")
    P("wrote " + str(OUT / "paired_gap_necessity_control.txt"))


if __name__ == "__main__":
    main()
