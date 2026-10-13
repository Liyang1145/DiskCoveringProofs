"""r20 GLOBAL SHORT-GAP SCREEN: Dirichlet/effective-conductance lower bound on V(U) when a gap is small.

Writes ../out/r20_short_gap_screen.txt.  Read-only elsewhere.  No subagents.

OBJECT (lead's FIXED-SWITCH-SOC-REDUCTION.md / NETWORK-ENERGY-INTERFACE.md)
  Fix nine unit anchors U_0..U_8 in cyclic order with gap angles Delta_i = angle(U_{i-1},U_i),
  sum_i Delta_i = 2pi, each Delta_i in [m, L], m = 2pi - 8L, L = 2 asin(19/50) = 0.7796...
  V(U) = min t s.t. |c_i - U_{i-1}|,|c_i - U_i| <= t (18) and |c_s - z_f| <= t (33)  [SOCP]
  DUAL (exact, Slater):  V(U)^2 = max_{alpha in simplex_51} E_alpha(U),
      E_alpha(U) = inf_X sum_e alpha_e q_e(X,U) = sum_{i,j} Lambda_ij(alpha) <U_i,U_j>
  (Schur complement of the alpha-weighted graph Laplacian; zero-weight components handled by
  pseudoinverse).  Every admissible alpha gives a LOWER bound V(U) >= sqrt(E_alpha(U)).

WHY THE NAIVE PATH BOUND IS WEAK (kept as a calibration, not as the screen)
  An m-edge path between two anchors carries value |U_a-U_b|^2/(4m) at the best alpha, so
  V >= |U_a-U_b|/(2 sqrt(m)); with one gap Delta <= 0.2 the other eight gaps have average
  (2pi-0.2)/8 = 0.7675 and at least one is >= 0.7604, chord = 2 sin(0.3802) = 0.7426, and the
  2-edge path through the middle site gives only 0.7426/(2 sqrt 2) = 0.2626 < 0.38.  Hence the
  path-only screen CANNOT fire; the screen below maximises the FULL dual over alpha (all 51 edges
  share the budget), which is the strongest bound available at this interface.

METHOD
  * E_alpha and its gradient: Danskin gives d E/d alpha_e = q_e(X*_alpha) = |X*_v - X*_w|^2 at the
    weighted-least-squares minimiser X*; E is CONCAVE in alpha, so a projected-gradient ASCENT on
    the simplex is run (no vertex reduction possible - every simplex vertex gives E = 0).
  * both coordinates are handled at once by stacking (the quadratic form factorises per coordinate).
  * structured extremal cases of the short-gap region {Delta_i <= 0.2} are tested, not a grid:
    (A) one gap 0.2, other eight equal; (B) one gap 0.2, others at the cap L (last one residual);
    (C) one gap 0.2, others as close to m as feasibility allows; each cyclically placed (9 shifts).
"""
import json
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []
R_STAR = 0.3799838531198385
L = 2*np.arcsin(19/50)


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def load_graph():
    d = json.loads((ROOT / "r20-alternative" / "socp_anchor_export.json").read_text())
    inc = d["incidence_map"]
    edges = []
    for (kind, site, q) in inc:
        if kind == "endpoint":
            edges.append((9 + int(site), int(q)))
        else:
            edges.append((9 + int(site), 20 + int(q)))
    return edges, d


def anchors_from_gaps(gaps):
    """cyclic anchors on the unit circle from the 9 gap widths (sum 2pi)."""
    th = [0.0]
    for g in gaps[:-1]:
        th.append(th[-1] + g)
    return np.array([[np.cos(t), np.sin(t)] for t in th])


def energy(alpha, edges, U, nnode=31):
    Lm = np.zeros((nnode, nnode))
    for (v, w), a in zip(edges, alpha):
        if a <= 0:
            continue
        Lm[v, v] += a; Lm[w, w] += a; Lm[v, w] -= a; Lm[w, v] -= a
    bb = Lm[:9, :9]; bf = Lm[:9, 9:]; ff = Lm[9:, 9:]
    Lam = bb - bf @ np.linalg.pinv(ff, rcond=1e-12) @ bf.T
    return float(np.sum(Lam * (U @ U.T))), Lam


def Xstar(alpha, edges, U, nnode=31):
    """weighted least squares minimiser (per coordinate), anchors fixed."""
    Lm = np.zeros((nnode, nnode))
    for (v, w), a in zip(edges, alpha):
        if a <= 0:
            continue
        Lm[v, v] += a; Lm[w, w] += a; Lm[v, w] -= a; Lm[w, v] -= a
    free = np.arange(9, nnode)
    Xf = np.linalg.pinv(Lm[np.ix_(free, free)], rcond=1e-12) @ (-Lm[np.ix_(free, range(9))] @ U)
    return Xf


def ascent(edges, U, iters=4000, tol=1e-14):
    m = len(edges)
    alpha = np.ones(m)/m
    E, _ = energy(alpha, edges, U)
    step = 0.5
    for it in range(iters):
        X = Xstar(alpha, edges, U)
        full = np.vstack([U, X])
        g = np.array([np.sum((full[v]-full[w])**2) for (v, w) in edges])
        for _ in range(40):                       # backtracking on the simplex projection
            v = alpha + step*g
            u = np.sort(v)[::-1]
            css = np.cumsum(u)
            r = np.nonzero(u - (css-1)/(np.arange(m)+1) > 0)[0]
            th = (css[r[-1]]-1)/(r[-1]+1) if len(r) else 0.0
            proj = np.maximum(v-th, 0)
            E2, _ = energy(proj, edges, U)
            if E2 >= E - 1e-15:
                break
            step *= 0.5
        if E2 - E < tol*max(1.0, abs(E)):
            E = max(E, E2); alpha = proj if E2 >= E else alpha
            break
        E, alpha = E2, proj
        step *= 1.5
    return E, alpha


def cases():
    """structured extremal short-gap configurations (9 cyclic placements each)."""
    out = []
    for shift in range(9):
        base = [2*np.pi/9.0]*9
        for name, others in (("A: rest equal", None),
                             ("B: rest at cap L", "cap"),
                             ("C: rest near m", "min")):
            g = [0.0]*9
            g[shift] = 0.2
            rest = [i for i in range(9) if i != shift]
            rem = 2*np.pi - 0.2
            if others is None:
                vals = [rem/8.0]*8
            elif others == "cap":
                vals = []; acc = rem
                for k in range(8):
                    take = min(L, acc - (7-k)*max(0.0, acc - (7-k)*L))
                    v = min(L, acc)
                    vals.append(v); acc -= v
                vals = [min(L, rem/1.0) if k == 0 else 0.0 for k in range(8)]  # placeholder, fixed below
                vals = []
                acc = rem
                for k in range(8):
                    remaining = 7-k
                    lo = 2*np.pi - 8*L
                    v = min(L, max(lo, acc - remaining*L)) if remaining else acc
                    v = min(L, acc); vals.append(v); acc -= v
            else:
                lo = 2*np.pi - 8*L
                vals = []
                acc = rem
                for k in range(8):
                    remaining = 7-k
                    v = max(lo, acc - remaining*L)
                    v = min(L, max(lo, v)); vals.append(v); acc -= v
            for i, v in zip(rest, vals):
                g[i] = v
            if abs(sum(g) - 2*np.pi) < 1e-9 and min(g) > 0 and max(g) <= L + 1e-12:
                out.append(("%s shift %d" % (name, shift), g))
    return out


def main():
    edges, d = load_graph()
    P("=" * 100)
    P("GLOBAL SHORT-GAP SCREEN  (full-dual Dirichlet/effective-conductance bound; numeric proposal)")
    P("graph: %d edges, 31 nodes; anchors 0..8 (unit circle), sites 9..19, aux 20..30" % len(edges))
    P("L = 2 asin(19/50) = %.6f ; lower width bound m = 2 pi - 8L = %.6f" % (L, 2*np.pi - 8*L))
    P("")
    P("  case                        max_alpha E    V_lb = sqrt(E)   V_lb > 0.38 ?   path-only bound")
    worst = (1e9, None)
    for name, gaps in cases():
        gaps = np.array(gaps)
        U = anchors_from_gaps(gaps)
        # path-only calibration: best 2-edge path bound over the nine site paths
        chord = [np.linalg.norm(U[i] - U[(i+1) % 9]) for i in range(9)]
        pathb = max(c/(2*np.sqrt(2)) for c in chord)
        E, alpha = ascent(edges, U)
        vl = np.sqrt(max(E, 0.0))
        ok = vl > 0.38
        if vl < worst[0]:
            worst = (vl, name)
        P("  %-27s %.9f   %.9f      %-14s  %.6f" % (name, E, vl, ok, pathb))
    P("")
    P("VERDICT (numeric proposal): smallest bound over the tested short-gap extremal cases = %.9f at %s"
      % (worst[0], worst[1]))
    if worst[0] > 0.38:
        P("  => the full-dual bound EXCEEDS 0.38 on every tested case with a gap <= 0.2 (screen fires).")
    else:
        P("  => the bound does NOT exceed 0.38 there: the short-gap screen via this alpha family fails;")
        P("     either a stronger sub-network (3-anchor/Steiner) construction is needed, or the region")
        P("     genuinely admits V <= 0.38 (then the oracle inequality is false on that region).")
    P("")
    P("SCOPE: float arithmetic, numeric proposal only; NOT an interval certificate; structured extremal")
    P("cases, deliberately not a uniform grid.  A negative reading here is NOT a proof that the oracle")
    P("inequality fails, and the fixed-stress negative curvature says nothing about the oracle.")

    (OUT / "r20_short_gap_screen.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_short_gap_screen.txt"))


if __name__ == "__main__":
    main()
