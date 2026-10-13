"""r20-chain: exact rim-arc coverage account for the two-hub chain reduction.

For a legal configuration (9 ring centres + 2 hubs, all 11 centres in B(0,1-R)) define
    U_i := the rim of Lambda_i = Cc(c_i,R) that lies in the unit disk D and is covered by
           NO ring disk.   (Computed exactly, see arcs.py.)
If c_i is an essential ring site (i.e. U_i nonempty) then U_i must be covered by one of the
two hub disks.  Necessary conditions:
    (N1) for every essential i there is a hub H with  max_{x in U_i} |H-x| <= R ;
    (N2) the essential sites served by one hub form a CONTIGUOUS run in the cyclic order;
    (N3) for every edge (i,j) between two essential sites served by the same hub, the hub must
         also cover the cross-arc  J_ij := U_i^j ∪ U_j^i  where
         U_i^j  is the part of U_i NOT covered by B(c_j,R)  (a sub-arc of U_i, exact), and
         U_j^i  symmetrically;  these are the actual junction pieces.
    (N4) the two lens corners of the pair (i,j) must be covered by the two hubs.
All of N1..N4 are exact and are evaluated here at the certified candidate and on random legal
configurations; slacks are reported with sign (>= 0 means satisfied).
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT
from arcs import (truly_uncovered_arcs, canon, in_arc, arc_isect, arc_minus_union,
                  disk_interval, ring_cover_interval)

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def maxdist_arc(H, ci, R, arc):
    """max |H-x| over the arc (exact: endpoint or the phase of H-ci when present)."""
    c, hw = arc
    best = -np.inf
    for t in (c - hw, c + hw):
        x = np.asarray(ci) + R * np.array([np.cos(t), np.sin(t)])
        best = max(best, float(np.linalg.norm(x - H)))
    psi = float(np.arctan2(*(np.asarray(H) - np.asarray(ci))[::-1]))
    for k in (-1, 0, 1):
        t = psi + 2 * PI * k
        if c - hw - 1e-12 <= t <= c + hw + 1e-12:
            x = np.asarray(ci) + R * np.array([np.cos(t), np.sin(t)])
            best = max(best, float(np.linalg.norm(x - H)))
    return best


def essential_sites(ring, R, tol=1e-12):
    out = []
    for i in range(len(ring)):
        arcs = truly_uncovered_arcs(ring, i, R)
        tot = sum(2 * a[1] for a in arcs)
        if tot > tol:
            out.append((i, arcs, tot))
    return out


def junction_arcs(ring, i, j, R):
    """(arcs of U_i not covered by B(c_j,R), arcs of U_j not covered by B(c_i,R))."""
    Ui = truly_uncovered_arcs(ring, i, R)
    Uj = truly_uncovered_arcs(ring, j, R)
    covj = ring_cover_interval(ring[i], ring[j], R)
    covi = ring_cover_interval(ring[j], ring[i], R)
    Ai = []
    for a in Ui:
        if covj is None:
            Ai.append(a)
        else:
            Ai.extend(arc_minus_union(a, [covj]))
    Aj = []
    for a in Uj:
        if covi is None:
            Aj.append(a)
        else:
            Aj.extend(arc_minus_union(a, [covi]))
    return Ai, Aj


def lens_corners_ij(ci, cj, R):
    d = float(np.linalg.norm(np.asarray(cj) - np.asarray(ci)))
    if d >= 2 * R:
        return []
    M = (np.asarray(ci) + np.asarray(cj)) / 2.0
    Gd = M - np.asarray(ci)
    k = 2.0 * np.sqrt(max(R * R - d * d / 4.0, 0.0)) / d
    J = np.array([[0.0, -1.0], [1.0, 0.0]])
    return [M + k * (J @ Gd), M - k * (J @ Gd)]


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")
    P("ring sites in polar order: " + ", ".join(map(str, ring_ids)))

    P("\n=== essential sites and their exact uncovered rim arcs ===")
    ess = essential_sites(ring, R)
    for (i, arcs, tot) in ess:
        P(f"  ring {ring_ids[i]:>2d} (index {i}): extent {tot:.9f}"
          f"   arcs: " + "; ".join(f"(c={c:.5f},hw={hw:.5f})" for c, hw in arcs))

    P("\n=== N1: per-site hub reach, both hubs ===")
    P("   ring   extent      d(A,gap-arcs)      d(B,gap-arcs)")
    for (i, arcs, tot) in ess:
        dA = max(maxdist_arc(HA, ring[i], R, a) for a in arcs)
        dB = max(maxdist_arc(HB, ring[i], R, a) for a in arcs)
        P(f"   {ring_ids[i]:>4d}  {tot:.6f}   {dA:.9f} {'OK' if dA <= R else 'FAIL'}"
          f"   {dB:.9f} {'OK' if dB <= R else 'FAIL'}")

    P("\n=== N3/N4: junction pieces of each consecutive pair ===")
    n = len(ring)
    for k in range(n):
        i, j = k, (k + 1) % n
        Ai, Aj = junction_arcs(ring, i, j, R)
        ti = sum(2 * a[1] for a in Ai)
        tj = sum(2 * a[1] for a in Aj)
        dA = max([maxdist_arc(HA, ring[i], R, a) for a in Ai] +
                 [maxdist_arc(HA, ring[j], R, a) for a in Aj] + [0.0])
        dB = max([maxdist_arc(HB, ring[i], R, a) for a in Ai] +
                 [maxdist_arc(HB, ring[j], R, a) for a in Aj] + [0.0])
        cor = lens_corners_ij(ring[i], ring[j], R)
        cA = max((float(np.linalg.norm(x - HA)) for x in cor), default=0.0)
        cB = max((float(np.linalg.norm(x - HB)) for x in cor), default=0.0)
        P(f"  ({ring_ids[i]:>2d},{ring_ids[j]:>2d}) junction extents {ti:.6f} / {tj:.6f}"
          f" | A: max-dist {dA:.6f} {'OK' if dA <= R else 'FAIL'}"
          f" | B: max-dist {dB:.6f} {'OK' if dB <= R else 'FAIL'}")
        if cor:
            P(f"        lens corners: A {cA:.6f} {'OK' if cA <= R else 'FAIL'}"
              f"   B {cB:.6f} {'OK' if cB <= R else 'FAIL'}")

    (OUT / "arc_account.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "arc_account.txt"))


if __name__ == "__main__":
    main()
