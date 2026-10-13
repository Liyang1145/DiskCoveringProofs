"""r20-chain: the exact VERTEX criterion for the residual set of the two-hub chain reduction.

Residual set (what the hub disks must cover additionally to the 9 ring disks):
    Res := D \\ (union of the 9 ring disks).
Its boundary is made of arcs of the 9 circles Lambda_i and of arcs of the unit circle ∂D
(the latter are ALREADY covered by the ring disks, since |c_i| >= 1-R).  Hence:

  **Vertex criterion (necessary and sufficient for Res ⊆ B(H_A,R) ∪ B(H_B,R))**
     for every vertex V of the arrangement -- i.e. every intersection of two circle boundaries
     Lambda_i ∩ Lambda_j and every intersection Lambda_i ∩ ∂D that lies in Res -- there is a hub
     H with |H - V| <= R,
  combined with the statement that every remaining boundary arc has both endpoints covered by the
  SAME hub (needed because a disk is convex; a single arc must not be split between the two hubs).
  For an arc A of Lambda_i with endpoints P,Q: A ⊆ B(H,R) iff |H-P|<=R, |H-Q|<=R and
  max_{x in A}|H-x| <= R, the max attained at an endpoint or at the phase of H-c_i.

This file: (a) computes the exact uncovered arcs of the certified candidate and its vertices;
(b) verifies the criterion there; (c) evaluates the criterion as an exclusion test on random
legal configurations and reports the slack with sign.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT
from arcs import (truly_uncovered_arcs, canon, in_arc, arc_isect, disk_interval,
                  ring_cover_interval)

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def circle_circle_x(C1, R, C2):
    """Intersection points of Cc(C1,R) and Cc(C2,R) (same radius)."""
    d = float(np.linalg.norm(np.asarray(C2) - np.asarray(C1)))
    if d >= 2 * R or d <= 1e-15:
        return []
    M = (np.asarray(C1) + np.asarray(C2)) / 2.0
    Gd = M - np.asarray(C1)
    k = 2.0 * np.sqrt(max(R * R - d * d / 4.0, 0.0)) / d
    J = np.array([[0.0, -1.0], [1.0, 0.0]])
    return [M + k * (J @ Gd), M - k * (J @ Gd)]


def arc_maxdist(H, ci, R, arc):
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


def residual_vertices(ring, R):
    """All arrangement vertices that lie in Res (in D, outside every ring disk)."""
    n = len(ring)
    cand = []
    for i in range(n):
        for j in range(i + 1, n):
            cand.extend(circle_circle_x(ring[i], R, ring[j]))
        I = disk_interval(ring[i], R)
        if I is not None:
            for t in (I[0] - I[1], I[0] + I[1]):
                cand.append(ring[i] + R * np.array([np.cos(t), np.sin(t)]))
    out = []
    for x in cand:
        if np.linalg.norm(x) > 1.0 + 1e-12:
            continue
        d = [np.linalg.norm(x - ring[k]) for k in range(n)]
        if min(d) > R + 1e-12:
            out.append(np.asarray(x, float))
    return out


def vertex_slack(ring, R, hA, hB):
    """min over residual vertices of max(0, dist to nearest hub - R): >=0 iff all vertices are
    within one hub's disk."""
    V = residual_vertices(ring, R)
    if not V:
        return np.inf, 0
    worst = np.inf
    for x in V:
        da = float(np.linalg.norm(x - hA))
        db = float(np.linalg.norm(x - hB))
        worst = min(worst, R - min(da, db))
    return worst, len(V)


def arc_cover_slack(ring, R, hA, hB):
    """For every uncovered boundary arc: the best hub's slack R - maxdist; and whether a single
    hub covers the whole arc.  Returns (min single-hub arc slack, list of (i, slackA, slackB))."""
    out = []
    worst = np.inf
    for i in range(len(ring)):
        for a in truly_uncovered_arcs(ring, i, R):
            sA = R - arc_maxdist(hA, ring[i], R, a)
            sB = R - arc_maxdist(hB, ring[i], R, a)
            best = max(sA, sB)
            worst = min(worst, best)
            out.append((i, sA, sB, a))
    return worst, out


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}; ring order " + ", ".join(map(str, ring_ids)))

    P("\n=== residual vertices of the certified candidate ===")
    V = residual_vertices(ring, R)
    P(f"  {len(V)} residual arrangement vertices (in D, outside all 9 ring disks)")
    P("     vertex                          |v|        d(A)      d(B)   nearest")
    for x in V:
        da = float(np.linalg.norm(x - HA))
        db = float(np.linalg.norm(x - HB))
        P(f"   ({x[0]:+.6f},{x[1]:+.6f})   {np.linalg.norm(x):.6f}   {da:.6f}  {db:.6f}"
          f"   {'A' if da <= db else 'B'}   R-dist={R - min(da, db):+.3e}")

    vs, nv = vertex_slack(ring, R, HA, HB)
    P(f"\n  VERTEX SLACK (min over vertices of R - dist to nearest hub) = {vs:+.6e}")

    P("\n=== single-hub coverage of each uncovered arc ===")
    ws, det = arc_cover_slack(ring, R, HA, HB)
    for (i, sA, sB, a) in det:
        P(f"  ring {ring_ids[i]:>2d} arc (c={a[0]:.5f},hw={a[1]:.5f}):"
          f" slack_A={sA:+.6f}  slack_B={sB:+.6f}  best={max(sA,sB):+.6f}"
          f"  -> {'A' if sA >= sB else 'B'}")
    P(f"  worst single-hub arc slack = {ws:+.6f}")

    P("\n=== exclusion test on random legal configurations ===")
    rng = np.random.default_rng(21)
    for RR in (0.34, 0.36, 0.38, 0.3901, 0.40, 0.42, 0.45):
        worst = np.inf
        nfail = 0
        for trial in range(300):
            hA = rng.uniform(-1, 1, 2) * (1 - RR)
            hB = rng.uniform(-1, 1, 2) * (1 - RR)
            th = np.sort(rng.uniform(0, 2 * PI, 9))
            rho = np.sqrt(rng.uniform((1 - RR) ** 2, 1.0, 9))
            rr = np.stack([rho * np.cos(th), rho * np.sin(th)], 1)
            v, nv = vertex_slack(rr, RR, hA, hB)
            if v < worst:
                worst = v
            if v < 0:
                nfail += 1
        P(f"  R={RR:.4f}: min vertex slack over 300 random configs = {worst:+.6f}"
          f"   ({nfail} configs with negative slack)")

    (OUT / "vertex_criterion.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "vertex_criterion.txt"))


if __name__ == "__main__":
    main()
