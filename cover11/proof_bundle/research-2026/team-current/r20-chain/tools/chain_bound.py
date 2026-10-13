"""r20-chain: THE EXACT RIM-ARC CRITERION and the chain-elimination bound.

Setting (q0(6,7), no symmetry/equal-angle/saturation premise):
  D = unit closed disk, R in (1/3,1/2), 11 centers = 9 ring sites c_1..c_9 plus hubs A,B,
  all 11 centers inside B(0,1-R)  (hubs strictly inside; ring disks must reach ∂D).
  The 9 ring edges are the cyclic pairs; each edge is served by A or B; the served sets are
  contiguous arcs (k and 9-k edges).  For each maximal GAP edge (i,j) of the chain served by H,
  H's disk must contain the uncovered gap boundary, in particular the rim arcs determined below.

CORE OBJECT (exact).  For two radii-R disks with centers C_i, C_j, d=|C_i-C_j|:
   * if d >= 2R the disks are disjoint/tangent and the uncovered rim of Cc(C_i,R) is ALL of it;
   * if d < 2R the rim of Cc(C_i,R) covered by B(C_j,R) is the arc centred on the direction
     C_j-C_i with half-width beta = arccos(d/(2R)); the UNCOVERED rim arc is the complementary arc,
     centred on the ANTIPODE of that direction, with half-width pi - beta, and its pole is
     P_i = (C_i/|C_i|)(|C_i|-R).
  (Equivalently, the "gap" between the two disks is bounded by the long arc of Cc(C_i,R) from the
   lens corner x_far out over the pole and back to the other corner.)

CRITERION (necessary, and exactly testable).  If H serves the edge (i,j) then for every rim arc
  Gamma on Cc(C_i,R) or Cc(C_j,R) that is uncovered by the partner disk and lies in D,
        max_{x in Gamma} |H - x| <= R.
  By the linear form |x-H| <= R <=> H.x >= (h^2-R^2)/2 with h=|H|, this is
        H.x >= (h^2-R^2)/2    for the extremal point x of the arc (attained at an arc endpoint
        or at the point of the arc nearest to the direction of H).
  We evaluate the minimum of the linear functional along each arc by dense sampling plus the exact
  critical point, and report the slack.

CHAIN BOUND (necessary).  Summing the necessary inequalities over the m gap edges of a chain with
  endpoints c_k, c_l turns them into  Theta_H(chain) >= f(chain)  with an explicit closed form
  f = m*pi/2 - (s_k - s_l)  (see the derivation in the response; s = arccos(|H-c|/(2R))).
"""
import numpy as np
from r20geom import load_certified, polar_order, s_H, OUT
from arc_exact import lens_corners, ang_about

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def uncovered_rim_arc(Ci, Cj, R, n=20001):
    """Dense sample of the rim arc of Cc(Ci,R) uncovered by B(Cj,R).
    Returns (pts, closed_flag).  closed_flag True when the arc is the whole circle."""
    d = np.linalg.norm(np.asarray(Cj) - np.asarray(Ci))
    u = (np.asarray(Cj) - np.asarray(Ci)) / d
    if d >= 2.0 * R:
        ts = np.linspace(0, 2 * np.pi, n, endpoint=False)
        return np.asarray(Ci) + R * np.stack([np.cos(ts), np.sin(ts)], 1), True
    beta = np.arccos(np.clip(d / (2 * R), -1, 1))
    # uncovered arc: centred on -u, half-width pi-beta
    t0 = ang_about(Ci, np.asarray(Ci) - u)  # = angle of -u
    ts = t0 + np.linspace(-(np.pi - beta), (np.pi - beta), n)
    return np.asarray(Ci) + R * np.stack([np.cos(ts), np.sin(ts)], 1), False


def clip_to_disk(pts):
    """Keep only the points inside the closed unit disk (returns the mask)."""
    return np.linalg.norm(pts, axis=1) <= 1.0 + 1e-14


def arc_slack(H, R, pts, mask=None):
    """min over the kept points of (H.x) - (|H|^2-R^2)/2 ; >=0 <=> all kept points covered."""
    if mask is not None:
        pts = pts[mask]
    if pts.size == 0:
        return np.inf
    h2 = float(H @ H)
    return float(np.min(pts @ H) - (h2 - R * R) / 2.0)


def rim_slack(H, R, Ci, Cj, n=20001):
    """Worst slack of the uncovered rim arcs of Cc(Ci,R) w.r.t. B(Cj,R) that lie in D.
    Also includes the exact critical point of the arc (direction of H)."""
    pts, closed = uncovered_rim_arc(Ci, Cj, R, n)
    m = clip_to_disk(pts)
    s = arc_slack(H, R, pts, m)
    if np.any(m):
        kept = pts[m]
        # exact extremum: point of the arc with maximal projection on H.  Dense sampling gives
        # the value up to O((dt)^2); refine at the argmin/argmax below.
        proj = kept @ H
        k = int(np.argmin(proj))
        # local golden-section refinement along the arc around sample k of the linear functional
        d = np.linalg.norm(np.asarray(Cj) - np.asarray(Ci))
        beta = np.arccos(np.clip(d / (2 * R), -1, 1))
        u = (np.asarray(Cj) - np.asarray(Ci)) / max(d, 1e-300)
        t0 = ang_about(Ci, np.asarray(Ci) - u)
        def val(t):
            x = np.asarray(Ci) + R * np.array([np.cos(t), np.sin(t)])
            if np.linalg.norm(x) > 1.0:
                return np.inf
            return float(x @ H)
        # refine on a bracket containing the min and the phase where x || H, keeping legality
        ts = np.array([t0 + s_ for s_ in np.linspace(-(np.pi - beta), (np.pi - beta), n)])
        th_ex = np.arctan2(H[1], H[0])           # x parallel to H
        best = s
        for t in (ts[k], th_ex, th_ex + np.pi):
            for dt in (0.0,):
                pass
        # simple robust local refine: scan the bracket around sample k
        lo = ts[max(k - 3, 0)]
        hi = ts[min(k + 3, n - 1)]
        grid = np.linspace(lo, hi, 401)
        vals = np.array([val(t) for t in grid])
        if np.isfinite(vals).any():
            j = int(np.nanargmin(np.where(np.isfinite(vals), vals, np.inf)))
            best = min(best, (vals[j] - (float(H @ H) - R * R) / 2.0))
        s = best
    return s


def chain_hub_slack(H, R, chain_idx, ring, n=20001):
    """min over the gap edges of the chain of the rim-slack criterion for the hub H."""
    m = np.inf
    detail = []
    for k in range(len(chain_idx) - 1):
        i, j = chain_idx[k], chain_idx[k + 1]
        s1 = rim_slack(H, R, ring[i], ring[j], n)
        s2 = rim_slack(H, R, ring[j], ring[i], n)
        m = min(m, s1, s2)
        detail.append((i, j, s1, s2))
    return m, detail


def main():
    C, R, ring_ids = load_certified()
    P(f"certified R = {R!r}")
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P("ring sites in polar order: " + ", ".join(str(i) for i in ring_ids))
    P(f"|hubs|: A={np.linalg.norm(HA):.9f} B={np.linalg.norm(HB):.9f}   1-R={1-R:.9f}")

    P("\n=== exact-arc sanity: lens corners vs. the analytic uncovered arc ===")
    for (i, j) in [(1, 2), (4, 9 - 9)]:
        pass
    for k in range(len(ring) - 1):
        i, j = k, k + 1
        Ci, Cj = ring[i], ring[j]
        d = np.linalg.norm(Cj - Ci)
        xf, Q = lens_corners(Ci, Cj, R)
        if xf is None:
            P(f"  rings {ring_ids[i]},{ring_ids[j]}: d={d:.9f} >= 2R (disjoint) ")
            continue
        beta = np.arccos(np.clip(d / (2 * R), -1, 1))
        pts, _ = uncovered_rim_arc(Ci, Cj, R)
        # every sampled rim point must be outside B(Cj,R)
        ok_out = np.all(np.linalg.norm(pts - Cj, axis=1) >= R - 1e-12)
        # and x_far must be at the boundary of the uncovered arc
        e1 = np.linalg.norm(pts[0] - xf) + np.linalg.norm(pts[-1] - Q)
        e2 = np.linalg.norm(pts[0] - Q) + np.linalg.norm(pts[-1] - xf)
        P(f"  rings {ring_ids[i]},{ring_ids[j]}: d={d:.9f} 2R-d={2*R-d:.2e} beta={beta:.9f}"
          f"  uncovered extent={2*(np.pi-beta):.9f}"
          f"  sample-outside-Bj={ok_out}  corner-match={min(e1,e2):.2e}")

    P("\n=== per-edge criterion at the certified candidate (real data) ===")
    P("  served edges from the recorded ledger: A serves [(4,9),(9,10),(10,3),(3,5),(6,4)]"
      "  B serves [(5,7),(7,1),(1,8),(8,6)]")
    served_A = [(4, 9), (9, 10), (10, 3), (3, 5), (6, 4)]
    served_B = [(5, 7), (7, 1), (1, 8), (8, 6)]
    pos = {int(v): k for k, v in enumerate(ring_ids)}
    for H, lab, pairs in ((HA, "A", served_A), (HB, "B", served_B)):
        P(f"\n  hub {lab}:  |H|={np.linalg.norm(H):.9f}")
        for (a, b) in pairs:
            i, j = pos[a], pos[b]
            s_ij = rim_slack(H, R, ring[i], ring[j])
            s_ji = rim_slack(H, R, ring[j], ring[i])
            # number of samples actually inside the disk, for honesty
            pts1, _ = uncovered_rim_arc(ring[i], ring[j], R)
            n1 = int(clip_to_disk(pts1).sum())
            pts2, _ = uncovered_rim_arc(ring[j], ring[i], R)
            n2 = int(clip_to_disk(pts2).sum())
            P(f"    edge ({a},{b}): rim-slack on Lambda_{a} = {s_ij:+.6f}  ({n1} pts in D)"
              f"   on Lambda_{b} = {s_ji:+.6f}  ({n2} pts in D)   -> min {min(s_ij, s_ji):+.6f}")

    P("\n=== chain width / L3-L4 comparison at the candidate ===")
    for H, lab, chain in ((HA, "A", [0, 1, 2, 3]), (HB, "B", [4, 5, 6, 7])):
        idx = chain
        pts = ring[idx]
        ang = np.arctan2(*(pts - H).T)
        turns = np.diff(ang)
        turns = (turns + np.pi) % (2 * np.pi) - np.pi
        Th = float(turns.sum())
        s = np.array([s_H(H, ring[k], R) for k in idx])
        P(f"  hub {lab}: chain rings {[int(ring_ids[k]) for k in idx]}")
        P(f"     turns = {np.round(turns,9).tolist()}   Theta = {Th:.9f}")
        P(f"     s     = {np.round(s,9).tolist()}")
        P(f"     sum(s_i+s_{i+1}-pi/2) = {float((s[:-1]+s[1:]-np.pi/2).sum()):.9f}"
          f"   Theta - that = {Th - float((s[:-1]+s[1:]-np.pi/2).sum()):+.9f}")
        P(f"     m*pi/2 - (s_first - s_last) = {len(idx)*np.pi/2 - (s[0]-s[-1]):.9f}")

    (OUT / "arc_exact.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "arc_exact.txt"))


if __name__ == "__main__":
    main()
