"""r20-chain: verify the four exact laws used by the chain elimination, then measure margins.

L1 (pole law)      : for a circle Cc(C,R) with |C|=:L>R, the function u -> |u| restricted to the
                     circle attains its minimum at the pole P=(C/L)(L-R).  Hence
                     arc A (subset of the circle) is contained in the hub disk B(H,R) iff
                     |H-P| <= R **provided P is the extremal point of A w.r.t. H**.  Concretely:
                     max_{u in A} |H-u| is attained at P or at an endpoint of A; so
                     "P in B(H,R) and both endpoints in B(H,R)"  <=>  A subset B(H,R).
L1' (root identity): for the unit-circle cut points x_+, x_- of Cc(C,R),
                     (a-R)(b-R) = 1-R^2 with a = L-R (pole norm), b = L+R (antipole norm).
L2 (interface)     : for consecutive chain rings c_i, c_{i+1} the uncovered piece of Lambda_i
                     (the unit-circle part of Cc(c_i,R) that no ring disk covers) meets Lambda_{i+1}
                     exactly at the unit-circle points: verified by direct sampling.
L3 (per-edge)      : hub covering interface (i,i+1)  ==>  theta_H(i,i+1) >= s_i + s_{i+1} - pi/2.
L4 (whole chain)   : summing L3 over the chain gives  Theta_H(chain) >= m*pi/2 + (s_last - s_first).

Everything is measured; margins are reported with sign so that a violation is visible.
"""
import numpy as np
from r20geom import (load_certified, polar_order, circle_arc_isect_unit, arc_distance_range,
                     s_H, OUT)

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


# ---------------------------------------------------------------- L1 pole law
def test_pole_law(rings, R, ntrials=4000, seed=0):
    rng = np.random.default_rng(seed)
    worst_ok, worst_fail = 1e9, -1e9
    fail = None
    for _ in range(ntrials):
        L = rng.uniform(R + 1e-6, 1.6)
        th = rng.uniform(0, 2 * np.pi)
        C = L * np.array([np.cos(th), np.sin(th)])
        u = C / L
        n = np.array([-u[1], u[0]])
        t0 = rng.uniform(0, 2 * np.pi)
        t1 = t0 + rng.uniform(1e-4, 2 * np.pi - 1e-4)
        pt = lambda t: C + R * np.array([np.cos(t), np.sin(t)])
        # random hub inside B(0,1-R)
        H = rng.uniform(-1, 1, 2) * (1 - R)
        pole = (C / L) * (L - R)
        ts = np.linspace(t0, t1, 401)
        pts = np.stack([pt(t) for t in ts])
        far = np.max(np.linalg.norm(pts - H, axis=1))
        # candidate extremal set: endpoints + pole if the pole is on the arc
        cand = [np.linalg.norm(pt(t0) - H), np.linalg.norm(pt(t1) - H)]
        tp = np.arctan2(*((-C)[::-1]))
        if ((tp - t0) % (2 * np.pi)) <= (t1 - t0) + 1e-15:
            cand.append(np.linalg.norm(pole - H))
        cfar = max(cand)
        d = far - cfar
        if d > 1e-9:
            if d > worst_fail:
                worst_fail, fail = d, (L, th, t0, t1, H)
        worst_ok = min(worst_ok, d)
    return worst_ok, worst_fail, fail


# ------------------------------------------------------- L2 interface by sampling
def uncovered_piece(Ci, Cj, R, M=2001):
    """Return the list of sample points on Cc(Ci,R) that (a) lie in the closed unit disk and
    (b) are NOT covered by the disk B(Cj,R).  The maximal such run is the interface piece."""
    ts = np.linspace(0, 2 * np.pi, M, endpoint=False)
    pts = Ci + R * np.stack([np.cos(ts), np.sin(ts)], 1)
    inside = np.linalg.norm(pts, axis=1) <= 1.0
    notcov = np.linalg.norm(pts - Cj, axis=1) > R
    ok = inside & notcov
    return ts, pts, ok


def run_interface_test(ring, hub, ring_ids, R, label):
    P(f"\n=== L2/L3 interface test  [{label}] ===")
    s_all = np.array([s_H(hub, c, R) for c in ring])
    order = polar_order(ring)
    ring, s_all = ring[order], s_all[order]
    ids = ring_ids[order]
    fin = np.isfinite(s_all)
    P("  chain rings (finite spoke deficit): " + ", ".join(str(i) for i in ids[fin]))
    P(f"  s values: " + " ".join(f"{i}:{v:.6f}" for i, v in zip(ids, s_all)))
    ang = np.arctan2(*(ring - hub).T)
    idx = np.where(fin)[0]
    worst_l3 = 1e9
    for k in range(len(idx) - 1):
        i, j = idx[k], idx[k + 1]
        Ci, Cj = ring[i], ring[j]
        # angular turn between the two spokes about H (principal value)
        d = ang[j] - ang[i]
        d = (d + np.pi) % (2 * np.pi) - np.pi
        th = d
        bound = s_all[i] + s_all[j] - np.pi / 2
        slack = th - bound
        # sampling check of the interface arcs
        #   piece on Lambda_i not covered by ring j and inside the unit disk
        alpha_i, mn_i, mx_i = arc_profile(Ci, Cj, R)
        alpha_j, mn_j, mx_j = arc_profile(Cj, Ci, R)
        P(f"   edge ({ids[i]},{ids[j]}): turn={th:+.6f}  L3 bound={bound:+.6f}  slack={slack:+.6f}")
        P(f"        interface on Lambda_{ids[i]}: angular extent {alpha_i:.6f}"
          f"   min|.{'':0}| to origin {mn_i:.6f} max {mx_i:.6f}")
        P(f"        interface on Lambda_{ids[j]}: angular extent {alpha_j:.6f}"
          f"   min to origin {mn_j:.6f} max {mx_j:.6f}")
        worst_l3 = min(worst_l3, slack)
    P(f"   worst L3 slack over the chain = {worst_l3:+.6f}")
    return worst_l3


def arc_profile(Ci, Cj, R, M=4001):
    """Angular extent (about Ci) of the largest run of points of Cc(Ci,R) that are inside the
    closed unit disk and not covered by B(Cj,R).  Returns (extent, min radius, max radius)."""
    ts, pts, ok = uncovered_piece(Ci, Cj, R, M)
    if not ok.any():
        return 0.0, np.inf, -np.inf
    # find the longest cyclic run
    runs, cur = [], []
    for k in range(len(ok)):
        if ok[k]:
            cur.append(k)
        else:
            if cur:
                runs.append(cur)
            cur = []
    if cur:
        runs.append(cur)
    if len(runs) > 1 and runs[0][0] == 0 and runs[-1][-1] == len(ok) - 1:
        runs[0] = runs[-1] + runs[0]
        runs.pop()
    run = max(runs, key=len)
    ptsr = pts[run]
    rr = np.linalg.norm(ptsr, axis=1)
    extent = (len(run) - 1) * 2 * np.pi / M
    return extent, rr.min(), rr.max()


# ---------------------------------------------------------------------- main
def main():
    C, R, ring_ids = load_certified()
    P(f"certified R = {R!r}")
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring = ring[o]
    ring_ids = ring_ids[o]

    P("\n=== L1 pole law: is max_{arc} |H-u| attained at {endpoints} u {pole} ? ===")
    w_ok, w_fail, fail = test_pole_law(ring, R)
    P(f"  random arcs tested; worst (far - candidate-far) = {w_ok:.3e}  (<=0 means supported)")
    P(f"  worst violation over 4000 random arcs = {w_fail:.3e}")

    P("\n=== L1' root identity (a-R)(b-R) = 1-R^2 at the candidate ===")
    for i, c in enumerate(ring):
        L = np.linalg.norm(c)
        if L <= 1 + R:
            a, b = L - R, L + R
            P(f"  ring {ring_ids[i]:>2d}: L={L:.9f}  (a-R)(b-R)={((a - R) * (b - R)):.12f}"
              f"   1-R^2={1 - R * R:.12f}   err={(a - R) * (b - R) - (1 - R * R):+.2e}")

    P("\n=== L1'' circle/unit-disk cut points, analytic vs quadratic roots ===")
    for i, c in enumerate(ring):
        L = np.linalg.norm(c)
        inter = circle_arc_isect_unit(c, R)
        if inter is None:
            continue
        t1, t2 = inter
        x1 = c + R * np.array([np.cos(t1), np.sin(t1)])
        x2 = c + R * np.array([np.cos(t2), np.sin(t2)])
        disc = L * L + R * R - 1
        aa = (L * L + R * R - 1) / (2 * L)
        hh = np.sqrt(max(R * R - aa * aa, 0))
        u = c / L
        n = np.array([-u[1], u[0]])
        y1, y2 = aa * u + hh * n, aa * u - hh * n
        e = min(np.linalg.norm(x1 - y1) + np.linalg.norm(x2 - y2),
                np.linalg.norm(x1 - y2) + np.linalg.norm(x2 - y1))
        P(f"  ring {ring_ids[i]:>2d}: |x_+-y_+-| = {e:.3e}   |x1|={np.linalg.norm(x1):.15f}"
          f"  |x2|={np.linalg.norm(x2):.15f}")

    for hub, lab in ((HA, "A (center 0)"), (HB, "B (center 2)")):
        run_interface_test(ring, hub, ring_ids, R, lab)

    P("\n=== candidate cross-check: the six tight faces of the certified object ===")
    tight = [(0, 9, 10), (0, 2, 5), (0, 3, 5), (2, 6, 8), (2, 5, 7), (0, 4, 6)]
    obj_r = np.array([[0.379983853119838708, 0], [0, 0], [0, 0]])
    for (a, b, c) in tight:
        pts = np.array([C[a], C[b], C[c]])
        # circumradius of a triangle
        A = np.linalg.norm(pts[1] - pts[2]); Bb = np.linalg.norm(pts[0] - pts[2])
        Cc = np.linalg.norm(pts[0] - pts[1])
        s = (A + Bb + Cc) / 2
        area = np.sqrt(max(s * (s - A) * (s - Bb) * (s - Cc), 0))
        rho = A * Bb * Cc / (4 * area)
        P(f"  face {a,b,c}: circumradius={rho:.15f}   R-rho={R - rho:+.3e}")

    (OUT / "chain_verify.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "chain_verify.txt"))


if __name__ == "__main__":
    main()
