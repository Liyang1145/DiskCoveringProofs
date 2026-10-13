"""r20-chain: apply the exact gap-arc necessary condition to the certified candidate and to
random legal configurations.  Reports slacks with sign; no grid search is used for the test."""
import numpy as np
from r20geom import load_certified, polar_order, s_H, OUT
from gap_arc import cover_slack, gap_arcs, beta_of

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")
    P("ring order: " + ", ".join(map(str, ring_ids)))

    # served edges of the chain (the ring 9-cycle; consecutive in the cyclic order above)
    n = len(ring)
    P("\n=== EXACT gap-arc coverage, certified candidate ===")
    P("   edge list of the 9-cycle (i,i+1 at the ring-order level):")
    for k in range(n):
        i, j = k, (k + 1) % n
        a, b = int(ring_ids[i]), int(ring_ids[j])
        d = float(np.linalg.norm(ring[j] - ring[i]))
        bta = beta_of(d, R)
        sa = s_H(HA, ring[i], R)
        sb = s_H(HB, ring[i], R)
        ser = "A" if np.isfinite(sa) and (not np.isfinite(sb) or True) else "?"
        P(f"   ({a:>2d},{b:>2d}): d={d:.9f}  beta={bta:.9f}  uncovered extent={np.pi-2*bta:.9f}")
    P("")

    served = {"A": [(4, 9), (9, 10), (10, 3), (3, 5), (6, 4)],
              "B": [(5, 7), (7, 1), (1, 8), (8, 6)]}
    pos = {int(v): k for k, v in enumerate(ring_ids)}
    for lab, H, pairs in (("A", HA, served["A"]), ("B", HB, served["B"])):
        P(f"\n  hub {lab} |H|={np.linalg.norm(H):.9f}")
        for (a, b) in pairs:
            i, j = pos[a], pos[b]
            s1, x1, e1 = cover_slack(H, R, ring[i], ring[j])
            s2, x2, e2 = cover_slack(H, R, ring[j], ring[i])
            P(f"    edge ({a},{b}): slack on Lambda_{a} = {s1:+.6f} (arc len {e1:.6f},"
              f" argmax={np.round(x1,6) if x1 is not None else None})")
            P(f"                slack on Lambda_{b} = {s2:+.6f} (arc len {e2:.6f})"
              f"   -> min {min(s1,s2):+.6f}")

    P("\n=== the decisive question: can a hub cover both gap arcs of ANY edge? ===")
    P("   (for each edge, the best possible hub is obtained by minimising max_x |H-x| over")
    P("    the two gap arcs; that minimum is a pure geometric number, computed by direct search")
    P("    on the plane, and is a LOWER bound on what any hub can do.)")

    def best_hub_for_edge(i, j, R, ring):
        arcs1 = gap_arcs(ring[i], ring[j], R)
        arcs2 = gap_arcs(ring[j], ring[i], R)
        # sample the arcs to get point sets; the optimal hub centre for two compact sets is
        # the centre of the minimal enclosing circle (approximated by fine sampling + refine)
        pts = []
        for (ci, arcs) in ((ring[i], arcs1), (ring[j], arcs2)):
            for (lo, hi) in arcs:
                t = np.linspace(lo, hi, 601)
                pts.append(np.asarray(ci) + R * np.stack([np.cos(t), np.sin(t)], 1))
        pts = np.vstack(pts)
        # 1-centre of a point set: Welzl-like via repeated smallest-enclosing from candidates
        from scipy.optimize import minimize
        c0 = pts.mean(0)
        f = lambda z: np.max(np.linalg.norm(pts - z, axis=1))
        res = minimize(f, c0, method="Nelder-Mead",
                       options=dict(maxiter=20000, maxfev=40000, xatol=1e-12, fatol=1e-14))
        return res.fun, res.x

    for k in range(n):
        i, j = k, (k + 1) % n
        val, hopt = best_hub_for_edge(i, j, R, ring)
        P(f"   edge ({int(ring_ids[i]):>2d},{int(ring_ids[j]):>2d}): min over hub positions of"
          f" max gap-arc distance = {val:.9f}   (R = {R:.9f},  R - val = {R - val:+.3e})"
          f"   at |h|={np.linalg.norm(hopt):.6f}")

    P("\n=== random legal configurations: is the per-edge criterion ever violated? ===")
    rng = np.random.default_rng(11)
    worst = 1e9
    worst_case = None
    for trial in range(300):
        hA = rng.uniform(-1, 1, 2) * (1 - R)
        hB = rng.uniform(-1, 1, 2) * (1 - R)
        th = np.sort(rng.uniform(0, 2 * np.pi, 9))
        rho = np.sqrt(rng.uniform((1 - R) ** 2, 1.0, 9))
        rr = np.stack([rho * np.cos(th), rho * np.sin(th)], 1)
        for lab, H in (("A", hA), ("B", hB)):
            s = np.array([s_H(H, c, R) for c in rr])
            fin = np.isfinite(s)
            # find maximal runs of fin-index rings in cyclic order = candidate chains
            idx = list(np.where(fin)[0])
            if len(idx) < 2:
                continue
            # split into cyclic runs
            runs, cur = [], [idx[0]]
            for k in range(1, len(idx)):
                if idx[k] == idx[k - 1] + 1:
                    cur.append(idx[k])
                else:
                    runs.append(cur)
                    cur = [idx[k]]
            runs.append(cur)
            if len(runs) > 1 and runs[0][0] == 0 and runs[-1][-1] == 8:
                runs[0] = runs.pop() + runs[0]
            for run in runs:
                for k in range(len(run) - 1):
                    i, j = run[k], run[k + 1]
                    s1, _, _ = cover_slack(H, R, rr[i], rr[j])
                    s2, _, _ = cover_slack(H, R, rr[j], rr[i])
                    m = min(s1, s2)
                    if m < worst:
                        worst, worst_case = m, (trial, lab, i, j, H.copy(), rr.copy())
    P(f"   smallest per-edge slack over 300 random legal configurations: {worst:+.6f}")
    if worst_case is not None:
        P(f"   worst case: trial={worst_case[0]} hub={worst_case[1]} edge=({worst_case[2]},"
          f"{worst_case[3]})")
    (OUT / "gap_arc_test.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "gap_arc_test.txt"))


if __name__ == "__main__":
    main()
