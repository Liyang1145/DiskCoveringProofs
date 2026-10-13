"""r20-chain: does the exact rim-arc criterion have TEETH as an exclusion criterion?

Necessary condition tested (exact object):
  with U_i := uncovered rim arcs of Lambda_i (in D, not covered by any ring disk), a legal cover
  must have hubs A,B with  U_i^{served by H} subset B(H,R)  for a partition into contiguous runs.
  Define, for a fixed ring configuration,
     SLACK(cfg) := max over ordered splits (S_A, S_B) of the cyclic order [contiguous, disjoint,
                   covering all essential indices] of  min_i ( R - max_{x in U_i} |H_{i}-x| ).
  A configuration with SLACK(cfg) < 0 cannot be covered => exclusion.  We maximise SLACK over
  configurations (numerically) and report whether the maximum ever becomes negative as R grows.
  Also reports the number of essential sites and the sizes of the contiguous runs (law of the
  chain sizes: the two runs must have sizes k and 9-k).
"""
import numpy as np
from scipy.optimize import minimize
from r20geom import load_certified, polar_order, OUT
from arcs import truly_uncovered_arcs

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def u_of(ring, i, R):
    return truly_uncovered_arcs(ring, i, R)


def maxdist_arc(H, ci, R, arc):
    c, hw = arc
    best = -np.inf
    for t in (c - hw, c + hw):
        x = ci + R * np.array([np.cos(t), np.sin(t)])
        best = max(best, float(np.linalg.norm(x - H)))
    psi = float(np.arctan2(*(np.asarray(H) - ci)[::-1]))
    for k in (-1, 0, 1):
        t = psi + 2 * PI * k
        if c - hw - 1e-12 <= t <= c + hw + 1e-12:
            x = ci + R * np.array([np.cos(t), np.sin(t)])
            best = max(best, float(np.linalg.norm(x - H)))
    return best


def slack_config(ring, R, hA, hB):
    """SLACK = max over contiguous splits (S_A, S_B) of the cyclic order of
               min(  min_{i in S_A} (R - reach_A(U_i)),  min_{i in S_B} (R - reach_B(U_i)) ).
    A legal cover with hubs at hA,hB needs SLACK >= 0."""
    n = len(ring)
    arcs = [u_of(ring, i, R) for i in range(n)]
    essential = [i for i in range(n) if sum(2 * a[1] for a in arcs[i]) > 1e-12]
    if not essential:
        return np.inf, None
    cost = {}
    for i in essential:
        ra = max(maxdist_arc(hA, ring[i], R, a) for a in arcs[i])
        rb = max(maxdist_arc(hB, ring[i], R, a) for a in arcs[i])
        cost[i] = (R - ra, R - rb)
    m = len(essential)
    best, bestsplit = -np.inf, None
    for start in range(m):
        for length in range(1, m):
            S = [essential[(start + t) % m] for t in range(length)]
            T = [essential[(start + length + t) % m] for t in range(m - length)]
            for SA, SB in ((S, T), (T, S)):
                vA = min(cost[i][0] for i in SA)
                vB = min(cost[i][1] for i in SB)
                v = min(vA, vB)
                if v > best:
                    best, bestsplit = v, (SA, SB)
    return best, bestsplit


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")
    P("ring order: " + ", ".join(map(str, ring_ids)))
    s, sp = slack_config(ring, R, HA, HB)
    P(f"SLACK at the certified candidate = {s:+.9f}   split={sp}")
    P("(must be >= 0; the candidate is a genuine legal configuration)")

    P("\n=== SLACK for the candidate rings as R varies (curve of the criterion) ===")
    P("     R        SLACK      min over sites")
    for RR in (R - 0.01, R - 0.005, R - 0.002, R - 0.001, R, R + 0.001, R + 0.005, R + 0.01,
               R + 0.02):
        v, spl = slack_config(ring, RR, HA, HB)
        P(f"  {RR:.9f}  {v:+.9f}   {spl if False else ''}")

    P("\n=== random legal configurations: max-min reach per hub (does it ever fail?) ===")
    rng = np.random.default_rng(3)
    for RR in (0.34, 0.36, 0.38, 0.3901, 0.40, 0.42, 0.45):
        worst = 1e9
        worst_cfg = None
        for trial in range(400):
            hA = rng.uniform(-1, 1, 2) * (1 - RR)
            hB = rng.uniform(-1, 1, 2) * (1 - RR)
            th = np.sort(rng.uniform(0, 2 * PI, 9))
            rho = np.sqrt(rng.uniform((1 - RR) ** 2, 1.0, 9))
            rr = np.stack([rho * np.cos(th), rho * np.sin(th)], 1)
            v, spl = slack_config(rr, RR, hA, hB)
            if v < worst:
                worst, worst_cfg = v, (hA.copy(), hB.copy(), rr.copy(), spl)
        P(f"  R={RR:.4f}: min over 400 random configs of SLACK = {worst:+.6f}"
          f"   {'(negative => some config excluded)' if worst < 0 else ''}")

    (OUT / "slack_criterion.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "slack_criterion.txt"))


if __name__ == "__main__":
    main()
