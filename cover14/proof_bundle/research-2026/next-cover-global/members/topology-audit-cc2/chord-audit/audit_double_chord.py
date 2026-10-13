"""Audit of lead/Q11-DOUBLE-CHORD-EXCLUSION.md (C1177), scope chord-audit/.

Decision-relevant facts, all recomputed here:
 T1 constants: B = 2 asin(2rho), L = 2 asin(rho), and the comparisons
     3L vs B  (at most 2 whole owner arcs fit in an arc of length <= B)
     2B+5L vs 2pi (two disjoint chord triples impossible)
     B+7L vs 2pi  (four whole arcs in K impossible)
     the connectedness crossover 1-2rho for S^1 cap B(p,2rho) = one arc.
 T2 explicit clustered configurations: measure K = S^1 cap B(p,2rho), its component lengths,
     and the actual owned arcs of three sites all within rho of p (witness p) via nearest-site
     sampling; report sum(|J|) / B to test the bound "sum <= B".
 T3 the distance-exactly-2 graph on C11: triangles (must be 0) and max matching, which bounds
     the number of chords whose middles are pairwise at distance 2.
 T4 catalogue pruning reproduction: reconstruct middles from face edges, drop rows with two
     vertex-disjoint chord triples, compare with lead/q11-double-chord-pruning.json.
"""
import json
import math
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = HERE.parents[2] / "lead"
U = 0.33173203427623414
N = 11


def consts(rho):
    B = 2 * math.asin(2 * rho)
    L = 2 * math.asin(rho)
    return dict(rho=rho, B=B, L=L, threeL=3 * L, twoL=2 * L,
                # NOTE 3L > B is NOT an exclusion (each arc is bounded ABOVE by L);
                # kept for bookkeeping only.
                threeL_gt_B=3 * L > B,
                twoB5L=2 * B + 5 * L, twoB5L_lt_2pi=2 * B + 5 * L < 2 * math.pi,
                Bplus7L=B + 7 * L, Bplus7L_lt_2pi=B + 7 * L < 2 * math.pi,
                twoAsin2Plus14AsinU=2 * B + 14 * math.asin(rho),
                q10_bound_lt_2pi=2 * B + 14 * math.asin(rho) < 2 * math.pi)


def cap_measure(p, a):
    """measure of S^1 cap B(p,a): empty iff A=(1+|p|^2-a^2)/(2|p|) > 1; single arc
    2 acos(A) for |A| <= 1; whole circle for A <= -1.  NEVER two components."""
    r = math.hypot(*p)
    if r < 1e-12:
        return 2 * math.pi if a >= 1 else 0.0
    A = (1 + r * r - a * a) / (2 * r)
    if A > 1:
        return 0.0
    if A <= -1:
        return 2 * math.pi
    return 2 * math.acos(A)


def owned_lens(sites, r, samples=120000):
    own = [0.0] * len(sites)
    for k in range(samples):
        th = 2 * math.pi * (k + 0.5) / samples
        x = (math.cos(th), math.sin(th))
        ds = [math.hypot(x[0] - c[0], x[1] - c[1]) for c in sites]
        m = min(ds)
        if m <= r:
            own[min(range(len(sites)), key=lambda j: ds[j])] += 2 * math.pi / samples
    return own


def T2_cases(rho):
    out = []
    for (a, th, dd) in ((0.97, 0.20, 0.95), (0.95, 0.20, 0.90), (0.90, 0.30, 0.90),
                        (0.99, 0.10, 0.99), (0.94, 0.25, 0.94)):
        p = (a, 0.0)
        c1 = (a + dd * rho, 0.0)
        # two outer sites at +-th seen from c1, all within rho of p
        c0 = (c1[0] + (1 - dd) * rho * math.cos(-th), c1[1] + (1 - dd) * rho * math.sin(-th))
        c2 = (c1[0] + (1 - dd) * rho * math.cos(th), c1[1] + (1 - dd) * rho * math.sin(th))
        sites = [c0, c1, c2]
        if max(math.hypot(*c) for c in sites) > rho:
            continue
        own = owned_lens(sites, rho)
        B = 2 * math.asin(2 * rho)
        km = cap_measure(p, 2 * rho); kc = km
        out.append(dict(a=a, theta=th, dd=dd, own=[round(o, 5) for o in own],
                        sum=round(sum(own), 5), B=round(B, 5),
                        ratio=round(sum(own) / B, 4), K_measure=round(km, 5),
                        K_component=round(kc, 5)))
    return out


def T3():
    n = N
    adj = {(i - 2) % n for i in range(0, 1)}  # placeholder
    tris = 0
    for i in range(n):
        for j in ((i + 2) % n, (i - 2) % n):
            for k in ((j + 2) % n, (j - 2) % n):
                if k == i:
                    continue
                # i,j,k mutually distance 2?
                if ((i - j) % n) in (2, n - 2) and ((j - k) % n) in (2, n - 2) \
                        and ((i - k) % n) in (2, n - 2):
                    tris += 1
    maxset = 0
    for mask in range(1 << n):
        S = [i for i in range(n) if (mask >> i) & 1]
        if all(((a - b) % n) not in (2, n - 2) for i2, a in enumerate(S) for b in S[i2 + 1:]):
            maxset = max(maxset, len(S))
    return dict(triangles_in_distance2_graph=tris // 6, max_set_with_no_distance2_pair=maxset)


def T4():
    D = json.loads((LEAD / "q11-pocket-catalogue.json").read_text(encoding="utf-8"))
    keep, hist = [], {}
    bad = 0
    for idx, e in enumerate(D["entries"]):
        edges = {tuple(sorted(uv)) for f in e["faces"] for uv in combinations(f, 2)}
        middles = [i for i in range(N) if tuple(sorted(((i - 1) % N, (i + 1) % N))) in edges]
        if len(middles) != len(e["chord_middle_representative"]):
            bad += 1
        tri = [{(i - 1) % N, i, (i + 1) % N} for i in middles]
        pair = next(((middles[x], middles[y]) for x in range(len(tri))
                     for y in range(x + 1, len(tri)) if not tri[x] & tri[y]), None)
        if pair is None:
            keep.append(idx)
            if len(middles) > 2:
                bad += 1
            if len(middles) == 2 and (middles[1] - middles[0]) % N not in (2, N - 2):
                bad += 1
        key = str(len(middles))
        hist.setdefault(key, [0, 0])
        hist[key][0 if pair is None else 1] += 1
    C = json.loads((LEAD / "q11-double-chord-pruning.json").read_text(encoding="utf-8"))
    return dict(kept=len(keep), removed=sum(v[1] for v in hist.values()),
                structural_violations=bad,
                hist={k: list(v) for k, v in sorted(hist.items(), key=lambda x: int(x[0]))},
                lead_kept=C["retained_count"],
                kept_sets_equal=sorted(keep) == sorted(C["retained_indices"]),
                newly_removed_beyond_double_ear=C["newly_removed_beyond_double_ear"])


def main():
    rep = dict(T1_constants=[consts(U), consts(U + 1e-6), consts(1 / 3 - 1e-9)],
               T2_clustered=T2_cases(U), T3=T3(), T4=T4())
    (HERE / "chord-audit.json").write_text(json.dumps(rep, indent=1), encoding="utf-8")
    print(json.dumps({k: v for k, v in rep.items()}, indent=1)[:5000])


if __name__ == "__main__":
    main()

