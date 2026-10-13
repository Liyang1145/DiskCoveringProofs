"""C28: the reduction, verified numerically end to end.

FINDING.  The nine "sharpness" equations F_i(gaps, R) = 0 are NOT constraints:
for every gap sequence and every R with R >= max_i sin(g_i/2), the construction
    switch_i = unit vector at theta_i = sum_{k<=i} g_k
    site_i   = s_i * dir(switch_(i-1) + switch_i),   s_i = cos(g_i/2) - sqrt(R^2 - sin^2(g_i/2))
satisfies |site_i - switch_(i-1)| = |site_i - switch_i| = R identically.
Hence the sharp 9-ring stratum is exactly

    { (g_1..g_9, R) : g_i > 0, sum g_i = 2 pi, max_i sin(g_i/2) <= R < 1 }

an 8-parameter family, and on it the nine boundary tight radii all equal R
automatically.  Consequently the tightness conditions do NOT constrain R at all:
the sharp value of R must come from the COVERING condition (interior of the disk),
i.e. from the two hubs.

This script verifies
  (V1) the identity |site_i - switch| = R over random families (residual size);
  (V2) the covering radius of the ring-only part and of the ring+hub
       configuration along the family (hub placed optimally inside), showing that
       the covering radius is a NONTRIVIAL function of the gaps;
  (V3) the candidate's own gap vector lies in the family and its covering radius
       is 0.3799838531198387 (independent recomputation).
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def candidate_switches(C, R):
    sw = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        h = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                sw.append(p)
                break
    return np.array(sw)


def construct(gaps, R, theta0=0.0):
    """switches + ring sites; returns None if the branch is invalid."""
    th = np.cumsum(np.r_[theta0, gaps[:-1]])
    P = np.stack([np.cos(th), np.sin(th)], 1)
    Z = np.zeros((9, 2))
    for i in range(9):
        pL, pR = P[(i - 1) % 9], P[i]
        n = pL + pR
        nn = np.hypot(*n)
        if nn < 1e-12:
            return None, None
        n = n / nn
        root = R * R - math.sin(gaps[i] / 2) ** 2
        if root < 0:
            return None, None
        Z[i] = (math.cos(gaps[i] / 2) - math.sqrt(root)) * n
    return P, Z


def cover_radius(S, refine_from=None):
    """max-min distance of the site set S over the unit disk (numeric)."""
    N = 600000
    t = np.linspace(0, 2 * pi, N + 1)[:-1]
    best = (0.0, None)
    for r in (0.0, 0.25, 0.5, 0.7, 0.85, 0.95, 1.0):
        xs = np.stack([r * np.cos(t), r * np.sin(t)], 1)
        d = np.hypot(xs[:, 0:1] - S[None, :, 0], xs[:, 1:2] - S[None, :, 1]).min(1)
        k = int(np.argmax(d))
        if d[k] > best[0]:
            best = (float(d[k]), xs[k].copy())
    from scipy.optimize import minimize
    r = minimize(lambda q: -min(np.hypot(*(S - q[None, :]).T)), best[1], method="Nelder-Mead",
                 options={"xatol": 1e-13, "fatol": 1e-15, "maxiter": 8000, "maxfev": 8000})
    if -r.fun > best[0]:
        best = (float(-r.fun), r.x)
    return best


def main():
    C = load()
    R = 0.37998385311983884
    sw = candidate_switches(C, R)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    gaps = np.array([((th[i] - th[(i - 1) % 9]) % (2 * pi)) for i in range(9)])

    # ---- V1
    print("V1: identity |site_i - switch_(i-1)| = |site_i - switch_i| = R")
    rng = np.random.default_rng(17)
    worst = 0.0
    for _ in range(400):
        g = rng.uniform(0.15, 1.3, 9)
        g = g * (2 * pi / g.sum())
        if math.sin(g.max() / 2) > R:
            continue
        P, Z = construct(g, R, theta0=0.0)
        if Z is None:
            continue
        for i in range(9):
            d1 = np.hypot(*(Z[i] - P[(i - 1) % 9]))
            d2 = np.hypot(*(Z[i] - P[i]))
            worst = max(worst, abs(d1 - R), abs(d2 - R))
    print("   max residual over 400 random gap vectors (valid ones):", worst)
    P, Z = construct(gaps, R, theta0=th[0])
    print("   candidate gap vector: max residual =",
          max(max(abs(np.hypot(*(Z[i] - P[(i - 1) % 9])) - R),
                  abs(np.hypot(*(Z[i] - P[i])) - R)) for i in range(9)))

    # ---- V2: covering radius along the family, with the candidate's hub strategy
    print("\nV2: covering radius of the ring+2-hub construction along the family")
    C2 = C.copy()
    hubs = C2[[0, 2]]
    print("   candidate: gaps =", np.round(np.degrees(gaps), 4).tolist())
    r0, arg0 = cover_radius(C2)
    print(f"   candidate covering radius = {r0:.15f}  (at {np.round(arg0,6)})")

    rows = []
    for scale in (0.94, 0.97, 1.0, 1.03, 1.06):
        # perturb the gaps proportionally-ish while keeping the sum
        pert = gaps * scale
        pert = pert * (2 * pi / pert.sum())
        P2, Z2 = construct(pert, R, theta0=th[0])
        if Z2 is None:
            print(f"   scale {scale}: branch invalid")
            continue
        S = np.vstack([Z2, hubs])
        rr, arg = cover_radius(S)
        rows.append({"scale": scale, "covering": rr, "maxgap": float(pert.max())})
        print(f"   scale {scale:.2f}: ring radii {np.round(np.hypot(*Z2.T),6).tolist()}")
        print(f"             covering radius = {rr:.9f}   (candidate {r0:.9f}, diff {rr-r0:+.3e})")

    # ---- V3: does the covering radius depend on the gaps at all?
    print("\nV3: sensitivity of the covering radius to a single gap")
    for base in (0, 3):
        for dg in (-0.05, -0.02, 0.02, 0.05):
            g = gaps.copy()
            g[base] += dg
            g[3 if base == 0 else 0] -= dg
            if (g <= 0).any():
                continue
            P2, Z2 = construct(g, R, theta0=th[0])
            if Z2 is None:
                print(f"   gap {base} dg={dg:+.2f}: invalid branch")
                continue
            S = np.vstack([Z2, hubs])
            rr, _ = cover_radius(S)
            print(f"   gap {base} dg={dg:+.2f}: covering radius = {rr:.9f}  (change {rr-r0:+.3e})")

    OUT.mkdir(exist_ok=True)
    (OUT / "c28_family.json").write_text(json.dumps({
        "gaps": gaps.tolist(), "R": R, "candidate_covering": r0, "rows": rows}, indent=2))
    print("\nwrote", OUT / "c28_family.json")


if __name__ == "__main__":
    main()
