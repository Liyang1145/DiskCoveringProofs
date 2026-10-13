"""C29: the interior (hub) obligation in reduced coordinates.

On the sharp stratum (§3 of CLINE2-RING-REDUCTION.md) the ring sites are
determined by (gaps, R).  This script asks the reduced question:

  given the ring sites of the candidate, how far must the two hub sites be moved,
  and what is the best (smallest) covering radius achievable with the two hubs
  placed optimally inside?  Then: how does that optimum vary with the gaps?

Method: the hub sites only matter through (a) their own Voronoi cell inside the
disk and (b) the bisectors with the ring sites.  We optimise the two hub
positions by direct minimisation of the covering radius computed on a fine grid
of the disk (numeric diagnostic only - not a certificate).
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

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
    th = np.cumsum(np.r_[theta0, gaps[:-1]])
    P = np.stack([np.cos(th), np.sin(th)], 1)
    Z = np.zeros((9, 2))
    for i in range(9):
        pL, pR = P[(i - 1) % 9], P[i]
        n = pL + pR
        n = n / np.hypot(*n)
        root = R * R - math.sin(gaps[i] / 2) ** 2
        if root < 0:
            return None, None
        Z[i] = (math.cos(gaps[i] / 2) - math.sqrt(root)) * n
    return P, Z


def make_grid(nr=260, nang=2400):
    rs = np.linspace(0, 1, nr + 1)
    ths = np.linspace(0, 2 * pi, nang + 1)[:-1]
    pts = []
    for r in rs:
        pts.append(np.stack([r * np.cos(ths), r * np.sin(ths)], 1))
    return np.vstack(pts), rs, ths


def cover_radius_fast(S, grid):
    d = np.hypot(grid[:, 0:1] - S[None, :, 0], grid[:, 1:2] - S[None, :, 1]).min(1)
    return float(d.max())


def main():
    C = load()
    R = 0.37998385311983884
    sw = candidate_switches(C, R)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    gaps = np.array([((th[i] - th[(i - 1) % 9]) % (2 * pi)) for i in range(9)])
    P, Z = construct(gaps, R, theta0=th[0])
    print("reconstruction error vs candidate ring sites:",
          max(np.hypot(*(Z[i] - C[ORDER[i]])) for i in range(9)))

    ring = Z
    hubs0 = C[[0, 2]]
    grid, _, _ = make_grid(300, 3000)
    print("\ncandidate rings + candidate hubs: covering radius =",
          cover_radius_fast(np.vstack([ring, hubs0]), grid))

    # optimise the two hub positions with the ring fixed
    def f(h):
        S = np.vstack([ring, h.reshape(2, 2)])
        if np.any(np.hypot(h[0::2], h[1::2]) >= 1):
            return 1e3
        return cover_radius_fast(S, grid)

    best = None
    for seed in (hubs0.ravel(), [-0.02, 0.0, 0.02, 0.0], [0.0, -0.3, 0.0, 0.3],
                 [-0.15, 0.0, 0.15, 0.0]):
        r = minimize(f, np.asarray(seed, float), method="Nelder-Mead",
                     options={"xatol": 1e-10, "fatol": 1e-12, "maxiter": 4000})
        if best is None or r.fun < best.fun:
            best = r
    print("optimal hub placement  :", np.round(best.x, 9).tolist(),
          " covering radius =", best.fun)
    print("candidate hubs         :", np.round(hubs0.ravel(), 9).tolist())

    # how does the achievable radius move when the ring changes but the hubs stay put?
    print("\nring perturbations (gaps varied, hubs re-optimised each time):")
    rng = np.random.default_rng(23)
    res = []
    for trial in range(7):
        dg = rng.normal(0, 0.03, 9)
        dg -= dg.mean()
        g2 = gaps + dg
        if (g2 <= 0).any() or math.sin(g2.max() / 2) > R:
            continue
        P2, Z2 = construct(g2, R, theta0=th[0])
        if Z2 is None:
            continue
        def f2(h):
            S = np.vstack([Z2, h.reshape(2, 2)])
            if np.any(np.hypot(h[0::2], h[1::2]) >= 1):
                return 1e3
            return cover_radius_fast(S, grid)
        b2 = None
        for seed in (best.x, hubs0.ravel()):
            r = minimize(f2, np.asarray(seed, float), method="Nelder-Mead",
                         options={"xatol": 1e-10, "fatol": 1e-12, "maxiter": 3000})
            if b2 is None or r.fun < b2.fun:
                b2 = r
        res.append((trial, float(dg.max()), b2.fun))
        print(f"   trial {trial}: |dg|max={abs(dg).max():.4f}  best covering radius = {b2.fun:.9f}"
              f"   (candidate {best.fun:.9f}, change {b2.fun-best.fun:+.3e})")

    OUT.mkdir(exist_ok=True)
    (OUT / "c29_hubopt.json").write_text(json.dumps({
        "candidate_hubs": hubs0.tolist(), "opt_hubs": best.x.tolist(),
        "opt_radius": best.fun, "trials": [{"i": t[0], "dg": t[1], "rad": t[2]} for t in res],
    }, indent=2))
    print("\nwrote", OUT / "c29_hubopt.json")


if __name__ == "__main__":
    main()
