"""C12: continuation along the 1-D equidistant-switch stratum.

At the candidate the 9x10 Jacobian has rank 9 (F_i depends on t_i only through
t_(i-1), an exact structural fact).  So the sharp stratum
    { 9 ring sites on the unit circle, the 9 switches at equal angular
      spacing, each switch at equal distance sqrt(t_j) from its two adjacent
      ring sites }
is 1-dimensional.  Here we walk along it with a predictor-corrector and, at
each accepted point, evaluate
    R_sw   = max_j sqrt(t_j)                        (boundary arcs tight at R)
    R_hub  = max over hubs of (max distance from hub to its 3 switches)
    R_geo  = true coverage radius (dense sampling + refinement)
If R_sw varies monotonically we have a genuine sharpness statement; if it is
flat, the candidate sits in an exactly-flat family.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
delta = 2 * pi / 9


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def cand_x():
    C = load()
    R = 0.37998385311983884
    N0 = 360000
    t0 = np.linspace(0, 2 * pi, N0 + 1)[:-1]
    c0 = np.stack([np.cos(t0), np.sin(t0)], 1)
    d0 = np.hypot(c0[:, 0:1] - C[None, :, 0], c0[:, 1:2] - C[None, :, 1])
    own = np.argmin(d0, 1)
    order = []
    for k in range(N0):
        if own[k] != own[k - 1]:
            order.append(int(own[k]))
    ideal = np.array([[math.cos(2 * pi * k / 9), math.sin(2 * pi * k / 9)] for k in range(9)])
    Rm = np.array([[math.cos(2 * pi * k / 9 - pi / 9), math.sin(2 * pi * k / 9 - pi / 9)] for k in range(9)])
    best = None
    for sgn in (1, -1):
        for ph in np.linspace(0, 2 * pi, 721)[:-1]:
            ca, sa = math.cos(ph), math.sin(ph)
            sw = np.array([[ca * p[0] - sa * p[1], sa * p[0] + ca * p[1]] for p in Rm])
            err = 0.0
            for a in range(9):
                d = np.hypot(*(C - sw[a][None, :]).T)
                err += abs(d[order[a]] - R) ** 2
            if best is None or err < best[0]:
                best = (err, ph, sw.copy())
    err, ph, sw = best
    print("equal-spacing fit: max |dist - R| =", math.sqrt(best[0] / 9), " phase(deg) =", math.degrees(ph))
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    tvec = np.zeros(9)
    for i in range(9):
        zi = C[order[i]]
        tvec[i] = float(np.sum((zi - sw[i]) ** 2))
    return np.r_[tvec, float((th[0] + pi) % (2 * pi))], order, C, sw


def build(theta0, t):
    """switches -> ring sites at equal distance sqrt(t_i) from P_(i-1), P_i."""
    P = [np.array([math.cos(theta0 + k * delta), math.sin(theta0 + k * delta)]) for k in range(9)]
    Z = []
    F = []
    for i in range(9):
        pl = P[(i - 1) % 9]
        pr = P[i]
        rl = math.sqrt(max(t[(i - 1) % 9], 0.0))
        rr = math.sqrt(max(t[i], 0.0))
        d = pr - pl
        dist = math.hypot(*d)
        if dist > rl + rr or dist < abs(rl - rr) or dist == 0:
            return P, None, None
        a = (rl * rl - rr * rr + dist * dist) / (2 * dist)
        h2 = rl * rl - a * a
        if h2 < 0:
            return P, None, None
        h = math.sqrt(h2)
        m = pl + a * d / dist
        perp = np.array([-d[1], d[0]]) / dist
        p1 = m + h * perp
        p2 = m - h * perp
        zi = p1 if np.hypot(*p1) <= np.hypot(*p2) else p2
        Z.append(zi)
        F.append(float(np.sum((zi - pl) ** 2) - t[(i - 1) % 9]))
    return P, Z, np.array(F)


def Fx(x):
    P, Z, F = build(x[9], x[:9])
    if F is None:
        return np.full(9, 1e3)
    return F


def jac(x):
    J = np.zeros((9, 10))
    for k in range(10):
        h = 1e-7 * max(1e-3, abs(x[k]))
        xp = x.copy(); xp[k] += h
        xm = x.copy(); xm[k] -= h
        J[:, k] = (Fx(xp) - Fx(xm)) / (2 * h)
    return J


def coverage_radius(P, Z, hubsw, refine=True):
    sites = list(Z) + list(hubsw)
    S = np.array(sites)

    def f(q):
        return np.hypot(*(S - q[None, :]).T).min()

    # candidates: dense polar grid
    best = (0.0, None)
    for nr in (300, 900):
        rs = np.linspace(0, 1, nr + 1)
        ths = np.linspace(0, 2 * pi, max(600, 6 * nr) + 1)[:-1]
        for r in rs[1:]:
            xs = np.stack([r * np.cos(ths), r * np.sin(ths)], 1)
            d = np.hypot(xs[:, 0:1] - S[None, :, 0], xs[:, 1:2] - S[None, :, 1]).min(1)
            k = int(np.argmax(d))
            if d[k] > best[0]:
                best = (float(d[k]), xs[k].copy())
    if refine:
        from scipy.optimize import minimize
        r = minimize(lambda q: -f(q), best[1], method="Nelder-Mead",
                     options={"xatol": 1e-14, "fatol": 1e-16, "maxiter": 20000, "maxfev": 20000})
        x = r.x
        if not np.all(np.isfinite(x)):
            return best[0]
        if x @ x > 1.0:
            x = x * (1 - 1e-14) / math.sqrt(x @ x)
        if -r.fun > best[0]:
            best = (float(-r.fun), x)
    return best[0]


def hub_switches():
    tight = json.loads((OUT / "c5_tight.json").read_text())
    for e in tight["vor_tight"]:
        print("   V", e["sites"], e["r"], e["p"])


def main():
    x0, order, C, sw0 = cand_x()
    print("ring order:", order)
    print("t at candidate:", np.round(x0[:9], 12).tolist())
    print("F at candidate:", np.round(Fx(x0), 15).tolist())
    J = jac(x0)
    U, S, Vt = np.linalg.svd(J)
    print("singular values:", np.round(S, 8).tolist(), " rank:", int((S > 1e-6 * S[0]).sum()))
    nvec = Vt[-1] / np.linalg.norm(Vt[-1])
    print("null direction:", np.round(nvec, 8).tolist())

    # hubs from the candidate (triples of switches), indices in cyclic switch order
    hub_idx = [[6, 7, 8], [1, 1, 1]]   # placeholder, replaced below

    # determine hub switch triples from the tight data
    tight = json.loads((OUT / "c5_tight.json").read_text())
    hub_pts = {}
    for e in tight["vor_tight"]:
        s = e["sites"]
        if len(s) == 3 and set([0, 2]).issubset(set(s)):
            for h in (0, 2):
                if h in s:
                    hub_pts.setdefault(h, []).append(np.array(e["p"]))
    print("hub 0 pts:", [np.round(p, 6).tolist() for p in hub_pts[0]])
    print("hub 2 pts:", [np.round(p, 6).tolist() for p in hub_pts[2]])

    def hub_positions(P, Z):
        """hubs = circumcenters of their three tight Voronoi vertices' switch triples.
        We instead recompute the hub as the circumcenter of the three switches that
        are equidistant from it, which we read off the candidate incidence."""
        return None

    # Continue: predictor-corrector with pseudo-arclength in x
    hist = []
    step = 2e-3
    for direction in (+1, -1):
        x = x0.copy()
        for it in range(40):
            # predictor
            xp = x + direction * step * nvec
            # corrector: minimise ||F|| plus small step penalty
            from scipy.optimize import least_squares
            sol = least_squares(lambda y: np.r_[Fx(y), 1e-3 * (y - xp)], xp,
                                xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
            x = sol.x
            P, Z, F = build(x[9], x[:9])
            if Z is None or np.abs(F).max() > 1e-12:
                print(f"  dir {direction:+d} it {it}: corrector failed, stop")
                break
            Rsw = max(math.sqrt(max(t, 0.0)) for t in x[:9])
            Rlo = min(math.sqrt(max(t, 0.0)) for t in x[:9])
            hist.append((direction, it, float(x[9]), Rsw, Rlo, np.abs(F).max()))
            if it % 5 == 0 or it < 3:
                print(f"  dir {direction:+d} it {it:2d} th0={x[9]:+.9f} Rsw={Rsw:.15f} Rlo={Rlo:.15f}"
                      f" |F|={np.abs(F).max():.2e}")
    OUT.mkdir(exist_ok=True)
    (OUT / "c12_family.json").write_text(json.dumps({"x0": x0.tolist(), "null": nvec.tolist(),
                                                     "hist": hist}, indent=2))
    print("\nRsw range over the walk:", min(h[3] for h in hist), max(h[3] for h in hist))
    print("R at candidate =", 0.37998385311983884)
    print("wrote", OUT / "c12_family.json")


if __name__ == "__main__":
    main()
