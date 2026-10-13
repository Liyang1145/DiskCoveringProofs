"""C39: unsaturated model — implementation and first-order test at the candidate.

Model (all-free, no saturation): unknowns
    switches  P_0..P_8 on the unit circle in cyclic order (8 after rotation),
    radii     a_i = |c_i - P_(i-1)| , b_i = |c_i - P_i|  (18),
    hubs      h_1, h_2 (4).
Reconstruction (C38):
    n = dir(P_(i-1)+P_i), e = rot(n,90), d = 2 sin(w_i/2), k = cos(w_i/2),
    x = (a_i^2-b_i^2)/(2d),  xi = k - sqrt(k^2-1-x^2+b_i^2),  c_i = xi n + x e.

Test here: at the candidate (saturated, a_i=b_i=R), move along random directions of the
unsaturated parameter space and measure the covering radius of the reconstructed
configuration (dense sampling + refinement).  If some direction decreases it, the
saturated configuration is not even a local optimum of the covering radius, which is
exactly the content of the lead's counterexample direction.
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


def switches_cyclic(C, R):
    out = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        hh = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - hh * hh))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                out.append(p)
                break
    return np.array(out)


def reconstruct(th, aa, bb, theta0_shift=0.0):
    """th = switch angles (9); aa, bb = radii in the ring order."""
    P = np.stack([np.cos(th + theta0_shift), np.sin(th + theta0_shift)], 1)
    Z = np.zeros((9, 2))
    for i in range(9):
        pL = P[(i - 1) % 9]
        pR = P[i]
        nv = pL + pR
        nn = np.hypot(*nv)
        if nn < 1e-12:
            return None, None
        n = nv / nn
        e = np.array([-n[1], n[0]])
        d = math.hypot(*(pR - pL))
        k = float(n @ ((pL + pR) / 2))
        x = (aa[i] ** 2 - bb[i] ** 2) / (2 * d)
        disc = k * k - 1 - x * x + bb[i] ** 2
        if disc < 0:
            return None, None
        xi = k - math.sqrt(disc)
        Z[i] = xi * n + x * e
    return P, Z


def cover_radius(S):
    from scipy.optimize import minimize as mn
    N = 220000
    t = np.linspace(0, 2 * pi, N + 1)[:-1]
    best = 0.0
    arg = None
    for r in (0.0, 0.2, 0.4, 0.6, 0.8, 0.92, 1.0):
        X = np.stack([r * np.cos(t), r * np.sin(t)], 1)
        d = np.hypot(X[:, 0:1] - S[None, :, 0], X[:, 1:2] - S[None, :, 1]).min(1)
        k = int(np.argmax(d))
        if d[k] > best:
            best, arg = float(d[k]), X[k].copy()
    if arg is None:
        return best
    r = mn(lambda q: -np.hypot(*(S - q[None, :]).T).min(), arg, method="Nelder-Mead",
           options={"xatol": 1e-13, "fatol": 1e-15, "maxiter": 8000, "maxfev": 8000})
    return max(best, -r.fun)


def main():
    C = load()
    R = 0.37998385311983884
    sw = switches_cyclic(C, R)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    aa = np.array([float(np.hypot(*(C[ORDER[i]] - sw[(i - 1) % 9]))) for i in range(9)])
    bb = np.array([float(np.hypot(*(C[ORDER[i]] - sw[i]))) for i in range(9)])
    hubs = C[[0, 2]]

    P, Z = reconstruct(th, aa, bb)
    err = max(np.hypot(*(Z[i] - C[ORDER[i]])) for i in range(9))
    print("candidate reconstruction error:", err)
    S0 = np.vstack([Z, hubs])
    r0 = cover_radius(S0)
    print("candidate covering radius (dense + refine):", r0, " (exact value 0.37998385311983884)")

    print("\nrandom unsaturated perturbations (switch angles + radii + hubs), covering radius:")
    rng = np.random.default_rng(2024)
    best_down = 0.0
    rows = []
    for trial in range(12):
        dth = rng.normal(0, 2e-3, 9)
        da = rng.normal(0, 4e-3, 9)
        db = rng.normal(0, 4e-3, 9)
        dh = rng.normal(0, 4e-3, 4)
        a2 = aa + da
        b2 = bb + db
        P2, Z2 = reconstruct(th + dth, a2, b2)
        if Z2 is None:
            print(f"  trial {trial}: infeasible (disc<0)")
            continue
        S = np.vstack([Z2, hubs + dh.reshape(2, 2)])
        rr = cover_radius(S)
        rows.append(rr)
        best_down = min(best_down, rr - r0)
        print(f"  trial {trial}: |dth|={np.abs(dth).max():.1e} |da|={np.abs(da).max():.1e}"
              f" |db|={np.abs(db).max():.1e} |dh|={np.abs(dh).max():.1e}"
              f"  covering = {rr:.12f}  change = {rr - r0:+.3e}")
    print("\nmost negative change found:", best_down)

    OUT.mkdir(exist_ok=True)
    (OUT / "c39_unsaturated_test.json").write_text(json.dumps({
        "r0": r0, "rows": rows, "best_down": best_down}, indent=2))
    print("wrote", OUT / "c39_unsaturated_test.json")


if __name__ == "__main__":
    main()
