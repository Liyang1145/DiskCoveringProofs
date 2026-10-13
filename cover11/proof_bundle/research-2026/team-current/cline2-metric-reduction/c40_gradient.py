"""C40: gradient of the covering radius at the candidate in the unsaturated
coordinates.  Decides whether the candidate is (numerically) stationary.

Parameters (29): theta_0..theta_8 (switch angles), a_1..a_9, b_1..b_9 (switch
radii), hub_1, hub_2 (4 coordinates).  theta_0 is the rotation gauge and is not
varied (the covering radius is rotation invariant).

Covering radius estimate: dense polar grid + local refinement.  Cost ~ 1 s per
evaluation, so a full 29-parameter central difference (~58 evaluations) needs a
few minutes; we run it in the background and report both the gradient and the
best (most negative) directional derivative.
"""
import json, math, sys
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


def reconstruct(th, aa, bb):
    P = np.stack([np.cos(th), np.sin(th)], 1)
    Z = np.zeros((9, 2))
    for i in range(9):
        pL = P[(i - 1) % 9]
        pR = P[i]
        nv = pL + pR
        nn = np.hypot(*nv)
        if nn < 1e-12:
            return None
        n = nv / nn
        e = np.array([-n[1], n[0]])
        d = math.hypot(*(pR - pL))
        k = float(n @ ((pL + pR) / 2))
        x = (aa[i] ** 2 - bb[i] ** 2) / (2 * d)
        disc = k * k - 1 - x * x + bb[i] ** 2
        if disc < 0:
            return None
        Z[i] = (k - math.sqrt(disc)) * n + x * e
    return Z


_T = np.linspace(0, 2 * pi, 120000, endpoint=False)


def cover_radius(S, refine=True):
    best = 0.0
    bestx = None
    ct, st = np.cos(_T), np.sin(_T)
    for r in (0.0, 0.3, 0.55, 0.75, 0.9, 0.97, 1.0):
        X = np.stack([r * ct, r * st], 1)
        d = np.hypot(X[:, 0:1] - S[None, :, 0], X[:, 1:2] - S[None, :, 1]).min(1)
        k = int(np.argmax(d))
        if d[k] > best:
            best = float(d[k])
            bestx = X[k].copy()
    if refine and bestx is not None:
        from scipy.optimize import minimize
        rr = minimize(lambda q: -np.hypot(*(S - q[None, :]).T).min(), bestx,
                      method="Nelder-Mead",
                      options={"xatol": 1e-12, "fatol": 1e-14, "maxiter": 3000, "maxfev": 3000})
        if np.isfinite(rr.fun) and -rr.fun > best:
            best = float(-rr.fun)
    return best


def main():
    C = load()
    R = 0.37998385311983884
    sw = switches_cyclic(C, R)
    th0 = np.array([math.atan2(p[1], p[0]) for p in sw])
    aa0 = np.array([float(np.hypot(*(C[ORDER[i]] - sw[(i - 1) % 9]))) for i in range(9)])
    bb0 = np.array([float(np.hypot(*(C[ORDER[i]] - sw[i]))) for i in range(9)])
    hubs0 = C[[0, 2]].ravel()

    def radius_from_params(th, aa, bb, hb):
        Z = reconstruct(th, aa, bb)
        if Z is None:
            return None
        S = np.vstack([Z, hb.reshape(2, 2)])
        if np.any(np.hypot(hb.reshape(2, 2), axis=1) >= 1):
            return None
        return cover_radius(S)

    base = radius_from_params(th0, aa0, bb0, hubs0)
    print("base covering radius:", base, flush=True)

    # parameter vector: [dth(9), da(9), db(9), dh(4)] relative to the candidate
    steps = np.r_[np.full(9, 2e-4), np.full(9, 2e-4), np.full(9, 2e-4), np.full(4, 2e-4)]
    vec = np.zeros(29)
    vec[9:18] = aa0
    vec[18:27] = bb0
    vec[27:] = hubs0
    base_th = th0.copy()

    def evalp(delta, sgn):
        th = base_th + sgn * delta[0:9]
        aa = vec[9:18] + sgn * delta[9:18]
        bb = vec[18:27] + sgn * delta[18:27]
        hb = vec[27:] + sgn * delta[27:]
        if np.any(aa <= 0) or np.any(bb <= 0):
            return np.nan
        return radius_from_params(th, aa, bb, hb)

    grad = np.zeros(29)
    print("computing central differences (29 parameters)...", flush=True)
    for k in range(29):
        d = np.zeros(29)
        d[k] = steps[k]
        rp = evalp(d, +1)
        rm = evalp(d, -1)
        if rp is None or rm is None or not np.isfinite(rp) or not np.isfinite(rm):
            grad[k] = np.nan
        else:
            grad[k] = (rp - rm) / (2 * steps[k])
        print(f"  param {k:2d}: dR/dp = {grad[k]:+.6e}   (R+ = {rp}, R- = {rm})", flush=True)

    finite = np.isfinite(grad)
    print("\ngradient (finite entries):", np.round(grad[finite], 6).tolist())
    print("any negative entry (a decreasing direction):",
          bool(np.any(grad[finite] < -1e-9)), " min =", np.nanmin(grad))
    OUT.mkdir(exist_ok=True)
    (OUT / "c40_gradient.json").write_text(json.dumps({
        "base": base, "grad": grad.tolist(), "steps": steps.tolist()}, indent=2))
    print("wrote", OUT / "c40_gradient.json")


if __name__ == "__main__":
    main()
