"""n12 -- necessary-condition lower bounds for k=10/11 (no 2D dense grids).

Setup (all statements are NECESSARY conditions for a radius-r cover of D by
12 disks; minimising r over them therefore gives a LOWER bound for the true
k=11 / k=10 radius).

Notation.  r = disk radius, D = unit disk.
m = 12-k hubs (= disks with |c_j| < 1-r ; by the inner-root reduction every
boundary-active centre has norm in [1-r, sqrt(1-r^2)], and every inactive
centre has norm < 1-r).
Core fact: every hub has norm < 1-r, so |h_j| + r < 1: hubs never meet S^1.
Every point of B(0, 1-2r) is farther than r from every boundary-active
centre, so the hubs must cover B(0, 1-2r).

Per-ray conditions (exact, no Voronoi assumption):
  * ray direction phi; hub disc of centre h reaches, along that ray, the
    radial interval [0, Rh(phi)] with
        Rh(phi) = |h| cos(phi-arg h) + sqrt(r^2 - |h|^2 sin^2(phi-arg h)),
    which is > 0 for every phi because |h| < r.
  * ring disc i (centre c_i = t_i u_i) covers, along direction phi with
    psi = phi - arg c_i, the interval
        [D_i(phi), U_i(phi)],  D_i(phi)= t_i cos psi - sqrt(r^2-t_i^2 sin^2 psi)
    (needs t_i |sin psi| <= r; note t_i cos psi > sqrt(...) > 0 always).
  * the ring must cover everything outside the hub union, in particular for
    every phi:  min_i D_i(phi) <= R_H(phi) := max_j R_{h_j}(phi)   (REACH)
    and                                  min_i |e^{i phi} - c_i| <= r  (S^1)
    and                                  min_i |h_j + r e^{i beta} - c_i| <= r
                                                              (hub boundary)

The REACH condition is the interior condition that pure capacity/sum bounds
(arc measures on two concentric circles) do not see.
"""
import json
import sys
import numpy as np
from scipy.optimize import minimize


def hub_reach(h, r, phis):
    """outer radial end of hub disc B(h,r) along directions phis (vector)."""
    e = np.linalg.norm(h)
    if e < 1e-14:
        return np.full_like(phis, r)
    ah = np.arctan2(h[1], h[0])
    s = np.sin(phis - ah)
    return e * np.cos(phis - ah) + np.sqrt(np.maximum(0.0, r * r - e * e * s * s))


def ring_inner(th, t, r, phis):
    """innermost ring point along phis, for centre polar (t,th); +inf if the
    disc misses that ray.

    The disc meets the ray at direction phi only if the minimal angular
    distance d = dist(phi,th) satisfies  d <= asin(r/t)  (< pi/2 because
    t >= 1-r > r).  For d > pi/2 the disc lies strictly behind the ray and the
    two roots t cos d +- sqrt(r^2-t^2 sin^2 d) are both negative.
    """
    d = np.abs((phis - th + np.pi) % (2.0 * np.pi) - np.pi)
    s2 = np.sin(d) ** 2
    ok = (t * t * s2 <= r * r) & (d <= np.pi / 2.0)
    h = np.sqrt(np.maximum(0.0, r * r - t * t * s2))
    val = t * np.cos(d) - h
    return np.where(ok, val, np.inf)


def softmin(a, axis=0, k=60.0):
    m = np.min(a, axis=axis, keepdims=True)
    w = np.exp(-k * (a - m))
    return (m - np.log(w.sum(axis=axis, keepdims=True)) / k).squeeze(axis)


def softmax(a, k=60.0):
    m = np.max(a)
    return m + np.log(np.exp(k * (a - m)).mean()) / k


def viol_k11(r, theta, t, e, N=1440, ksoft=80.0, cap=1e3):
    """max violation (>0 means some necessary condition fails) for k=11."""
    phis = np.linspace(0.0, 2.0 * np.pi, N, endpoint=False)
    h = np.array([-e, 0.0])
    C = np.stack([t * np.cos(theta), t * np.sin(theta)], axis=-1)
    # (1) S^1 covered by ring arcs
    d1 = np.linalg.norm(np.stack([np.cos(phis), np.sin(phis)], -1)[:, None, :]
                        - C[None, :, :], axis=2)
    v1 = float(np.max(d1.min(axis=1)) - r)
    # (2) reach: min_i D_i(phi) <= R_h(phi)
    R = hub_reach(h, r, phis)
    D = np.stack([ring_inner(theta[i], t[i], r, phis) for i in range(11)], axis=1)
    D = np.minimum(D, cap)
    v2 = float(np.max(D.min(axis=1) - R))
    # (3) hub boundary circle S(h,r) covered
    bet = np.linspace(0.0, 2.0 * np.pi, N, endpoint=False)
    pts = h[None, :] + r * np.stack([np.cos(bet), np.sin(bet)], -1)
    d3 = np.linalg.norm(pts[:, None, :] - C[None, :, :], axis=2)
    v3 = float(np.max(d3.min(axis=1)) - r)
    # (4) hub must contain the core B(0,1-2r): |h| + (1-2r) <= r
    v4 = float(e - (3.0 * r - 1.0))
    return max(v1, v2, v3, v4), (v1, v2, v3, v4)


def _softmin(a, ksoft, cap):
    a = np.minimum(a, cap)
    m = np.min(a, axis=1, keepdims=True)
    w = np.exp(-ksoft * (a - m))
    return (m - np.log(w.sum(axis=1, keepdims=True)) / ksoft).ravel()


def _softmax(a, ksoft):
    m = float(np.max(a))
    return m + float(np.log(np.exp(ksoft * (a - m)).mean()) / ksoft)


def viol_soft_k11(r, theta, t, e, N=720, ksoft=60.0, cap=1e3):
    phis = np.linspace(0.0, 2.0 * np.pi, N, endpoint=False)
    h = np.array([-e, 0.0])
    C = np.stack([t * np.cos(theta), t * np.sin(theta)], axis=-1)
    d1 = np.linalg.norm(np.stack([np.cos(phis), np.sin(phis)], -1)[:, None, :]
                        - C[None, :, :], axis=2)
    v1 = _softmax(d1.min(axis=1), ksoft) - r
    R = hub_reach(h, r, phis)
    D = np.stack([ring_inner(theta[i], t[i], r, phis) for i in range(11)], axis=1)
    v2 = _softmax(np.minimum(D.min(axis=1), cap) - R, ksoft)
    bet = np.linspace(0.0, 2.0 * np.pi, N, endpoint=False)
    pts = h[None, :] + r * np.stack([np.cos(bet), np.sin(bet)], -1)
    d3 = np.linalg.norm(pts[:, None, :] - C[None, :, :], axis=2)
    v3 = _softmax(d3.min(axis=1), ksoft) - r
    v4 = e - (3.0 * r - 1.0)
    return max(v1, max(v2, 0.0), v3, v4)


def pack_k11(r, x):
    """x = [e_raw, theta(11), t_raw(11)]; t kept in (1-r, sqrt(1-r^2))."""
    lo, hi = 1.0 - r, np.sqrt(max(0.0, 1.0 - r * r))
    e = 3.0 * r - 1.0
    ex = float(np.clip(x[0], -40.0, 40.0))
    ev = (e / (1.0 + np.exp(-ex))) if e > 0.0 else 0.0
    theta = np.asarray(x[1:12], float)
    z = np.clip(np.asarray(x[12:23], float), -40.0, 40.0)
    t = lo + (hi - lo) / (1.0 + np.exp(-z))
    return theta, t, ev


def best_k11(r, starts=24, N=720, seed=0):
    rng = np.random.default_rng(seed)
    best = None
    init = np.zeros(23)
    init[1:12] = 2 * np.pi * np.arange(11) / 11
    init[12:23] = 0.0          # midpoint of the t range
    cands = [init]
    for _ in range(starts):
        p = init + rng.normal(0, 0.6, 23)
        cands.append(p)
    for p0 in cands:
        f = lambda x: viol_soft_k11(r, *pack_k11(r, x), N=N)
        res = minimize(f, p0, method="Powell",
                       options=dict(maxiter=20000, xtol=1e-10, ftol=1e-12))
        v, _ = viol_k11(r, *pack_k11(r, res.x), N=2880)
        if best is None or v < best[0]:
            best = (v, res.x.copy())
    return best


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "scan"
    out = {}
    if mode == "scan":
        rows = []
        for r in np.arange(0.360, 0.396, 0.002):
            v, x = best_k11(r, starts=14)
            th, t, e = pack_k11(r, x)
            rows.append(dict(r=round(float(r), 4), viol=round(v, 6),
                             e=round(float(e), 5),
                             t_min=round(float(t.min()), 5),
                             t_max=round(float(t.max()), 5)))
            print(rows[-1], flush=True)
        out["k11_scan"] = rows
    json.dump(out, open(f"reachscan_{mode}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
