"""Deep independent verification of one violating configuration.

Three independent representations of the same geometry:
 (R1) analytic pair-enumeration anchors (geom_exact)
 (R2) fine sampling of S1 + bisection refinement of label changes (no bisector algebra)
 (R3) Voronoi cells as intersections of closed half-planes + disk, built by explicit clipping
and a direct raw-vector angular measurement (global atan2, no local frame), plus the
campaign's own atan2 endpoint-angle formula for delta.
"""
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records, anchors_exact, covering_radius

def label(sites, x):
    return int(np.argmin(np.linalg.norm(sites - x, axis=1)))

def anchors_sampling(sites, M=4_000_000):
    """R2: sample S1 densely, then bisect every label change."""
    sites = np.asarray(sites, float)
    t = 2 * np.pi * np.arange(M) / M
    X = np.stack([np.cos(t), np.sin(t)], 1)
    D2 = ((X[:, None, :] - sites[None, :, :]) ** 2).sum(-1)
    own = D2.argmin(1)
    sw = np.nonzero(own != np.roll(own, 1))[0]
    res = []
    for k in sw:
        i, j = int(own[k - 1]), int(own[k])
        lo, hi = t[k - 1], t[k]
        def g(th, i=i, j=j):
            x = np.array([math.cos(th), math.sin(th)])
            return float(((x - sites[i]) ** 2).sum() - ((x - sites[j]) ** 2).sum())
        a, b = lo, hi if hi > lo else hi + 2 * math.pi
        ga, gb = g(a), g(b)
        if ga * gb > 0:
            continue
        for _ in range(200):
            m = 0.5 * (a + b)
            gm = g(m)
            if ga * gm <= 0:
                b, gb = m, gm
            else:
                a, ga = m, gm
        th = 0.5 * (a + b) % (2 * math.pi)
        A = np.array([math.cos(th), math.sin(th)])
        res.append((th, label(sites, A), sorted((i, j))))
    res = [(t, l, p) for (t, l, p) in res]
    return res

def cell_polygon(sites, i, nsamp=400):
    """R3: Voronoi cell of site i intersected with the disk, as a polygon (fine angular
    discretisation of the constraint |x-c_i| <= |x-c_j|).  Returns vertex list."""
    th = np.linspace(0, 2 * np.pi, nsamp, endpoint=False)
    R = np.linspace(0, 1, 1200)
    T, RR = np.meshgrid(th, R)
    P = np.stack([RR * np.cos(T), RR * np.sin(T)], 2)
    d = np.linalg.norm(P - sites[i], axis=2)
    ok = np.ones_like(d, bool)
    for j in range(len(sites)):
        if j == i:
            continue
        ok &= d <= np.linalg.norm(P - sites[j], axis=2) + 1e-15
    # boundary radius per angle
    rad = np.zeros(nsamp)
    for a in range(nsamp):
        col = ok[:, a]
        idx = np.nonzero(col)[0]
        rad[a] = R[idx[-1]] if len(idx) else 0.0
    return th, rad

def raw(dirv):
    return math.atan2(dirv[1], dirv[0])

if __name__ == "__main__":
    cfgs = json.loads((HERE / "violating-configs.json").read_text())
    cfg = cfgs[0]
    S = np.array(cfg["sites"])
    print("config:", {k: v for k, v in cfg.items() if k != "sites"})
    print("n =", len(S), " max|site| =", round(float(np.max(np.linalg.norm(S, axis=1))), 9))
    r = covering_radius(S, 500)
    print("grid covering radius (500) =", round(r, 8), " U = 0.33173203427623414")
    # local refinement of the covering radius
    from scipy.optimize import minimize
    def negcov(x):
        return float(np.min(np.linalg.norm(S - x, axis=1)))
    best = 0.0; arg = None
    for a in np.linspace(0, 2 * math.pi, 24, endpoint=False):
        for rr in (0.0, 0.3, 0.6, 0.9):
            x0 = np.array([rr * math.cos(a), rr * math.sin(a)])
            res = minimize(lambda x: -negcov(x), x0, method="Nelder-Mead",
                           options=dict(xatol=1e-12, fatol=1e-14, maxiter=4000))
            if -res.fun > best:
                best = -res.fun; arg = res.x
    print("refined covering radius (local search) =", round(best, 8), "at", np.round(arg, 6))

    recs, anch = anchor_records(S)
    print("\n(R1) analytic anchors:", len(anch))
    for r_ in recs:
        print(f"   k={r_['k']:2d} t={r_['t']:.9f} pair={r_['pair']} pair2={r_['arc_cw']}/{r_['arc_ccw']} "
              f"nmargin={r_['nmargin']:.3e} gam={r_['gam']:.9f} nest_ccw={r_['nest_ccw']:+.4e} "
              f"nest_cw={r_['nest_cw']:+.4e} resid={r_['resid']:+.4e}")
    # R2 cross-check
    A2 = anchors_sampling(S, M=3_000_000)
    print("\n(R2) sampled anchors:", len(A2))
    for (t, l, p) in A2:
        print(f"   t={t:.9f} owner={l} pair={p}")
    # focus on the worst anchor
    worst = min(recs, key=lambda r_: min(r_["nest_ccw"], r_["nest_cw"]))
    kk = worst["k"]
    print(f"\n=== deep dive at the worst anchor k={kk} (t={worst['t']:.9f}) ===")
    A = worst["A"]
    u, v = worst["pair"]
    v_cw, v_ccw = worst["arc_cw"][0], worst["arc_ccw"][0]
    Aprev = anch[(kk - 1) % len(anch)]["A"]
    Anext = anch[(kk + 1) % len(anch)]["A"]
    m = (S[u] + S[v]) / 2
    print("A      =", np.round(A, 9), " pair owners (v_cw, v_ccw) =", (v_cw, v_ccw),
          " arc pair =", (u, v))
    print("A_prev =", np.round(Aprev, 9), " A_next =", np.round(Anext, 9))
    print("sites: v_cw =", np.round(S[v_cw], 9), " v_ccw =", np.round(S[v_ccw], 9))
    print("m (midpoint of owners) =", np.round(m, 9), " |m| =", round(float(np.linalg.norm(m)), 9))
    dirs = {
        "A->A_next": Anext - A, "A->v_ccw": S[v_ccw] - A, "A->m": m - A,
        "A->v_cw": S[v_cw] - A, "A->A_prev": Aprev - A, "inward radial (-A)": -A,
    }
    for nm, dv in dirs.items():
        print(f"   raw polar angle of {nm:22s} = {math.degrees(raw(dv)):10.5f} deg"
              f"   |.|={np.linalg.norm(dv):.6f}")
    dnext = raw(dirs["A->A_next"])
    order = sorted(dirs.items(), key=lambda kv: (raw(kv[1]) - dnext) % (2 * math.pi))
    print("   CCW order starting from A->A_next:")
    prev = 0.0
    for nm, dv in order:
        rel = (raw(dv) - dnext) % (2 * math.pi)
        print(f"      {nm:22s} rel={math.degrees(rel):10.5f} deg  gap={math.degrees(rel - prev):10.5f}")
        prev = rel
    # polygon interior angle (direct)
    u1, u2 = Aprev - A, Anext - A
    gccw = (raw(u2) - raw(u1)) % (2 * math.pi)
    rif = raw(-A)
    inside = ((rif - raw(u1)) % (2 * math.pi)) < gccw
    poly = gccw if inside else 2 * math.pi - gccw
    print(f"\n   polygon interior angle at A (direct measurement) = {math.degrees(poly):.9f} deg"
          f" = {poly:.12f} rad")
    print(f"   pi - (theta_cw+theta_ccw)/2                        = "
          f"{math.degrees(math.pi - (worst['theta_cw'] + worst['theta_ccw']) / 2):.9f} deg")
    # campaign's own endpoint-angle formula, from raw distances/angle at the site
    def endpoint_angle(site, X, Y):
        x1, x2 = X - site, Y - site
        r1, r2 = np.linalg.norm(x1), np.linalg.norm(x2)
        a = math.acos(max(-1, min(1, float(x1 @ x2) / (r1 * r2))))
        # delta at X in triangle (site, X, Y):
        return math.atan2(r2 * math.sin(a), r1 - r2 * math.cos(a)), a
    d_cw, alpha_cw = endpoint_angle(S[v_cw], A, Aprev)
    d_ccw, alpha_ccw = endpoint_angle(S[v_ccw], A, Anext)
    gam_cw = math.acos(max(-1, min(1, float((S[v_cw] - A) @ (m - A)) /
                                (np.linalg.norm(S[v_cw] - A) * np.linalg.norm(m - A)))))
    gam_ccw = math.acos(max(-1, min(1, float((S[v_ccw] - A) @ (m - A)) /
                                 (np.linalg.norm(S[v_ccw] - A) * np.linalg.norm(m - A)))))
    print(f"   campaign formula: delta_cw  = {d_cw:.12f} rad ({math.degrees(d_cw):.6f} deg)"
          f"  (angle at A of triangle (v_cw,A,A_prev)); alpha_v_cw={alpha_cw:.9f}")
    print(f"   campaign formula: delta_ccw = {d_ccw:.12f} rad ({math.degrees(d_ccw):.6f} deg)"
          f"  (angle at A of triangle (v_ccw,A,A_next)); alpha_v_ccw={alpha_ccw:.9f}")
    print(f"   angle check: gamma(v_cw)={gam_cw:.12f}  gamma(v_ccw)={gam_ccw:.12f}")
    lhs = d_cw + gam_cw + gam_ccw + d_ccw
    print(f"\n   LHS of claimed identity  delta_cw + 2*gamma + delta_ccw = {lhs:.12f} rad"
          f" ({math.degrees(lhs):.6f} deg)")
    print(f"   RHS  pi - (theta_cw+theta_ccw)/2                       = "
          f"{math.pi - (worst['theta_cw'] + worst['theta_ccw']) / 2:.12f} rad "
          f"({math.degrees(math.pi - (worst['theta_cw'] + worst['theta_ccw']) / 2):.6f} deg)")
    print(f"   difference = {lhs - (math.pi - (worst['theta_cw'] + worst['theta_ccw']) / 2):+.6e} rad")
    # cap test: sign of the site against the chord A--Aprev
    # chord line through A and Aprev; "cap" = same side as the arc midpoint
    def side(P, X, Y):
        return float(np.cross(Y - X, P - X))
    mid = (A + Aprev) / 2
    arc_mid = np.array([math.cos((math.atan2(A[1], A[0]) + math.atan2(Aprev[1], Aprev[0])) / 2),
                        math.sin((math.atan2(A[1], A[0]) + math.atan2(Aprev[1], Aprev[0])) / 2)])
    s_site = side(S[v_cw], A, Aprev)
    s_arc = side(arc_mid, A, Aprev)
    print(f"\n   cap test (chord A--A_prev): cross(site)={s_site:+.6e} cross(arc midpoint)={s_arc:+.6e}"
          f" -> site inside cap: {s_site * s_arc > 0}")
    print(f"   |v_cw - A| = {np.linalg.norm(S[v_cw] - A):.9f}   |v_cw - A_prev| = "
          f"{np.linalg.norm(S[v_cw] - Aprev):.9f}")
    # R3: cell of v_cw via explicit half-plane occupancy
    th, rad = cell_polygon(S, v_cw, nsamp=2000)
    j = int(np.argmin(np.abs(np.angle(np.exp(1j * (th - math.atan2(A[1], A[0])))))))
    print(f"   (R3) cell {v_cw} radial boundary at angle of A: r={rad[j]:.6f}"
          f"  (|A|=1 expected if A is on the cell boundary)")
