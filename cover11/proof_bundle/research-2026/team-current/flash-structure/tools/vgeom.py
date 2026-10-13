"""flash-structure core geometry: inner-root ring ledgers, tips, Voronoi/Delaunay checks.

Conventions (documented in out/REPORT.md):
  r          : common radius, 0<r<1/2
  t[i]       : half-width of the ACTUAL boundary arc of ring disk i (radians), 0<t<=asin(r)
  o[i]       : overlap of arcs i and i+1  (>=0),   gamma[i] = t[i]+t[i+1]-o[i] = centre angle gap
  rho(t)     : inner root   cos t - sqrt(r^2 - sin^2 t)
  c[i]       : rho(t[i]) * u(phi[i]),  phi[1]=0, phi[i+1]=phi[i]+gamma[i]
  H          : D \\ union_i B(c_i,r)   (hole of the ring)
  crossings of circles i,i+1 : M +- h*nperp,  M=(c_i+c_{i+1})/2, h=sqrt(r^2-|c_i-c_{i+1}|^2/4),
               nperp = rot_{-90}(c_{i+1}-c_i)/|c_{i+1}-c_i|   (M.nperp > 0, so M-h*nperp is the tip
               when o_i = 0, where it equals c_i+c_{i+1}-u(phi_i+t_i))
"""
import math

import numpy as np


# ---------------------------------------------------------------- ring basics
def rho(t, r):
    s = math.sin(t)
    return math.cos(t) - math.sqrt(max(0.0, r * r - s * s))


def drho_dt(t, r):
    s = math.sin(t)
    q = math.sqrt(max(1e-300, r * r - s * s))
    return s * rho(t, r) / q


def t_from_center(a, r):
    cth = max(-1.0, min(1.0, (1.0 + a * a - r * r) / (2.0 * a)))
    return math.acos(cth)


def build_ring(r, t, o):
    n = len(t)
    gamma = [t[i] + t[(i + 1) % n] - o[i] for i in range(n)]
    phi, acc = [], 0.0
    for i in range(n):
        phi.append(acc)
        acc += gamma[i]
    cen = [(rho(t[i], r) * math.cos(phi[i]), rho(t[i], r) * math.sin(phi[i])) for i in range(n)]
    return phi, cen, gamma


def ledger_from_arcs(r, phis, t):
    n = len(t)
    o = []
    for i in range(n):
        g = phis[(i + 1) % n] - phis[i]
        if i == n - 1:
            g += 2 * math.pi
        o.append(t[i] + t[(i + 1) % n] - g)
    return o


def closed_form_tip_sq(r, tk, tk1, gamma):
    """|v|^2 for the crossing M - h*nperp : rho_k rho_k1 cos g + r^2 - rho_k rho_k1 sin g cot(beta)."""
    rk, rk1 = rho(tk, r), rho(tk1, r)
    d2 = rk * rk + rk1 * rk1 - 2 * rk * rk1 * math.cos(gamma)
    d = math.sqrt(max(0.0, d2))
    if d == 0.0:
        return None
    sb = min(1.0, d / (2 * r))
    cb = math.sqrt(max(0.0, 1 - sb * sb))
    cotb = cb / sb if sb > 0 else float("inf")
    return rk * rk1 * math.cos(gamma) + r * r - rk * rk1 * math.sin(gamma) * cotb


def crossings(r, ck, ck1):
    """both circle-circle crossings of two equal circles: returns (M-h*n, M+h*n, M, h, d)."""
    M = (0.5 * (ck[0] + ck1[0]), 0.5 * (ck[1] + ck1[1]))
    dx, dy = ck1[0] - ck[0], ck1[1] - ck[1]
    d = math.hypot(dx, dy)
    h = math.sqrt(max(0.0, r * r - d * d / 4.0))
    nx, ny = dy / d, -dx / d
    return ((M[0] - h * nx, M[1] - h * ny), (M[0] + h * nx, M[1] + h * ny), M, h, d)


def dist(p, q):
    return math.hypot(p[0] - q[0], p[1] - q[1])


# ---------------------------------------------------------------- audits
def audit_ledger(r, t, o):
    """independent re-derivation of coverage / non-adjacency / private lengths."""
    n = len(t)
    phi, cen, gamma = build_ring(r, t, o)
    two_pi = 2 * math.pi
    L = [phi[i] - t[i] for i in range(n)]
    R = [phi[i] + t[i] for i in range(n)]
    Lu, Ru = [L[0]], [R[0]]
    for i in range(1, n):
        x = L[i]
        while x < Lu[-1]:
            x += two_pi
        Lu.append(x)
    for i in range(1, n):
        x = R[i]
        while x < Ru[-1]:
            x += two_pi
        Ru.append(x)
    cover = all(Ru[i] >= Lu[i + 1] for i in range(n - 1)) and (Ru[-1] >= Lu[0] + two_pi)
    nonadj = all(Ru[i] < Lu[i + 2] for i in range(n - 2))
    ell = [2 * t[i] - o[(i - 1) % n] - o[i] for i in range(n)]
    sumo = abs(sum(o) - (2 * sum(t) - two_pi))
    return dict(phi=phi, cen=cen, gamma=gamma, cover=cover, nonadj=nonadj, ell=ell,
                sum_err=sumo, L=Lu, R=Ru)


def tips_cyclic(r, t, o):
    """crossings for each consecutive pair; 'v' is the crossing inside D (smaller radius)."""
    phi, cen, gamma = build_ring(r, t, o)
    out = []
    n = len(t)
    for i in range(n):
        p1, p2, M, h, d = crossings(r, cen[i], cen[(i + 1) % n])
        a, b = dist(p1, (0, 0)), dist(p2, (0, 0))
        if a < b:
            v, r_in, v_out, r_out = p1, a, p2, b
        else:
            v, r_in, v_out, r_out = p2, b, p1, a
        out.append(dict(i=i, v=v, r_in=r_in, v_out=v_out, r_out=r_out, M=M, h=h, d=d))
    return out


def tip_margin(r, t, o):
    """min over k, j not in {k,k+1} of |v_k - c_j| - r."""
    phi, cen, gamma = build_ring(r, t, o)
    n = len(t)
    tc = tips_cyclic(r, t, o)
    worst, tab = float("inf"), []
    for k in range(n):
        v = tc[k]["v"]
        m, arg = float("inf"), None
        for j in range(n):
            if j in (k, (k + 1) % n):
                continue
            val = dist(v, cen[j]) - r
            if val < m:
                m, arg = val, j
        tab.append((k, m, arg))
        worst = min(worst, m)
    return worst, tab, tc


def ray_clear(r, t, o, k, eps_list=(1e-4, 1e-6)):
    """is v_k - eps*u(arg v_k) inside D and outside every ring disk ?"""
    phi, cen, gamma = build_ring(r, t, o)
    n = len(t)
    p = tips_cyclic(r, t, o)[k]["v"]
    rv = math.hypot(*p)
    ux, uy = p[0] / rv, p[1] / rv
    res = []
    for eps in eps_list:
        q = (p[0] - eps * ux, p[1] - eps * uy)
        res.append(dict(eps=eps, inside_D=math.hypot(*q) < 1.0,
                        min_clear=min(dist(q, cen[j]) - r for j in range(n))))
    return res


# ---------------------------------------------------------------- exact legal-ledger sampler
def sample_ledger(r, rng, Emax_frac=1.0, n=9):
    """Sample the legal ledger domain L_r (ARC-COORD P2):
       0<t_i<=asin r, o_i>=0, sum o = 2 sum t - 2pi, ell_i = 2t_i - o_{i-1} - o_i > 0.
    Method: t with sum t = pi+E; gaps gamma_i in (|t_i-t_{i+1}|, t_i+t_{i+1}] with sum gamma = 2pi
    and gamma_{i-1}+gamma_i > t_{i-1}+t_{i+1} (== ell_i>0); o_i = t_i+t_{i+1}-gamma_i.
    Returns (t, o, gamma, E) or None.
    """
    amax = math.asin(r)
    Emax = max(0.0, n * amax - math.pi) * Emax_frac
    tmin = max(1e-7, math.pi - (n - 1) * amax)     # = amax - Emax  (for Emax>0)
    if Emax <= 0:
        return None
    # any legal t has the form t_i = amax - s_i with s_i>=0, sum s = Emax - E =: delta <= Emax
    delta = rng.uniform(0.0, 1.0) * Emax
    if hasattr(rng, "standard_exponential"):
        w = np.asarray(rng.standard_exponential(size=n))
    else:
        w = np.array([rng.expovariate(1.0) for _ in range(n)])
    s = delta * w / w.sum()
    t = list(amax - s)
    if min(t) < tmin - 1e-12 or max(t) > amax + 1e-15:
        return None
    E = Emax - delta
    dl = [abs(t[i] - t[(i + 1) % n]) for i in range(n)]
    cap = [t[i] + t[(i + 1) % n] for i in range(n)]
    for _ in range(80):
        wg = [rng.uniform(0.02, 1.0) for _ in range(n)]

        def gam(lam):
            return [min(cap[i] - 1e-13, dl[i] + lam * wg[i] * (cap[i] - dl[i])) for i in range(n)]

        if sum(gam(0.0)) > 2 * math.pi + 1e-15:
            return None
        lo, hi = 0.0, 1e9
        for _ in range(300):
            mid = 0.5 * (lo + hi)
            if sum(gam(mid)) < 2 * math.pi:
                lo = mid
            else:
                hi = mid
        g = gam(hi)
        if abs(sum(g) - 2 * math.pi) > 1e-12:
            continue
        if not all(g[(i - 1) % n] + g[i] > t[(i - 1) % n] + t[(i + 1) % n] + 1e-12
                   for i in range(n)):
            continue
        o = [t[i] + t[(i + 1) % n] - g[i] for i in range(n)]
        if min(o) < -1e-15:
            continue
        return t, o, g, E
    return None


# ---------------------------------------------------------------- config
def load_fammin(path):
    import json
    with open(path, "r", encoding="utf-8") as fh:
        js = json.load(fh)
    return js, [(float(a), float(b)) for a, b in js["centers"]]


def classify(cen, r):
    ring, hub = [], []
    for i, (x, y) in enumerate(cen):
        a = math.hypot(x, y)
        (ring if abs(a - 1.0) <= r + 1e-12 else hub).append(i)
    return ring, hub
