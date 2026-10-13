# -*- coding: utf-8 -*-
"""voronoi_area.py -- independent separable computation (numeric screening, NOT certified).

Input (lead): team-current/lead/VORONOI-BOUNDARY-REDUCTION.md
  disk cellulation of D by the 11 nearest-centre Voronoi cells; 9 ordered boundary
  cells (one arc + q_i straight sides, q_i >= 2), 2 compact interior cells (k_j >= 3),
  Sigma q + k1 + k2 = 2e <= 42.

Area envelope tested here (derived independently, then cross-checked against the FT
normalisation of Fejes Toth 2005; units: covering disks radius r, target radius 1):
  boundary cell i :  A_i <= F_r(alpha_i) + (r^2/2) q_i sin((2pi - alpha_i)/q_i)
      with beta_i = f_r(alpha_i) = 2 asin(r sin(alpha_i/2))  (exact chord identity)
      and   F_r(alpha) = (r^2/2) sin(alpha) + Seg(beta),  Seg(b) = (b - sin b)/2
  interior cell j :  A_j <= (r^2/2) k_j sin(2pi/k_j)
  sum_i beta_i >= 2pi

PART A: build an explicit configuration, compute its true Voronoi cellulation, and test
        soundness of the envelope cell-by-cell (envelope must be >= true area; the true
        total is pi).  Controls: the saved certified n=11 object at r=38/100 and r=R_saved,
        plus regular 9-ring configurations.
PART B: maximise the envelope over allocations (q_i, k1, k2) and the continuous alphas
        with sum beta >= 2pi; report G_max(r) and the threshold where G_max = pi.

All floats: screening only, not a certificate.
"""
import os, sys, json, math
import numpy as np

ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"
S = 10 ** 17


# ------------------------------------------------------------------ polygon tools
def clip_halfplane(poly, a, b, eps=1e-14):
    """clip convex polygon (list of (x,y), ccw or cw) by {x: a.x <= b}."""
    if not poly:
        return []
    out = []
    n = len(poly)
    for k in range(n):
        p = poly[k]
        q = poly[(k + 1) % n]
        fp = a[0] * p[0] + a[1] * p[1] - b
        fq = a[0] * q[0] + a[1] * q[1] - b
        if fp <= eps:
            out.append(p)
        if (fp < -eps and fq > eps) or (fp > eps and fq < -eps):
            t = fp / (fp - fq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def poly_area(poly):
    n = len(poly)
    if n < 3:
        return 0.0
    s = 0.0
    for k in range(n):
        x1, y1 = poly[k]
        x2, y2 = poly[(k + 1) % n]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


def cell_of_centre(idx, C, box=4.0):
    """Voronoi cell of centre idx inside the square [-box,box]^2 (halfplane clipping)."""
    poly = [(-box, -box), (box, -box), (box, box), (-box, box)]
    ci = C[idx]
    for j, cj in enumerate(C):
        if j == idx:
            continue
        a = (2 * (cj[0] - ci[0]), 2 * (cj[1] - ci[1]))
        b = (cj[0] ** 2 + cj[1] ** 2) - (ci[0] ** 2 + ci[1] ** 2)
        poly = clip_halfplane(poly, a, b)
        if len(poly) < 3:
            return None
    return poly


def cell_metrics(poly, ci):
    """split the cell into the part inside the unit disk: returns dict with
       sides (straight edges), area, arc measure beta (at origin), alpha (at ci)."""
    inside = [p for p in poly if p[0] ** 2 + p[1] ** 2 <= 1 + 1e-12]
    cross = []
    n = len(poly)
    for k in range(n):
        p = poly[k]; q = poly[(k + 1) % n]
        rp = math.hypot(*p); rq = math.hypot(*q)
        if (rp - 1) * (rq - 1) < 0:
            # segment p-q crosses the unit circle; solve exactly
            dx, dy = q[0] - p[0], q[1] - p[1]
            A = dx * dx + dy * dy
            B = 2 * (p[0] * dx + p[1] * dy)
            Cc = p[0] ** 2 + p[1] ** 2 - 1
            disc = B * B - 4 * A * Cc
            if disc < 0:
                continue
            t = (-B + math.sqrt(disc)) / (2 * A)
            if not (0 <= t <= 1):
                t = (-B - math.sqrt(disc)) / (2 * A)
            if 0 <= t <= 1:
                cross.append((p[0] + t * dx, p[1] + t * dy))
    area_in = poly_area(poly) if not cross else poly_area(inside) if len(inside) >= 3 else 0.0
    res = dict(sides=None, area=0.0, beta=0.0, alpha=0.0, kind="interior")
    if len(cross) == 2:
        # choose the arc that lies inside the polygon: test angular midpoints
        a1 = math.atan2(cross[0][1], cross[0][0])
        a2 = math.atan2(cross[1][1], cross[1][0])
        for d in (a1, a2):
            pass
        # two candidate arcs: ccw from a1 to a2, or from a2 to a1
        def arc_meas(t0, t1):
            d = (t1 - t0) % (2 * math.pi)
            return d if d > 0 else 2 * math.pi
        cands = []
        for (t0, t1, p0, p1) in ((a1, a2, cross[0], cross[1]), (a2, a1, cross[1], cross[0])):
            d = arc_meas(t0, t1)
            mid = t0 + d / 2
            mp = (math.cos(mid), math.sin(mid))
            if point_in_poly(mp, poly):
                cands.append((d, t0, t1, p0, p1))
        if cands:
            beta, t0, t1, p0, p1 = cands[0]
            seg = (beta - math.sin(beta)) / 2
            res.update(kind="boundary", beta=beta, area=area_in + seg)
            # alpha = angle at ci between the two crossings
            v1 = (p0[0] - ci[0], p0[1] - ci[1])
            v2 = (p1[0] - ci[0], p1[1] - ci[1])
            d1 = math.hypot(*v1); d2 = math.hypot(*v2)
            cosang = (v1[0] * v2[0] + v1[1] * v2[1]) / (d1 * d2)
            res["alpha"] = math.acos(max(-1.0, min(1.0, cosang)))
            res["radii"] = (d1, d2)
            res["area"] = area_in + seg
    else:
        res["area"] = poly_area(poly)
    # straight sides = number of edges of the clipped polygon that survive
    if len(cross) == 2:
        res["sides"] = len([p for p in inside]) + 1
    else:
        res["sides"] = len(poly)
    return res


def point_in_poly(p, poly):
    # convex: all cross products of consecutive edges have the same sign
    n = len(poly)
    pos = neg = 0
    for k in range(n):
        x1, y1 = poly[k]
        x2, y2 = poly[(k + 1) % n]
        cr = (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1)
        if cr > 0:
            pos += 1
        elif cr < 0:
            neg += 1
    return pos == 0 or neg == 0


# ------------------------------------------------------------------ envelope
def beta_of_alpha(r, a):
    return 2 * math.asin(max(-1.0, min(1.0, r * math.sin(a / 2))))


def F_env(r, a):
    b = beta_of_alpha(r, a)
    return 0.5 * r * r * math.sin(a) + (b - math.sin(b)) / 2


def poly_env(r, q, a):
    return 0.5 * r * r * q * math.sin((2 * math.pi - a) / q)


def hub_env(r, k):
    return 0.5 * r * r * k * math.sin(2 * math.pi / k)


# ------------------------------------------------------------------ PART A
def analyse_config(tag, C, r, r_geom=None):
    """C: list of 11 centres; r = radius used in the envelope; r_geom = radius used to
       compute the tip geometry (defaults to r)."""
    r_geom = r if r_geom is None else r_geom
    print("-" * 74)
    print("CONFIG %s   r(envelope)=%.9f  r(geometry)=%.9f" % (tag, r, r_geom))
    tot_area = 0.0
    tot_env = 0.0
    bnd = []
    hub = []
    for i in range(len(C)):
        poly = cell_of_centre(i, C)
        if poly is None:
            print("   centre %d: empty cell" % i)
            continue
        m = cell_metrics(poly, C[i])
        tot_area += m["area"]
        if m["kind"] == "boundary":
            bnd.append((i, m))
        else:
            hub.append((i, m))
    print("   boundary cells %d, interior cells %d, sum of cell areas = %.12f (pi=%.12f)"
          % (len(bnd), len(hub), tot_area, math.pi))
    qsum = 0
    ksum = 0
    for i, m in bnd:
        b_hat = beta_of_alpha(r, m["alpha"])
        env = F_env(r, m["alpha"]) + poly_env(r, m["sides"], m["alpha"])
        tot_env += env
        qsum += m["sides"]
        ok_id = abs(b_hat - m["beta"]) < 1e-9
        print("   bnd cell c%-2d q=%-2d beta=%.9f alpha=%.9f | chord identity %s | beta_hat=%.9f"
              % (i, m["sides"], m["beta"], m["alpha"], ok_id, b_hat))
        print("        true area=%.9f  envelope=%.9f  slack=%+.3e" % (m["area"], env, env - m["area"]))
    for i, m in hub:
        env = hub_env(r, m["sides"])
        tot_env += env
        ksum += m["sides"]
        print("   hub cell c%-2d k=%-2d true area=%.9f  envelope=%.9f  slack=%+.3e"
              % (i, m["sides"], m["area"], env, env - m["area"]))
    nsides = 2 * (qsum + ksum)
    print("   side budget: sum q = %d, k1+k2 = %d, sum q+k = %d = 2e  (e=%d, budget 42)"
          % (qsum, ksum, qsum + ksum, (qsum + ksum) // 2))
    print("   ENVELOPE TOTAL = %.9f   pi = %.9f   slack = %+.3e  (must be >= 0)"
          % (tot_env, math.pi, tot_env - math.pi))
    return dict(bnd=bnd, hub=hub, tot_area=tot_area, tot_env=tot_env)


def load_saved():
    p = ROOT + r"\n11\upper\certified_object.json"
    J = json.load(open(p, encoding="utf-8"))
    C = [(int(a) / S, int(b) / S) for a, b in J["centers_scaled_1e17"]]
    return C


def regular_9ring(r, hub_off=0.02):
    """9 ring disks (arcs 2pi/9 each) at rho = sqrt(1-r^2) + 2 tiny hubs at +-hub_off."""
    rho = math.sqrt(1 - r * r)
    C = []
    for k in range(9):
        # centre at angle so that the arc is centred at angle (k+0.5)*2pi/9
        th = (k + 0.5) * 2 * math.pi / 9
        # half-arc of disk: t = arccos((1+rho^2-r^2)/(2 rho)); place centre at th + t?
        C.append((rho * math.cos(th), rho * math.sin(th)))
    C.append((hub_off, 0.0))
    C.append((-hub_off, 0.0))
    return C


# ------------------------------------------------------------------ PART B
def G_max(r, kmax=42, verbose=True):
    best = None
    for k1 in range(3, 40):
        for k2 in range(k1, 40):
            qtot = 42 - k1 - k2
            if qtot < 18:
                continue
            q = qtot / 9.0
            # maximise over alphas with sum beta >= 2pi (scipy if available, else grid)
            val, alphas = alpha_opt(r, q, 9)
            tot = val + hub_env(r, k1) + hub_env(r, k2)
            if best is None or tot > best[0]:
                best = (tot, k1, k2, q, alphas)
    if verbose:
        tot, k1, k2, q, alphas = best
        print("   G_max(r=%.6f) = %.9f  at k1=%d k2=%d q_i=%.4f  alpha=%.6f..%.6f  (pi=%.9f)"
              % (r, tot, k1, k2, q, min(alphas), max(alphas), math.pi))
    return best


def alpha_opt(r, q, n=9):
    """maximise n*[F(a)+poly(q,a)] subject to sum beta(a_i) >= 2pi (a_i in (0,pi])."""
    def g(a):
        return F_env(r, a) + poly_env(r, q, a)

    def neg_obj(x):
        return -sum(g(a) for a in x)

    def con(x):
        return sum(beta_of_alpha(r, a) for a in x) - 2 * math.pi

    try:
        from scipy.optimize import minimize
        cons = [{"type": "ineq", "fun": con}]
        bnds = [(1e-6, math.pi)] * n
        best = None
        for start in (2.24, 2.0, 1.5, 2.6, 1.2):
            x0 = np.array([start] * n)
            res = minimize(neg_obj, x0, bounds=bnds, constraints=cons, method="SLSQP",
                           options=dict(maxiter=400, ftol=1e-14))
            if best is None or res.fun < best.fun:
                best = res
        x = list(best.x)
        return sum(g(a) for a in x), x
    except Exception as e:
        # grid fallback: equal alphas only, scan
        lo, hi = 1e-6, math.pi
        best = None
        for k in range(20001):
            a = lo + (hi - lo) * k / 20000
            if 9 * beta_of_alpha(r, a) >= 2 * math.pi:
                v = 9 * g(a)
                if best is None or v > best[0]:
                    best = (v, [a] * 9)
        return best if best else (float("nan"), [float("nan")] * 9)


if __name__ == "__main__":
    print("=" * 74)
    print("PART A -- cellulation controls (soundness of the area envelope)")
    print("=" * 74)
    C = load_saved()
    analyse_config("saved certified object, r=38/100", C, 0.38)
    analyse_config("saved certified object, r=R_saved", C, 0.3799838531198387090485182)
    for r in (0.45, 0.40, 0.38):
        analyse_config("regular 9-ring + 2 hubs, r=%.2f" % r, regular_9ring(r), r)
    print()
    print("=" * 74)
    print("PART B -- envelope maximised over allocations and alphas (numeric screening)")
    print("=" * 74)
    for r in (0.38, 0.3799, 0.378, 0.376, 0.374, 0.372, 0.3710, 0.3709):
        G_max(r)
