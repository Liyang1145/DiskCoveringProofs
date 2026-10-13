# -*- coding: utf-8 -*-
"""voronoi_area2.py -- corrected cellulation + area envelope (numeric screening).

Fixes vs. the first run:
  * cell area now computed on (polygon vertices inside D) + (crossing points) + arc
    segment, so the 11 cells must sum to pi (self-check);
  * envelope variants:
      E_opt  : beta_i = f_r(alpha_i) = 2 asin(r sin(alpha_i/2))     [proved iff alpha>=pi/3]
      E_safe : beta_i = 2 asin(r * max(sin(alpha_i/2), 1/2))        [proved for all alpha]
  * G_max(r) maximised over allocations with q_i equal (Jensen concavity in q) and the
    constraint sum beta >= 2pi.

Derivation of the alpha>=pi/3 threshold: the cell arc endpoints p1,p2 satisfy
|c_i p_j| = d_j <= r and angle(p1 c_i p2) = alpha; the chord obeys
chord^2 = d1^2+d2^2-2 d1 d2 cos alpha <= max over [0,r]^2 = r^2 max(4 sin^2(alpha/2), 1).
Hence beta = 2 asin(chord/2) <= 2 asin(r max(sin(alpha/2),1/2)) for ALL cells, and
beta <= f_r(alpha) whenever 2 sin(alpha/2) >= 1, i.e. alpha >= pi/3.
"""
import math, json, os
import numpy as np

ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"
S = 10 ** 17


# ------------------------------------------------------------------ geometry
def clip(poly, a, b, eps=1e-13):
    out = []
    n = len(poly)
    for k in range(n):
        p = poly[k]; q = poly[(k + 1) % n]
        fp = a[0] * p[0] + a[1] * p[1] - b
        fq = a[0] * q[0] + a[1] * q[1] - b
        if fp <= eps:
            out.append(p)
        if (fp < -eps < fq) or (fq < -eps < fp):
            t = fp / (fp - fq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def vor_cell(i, C, box=5.0):
    poly = [(-box, -box), (box, -box), (box, box), (-box, box)]
    ci = C[i]
    for j, cj in enumerate(C):
        if j == i:
            continue
        a = (2 * (cj[0] - ci[0]), 2 * (cj[1] - ci[1]))
        b = (cj[0] ** 2 + cj[1] ** 2) - (ci[0] ** 2 + ci[1] ** 2)
        poly = clip(poly, a, b)
        if len(poly) < 3:
            return None
    return poly


def cross_circle(p, q):
    dx, dy = q[0] - p[0], q[1] - p[1]
    A = dx * dx + dy * dy
    B = 2 * (p[0] * dx + p[1] * dy)
    Cc = p[0] ** 2 + p[1] ** 2 - 1
    disc = B * B - 4 * A * Cc
    if disc < 0 or A == 0:
        return []
    res = []
    for s in (-1, 1):
        t = (-B + s * math.sqrt(disc)) / (2 * A)
        if 0 <= t <= 1:
            res.append((p[0] + t * dx, p[1] + t * dy))
    return res


def cell_info(poly, ci):
    """walk the polygon; build the boundary of (poly cap unit disk):
       consecutive inside-runs joined by arcs. area + straight-side count + arc measures."""
    n = len(poly)
    inside = [math.hypot(*p) <= 1 + 1e-12 for p in poly]
    # build a mixed vertex cycle: polygon vertices tagged inside/outside, plus crossings
    cyc = []           # list of ('v', idx) / ('c', (x,y))
    for k in range(n):
        p = poly[k]; q = poly[(k + 1) % n]
        if inside[k]:
            cyc.append(("v", k))
        for c in cross_circle(p, q):
            cyc.append(("c", c))
    if not cyc:
        return dict(kind="empty", area=0.0, sides=0, arcs=[], chord=[], alpha=[])
    # rotate to start at a crossing
    start = next((i for i, t in enumerate(cyc) if t[0] == "c"), None)
    if start is None:
        # whole polygon (or nothing) inside
        if all(inside):
            pts = [poly[k] for k in range(n)]
            return dict(kind="interior", area=poly_area(pts), sides=n, arcs=[], chord=[], alpha=[])
        return dict(kind="empty", area=0.0, sides=0, arcs=[], chord=[], alpha=[])
    cyc = cyc[start:] + cyc[:start]
    # group into: inside run -> arc -> inside run -> arc ...
    area = 0.0
    sides = 0
    arcs = []
    crossings = [c for t, c in cyc if t == "c"]
    seq_pts = [poly[k] for t, k in [(t, c) for t, c in [(t, (c if t == "v" else None)) for t, c in cyc]] if t == "v"] \
        if False else [poly[k] for t, k in [(t, k) for t, k in cyc if t == "v"]]
    # walk: accumulate polygon edges inside; each arc between two crossings
    idx = [t for t in cyc]
    m = len(idx)
    cur_run = []
    runs = []
    for t in idx:
        if t[0] == "v":
            cur_run.append(poly[t[1]])
        else:
            if cur_run:
                runs.append((cur_run, t[1]))
                cur_run = []
            else:
                runs.append(([], t[1]))
    if cur_run:
        runs.append((cur_run, None))
    # close the cycle: the first crossing closes the last run
    if runs and runs[-1][1] is None:
        last_pts, _ = runs.pop()
        first_c = None
        for t in idx:
            if t[0] == "c":
                first_c = t[1]
                break
        runs.append((last_pts, first_c))
    if runs and runs[0][0] == []:
        # merge first (empty) run into last for closure
        pass
    # recompute: every inside run contributes a polyline; arcs connect run-end to next run-start
    chain = []
    for pts, endc in runs:
        if pts:
            sides += len(pts) + 1          # edges along the run + the edge into the next crossing
            chain.extend(pts)
            chain.append(endc)
        else:
            chain.append(endc)
    # close
    if chain and chain[0] != chain[-1]:
        chain.append(chain[0])
    # area: shoelace over chain (straight approximation) + arc corrections
    xx = [p[0] for p in chain]; yy = [p[1] for p in chain]
    A = 0.0
    for k in range(len(chain) - 1):
        A += xx[k] * yy[k + 1] - xx[k + 1] * yy[k]
    A = abs(A) / 2
    for k in range(len(runs)):
        pts, endc = runs[k]
        if not pts:
            continue
        st = runs[k][1] if False else None
    # arcs: consecutive crossings that are not separated by an inside run
    prev_c = None
    for k in range(len(runs)):
        pts, endc = runs[k]
        if not pts:
            st = runs[k - 1][1] if k > 0 else runs[-1][1]
            # arc from st to endc
            for (p0, p1) in ((st, endc),):
                t0 = math.atan2(p0[1], p0[0]); t1 = math.atan2(p1[1], p1[0])
                # choose the arc that is inside the polygon
                best = None
                for (s0, s1, w) in ((t0, t1, 1), (t1, t0, -1)):
                    d = (s1 - s0) % (2 * math.pi)
                    mid = s0 + d / 2
                    mp = (math.cos(mid), math.sin(mid))
                    if point_in_poly(mp, poly):
                        best = (d, s0, s1)
                        break
                if best is None:
                    continue
                d, s0, s1 = best
                seg = (d - math.sin(d)) / 2 if d <= math.pi else (d - math.sin(d)) / 2
                # segment area for arc measure d (d can exceed pi -> formula still exact)
                A += seg
                arcs.append(dict(beta=d, p0=p0, p1=p1))
                if st is not None:
                    pass
    return dict(kind="boundary" if arcs else "interior", area=A, sides=sides, arcs=arcs,
                crossings=crossings)


def poly_area(pts):
    n = len(pts)
    if n < 3:
        return 0.0
    s = 0.0
    for k in range(n):
        s += pts[k][0] * pts[(k + 1) % n][1] - pts[(k + 1) % n][0] * pts[k][1]
    return abs(s) / 2


def point_in_poly(p, poly):
    pos = neg = 0
    n = len(poly)
    for k in range(n):
        x1, y1 = poly[k]; x2, y2 = poly[(k + 1) % n]
        cr = (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1)
        if cr > 0:
            pos += 1
        elif cr < 0:
            neg += 1
    return pos == 0 or neg == 0


def analyse(tag, C, r, r_geom=None):
    r_geom = r if r_geom is None else r_geom
    print("-" * 76)
    print("CONFIG %s  r_env=%.9f r_geom=%.9f" % (tag, r, r_geom))
    tot = 0.0; env_o = 0.0; env_s = 0.0; bnd = []; hub = []
    for i in range(len(C)):
        poly = vor_cell(i, C)
        if poly is None:
            continue
        inf = cell_info(poly, C[i])
        tot += inf["area"]
        if inf["kind"] == "boundary" and len(inf["arcs"]) == 1:
            a = inf["arcs"][0]
            p0, p1 = a["p0"], a["p1"]
            v1 = (p0[0] - C[i][0], p0[1] - C[i][1]); v2 = (p1[0] - C[i][0], p1[1] - C[i][1])
            d1 = math.hypot(*v1); d2 = math.hypot(*v2)
            cang = (v1[0] * v2[0] + v1[1] * v2[1]) / (d1 * d2)
            alpha = math.acos(max(-1, min(1, cang)))
            beta = a["beta"]
            f_opt = 2 * math.asin(min(1.0, r * math.sin(alpha / 2)))
            f_safe = 2 * math.asin(min(1.0, r * max(math.sin(alpha / 2), 0.5)))
            seg_opt = (f_opt - math.sin(f_opt)) / 2
            seg_safe = (f_safe - math.sin(f_safe)) / 2
            eo = seg_opt + 0.5 * r * r * math.sin(alpha) + 0.5 * r * r * inf["sides"] * math.sin((2 * math.pi - alpha) / inf["sides"])
            es = seg_safe + 0.5 * r * r * math.sin(alpha) + 0.5 * r * r * inf["sides"] * math.sin((2 * math.pi - alpha) / inf["sides"])
            env_o += eo; env_s += es
            bnd.append((i, inf["sides"], alpha, beta, d1, d2, inf["area"], eo, es))
        else:
            k = inf["sides"]
            e = 0.5 * r * r * k * math.sin(2 * math.pi / k)
            env_o += e; env_s += e
            hub.append((i, k, inf["area"], e))
    print("   cells: %d boundary + %d interior ; sum of true areas = %.12f (pi = %.12f) diff=%+.2e"
          % (len(bnd), len(hub), tot, math.pi, tot - math.pi))
    sb = []
    for (i, q, alpha, beta, d1, d2, ar, eo, es) in bnd:
        sb.append((i, q, alpha, beta, d1, d2, ar, eo))
        ident = abs(2 * math.asin(min(1.0, r_geom * math.sin(alpha / 2))) - beta) < 1e-9
        print("     c%-2d q=%d alpha=%.6f beta=%.6f d1=%.6f d2=%.6f | area=%.6f env_opt=%.6f (slack %+.2e)"
              % (i, q, alpha, beta, d1, d2, ar, eo, eo - ar))
    for (i, k, ar, e) in hub:
        print("     hub c%-2d k=%d area=%.6f env=%.6f (slack %+.2e)" % (i, k, ar, e, e - ar))
    qsum = sum(b[1] for b in bnd); ksum = sum(h[1] for h in hub)
    print("   budget: sum q=%d k1+k2=%d total=%d (=2e, e=%d) <= 42 ? %s"
          % (qsum, ksum, qsum + ksum, (qsum + ksum) // 2, qsum + ksum <= 42))
    print("   ENVELOPE opt  = %.9f  (pi = %.9f)  slack %+.3e" % (env_o, math.pi, env_o - math.pi))
    print("   ENVELOPE safe = %.9f  slack %+.3e" % (env_s, env_s - math.pi))
    return bnd, hub


# ------------------------------------------------------------------ envelope maximisation
def fb_opt(r, a):
    return 2 * math.asin(min(1.0, r * math.sin(a / 2)))


def fb_safe(r, a):
    return 2 * math.asin(min(1.0, r * max(math.sin(a / 2), 0.5)))


def cell_env(r, q, a, fb):
    b = fb(r, a)
    return (b - math.sin(b)) / 2 + 0.5 * r * r * math.sin(a) + 0.5 * r * r * q * math.sin((2 * math.pi - a) / q)


def hub_env(r, k):
    return 0.5 * r * r * k * math.sin(2 * math.pi / k)


def G_max(r, fb, n=9, verbose=False):
    best = None
    for k1 in range(3, 40):
        for k2 in range(k1, 40):
            qtot = 42 - k1 - k2
            if qtot < 2 * n:
                continue
            q = qtot / float(n)
            # 1-D scan over alpha with n*beta(alpha) >= 2 pi
            lo, hi = 1e-6, math.pi
            bb = None
            for kk in range(4001):
                a = lo + (hi - lo) * kk / 4000.0
                if n * fb(r, a) >= 2 * math.pi:
                    v = n * cell_env(r, q, a, fb)
                    if bb is None or v > bb[0]:
                        bb = (v, a)
            if bb is None:
                continue
            tot = bb[0] + hub_env(r, k1) + hub_env(r, k2)
            if best is None or tot > best[0]:
                best = (tot, k1, k2, q, bb[1])
    if verbose and best:
        print("   G_max(r=%.6f)=%.9f  k1=%d k2=%d q_i=%.4f alpha=%.6f  pi=%.9f  slack=%+.3e"
              % (r, best[0], best[1], best[2], best[3], best[4], math.pi, best[0] - math.pi))
    return best


if __name__ == "__main__":
    C = [(int(a) / S, int(b) / S) for a, b in
         json.load(open(ROOT + r"\n11\upper\certified_object.json", encoding="utf-8"))["centers_scaled_1e17"]]
    print("=" * 76)
    print("PART A -- cellulation controls (saved certified object; R_saved=0.3799838531)")
    print("=" * 76)
    analyse("saved object, r_geom=R_saved", C, 0.3799838531198387090485182)
    analyse("saved object, r_geom=0.38", C, 0.38)
    print()
    print("=" * 76)
    print("PART B -- envelope maximised over allocations (equal q by concavity), alpha scan")
    print("=" * 76)
    for r in (0.3800, 0.3790, 0.3760, 0.3720, 0.3710, 0.3709, 0.3680, 0.3660, 0.3640, 0.3600):
        b1 = G_max(r, fb_opt)
        b2 = G_max(r, fb_safe)
        print("   r=%.4f  G_max(opt)=%.6f slack=%+.4f   G_max(safe)=%.6f slack=%+.4f"
              % (r, b1[0], b1[0] - math.pi, b2[0], b2[0] - math.pi))
