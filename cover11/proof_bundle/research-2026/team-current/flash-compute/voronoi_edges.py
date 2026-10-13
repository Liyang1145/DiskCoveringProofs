# -*- coding: utf-8 -*-
"""voronoi_edges.py -- edge-level audit of the Voronoi cellulation + the lead's angle algebra.

Checks on the saved certified object (a genuine 9-ring + 2-hub covering):
  (V1) every interior Voronoi edge is shared by exactly two cells, and the two apex
       angles at the two centres are EQUAL (edge congruence);
  (V2) angle bookkeeping: sum over hub-ring edges of tau = 4 pi - 2 d tau_hh,
       sum over ring-ring edges (both sides) = 14 pi - A + 2 d tau_hh,  A = sum alpha_i;
  (V3) combinatorics: E = E_rr + E_hr + d <= 21, E_rr >= 9, K = k1+k2 = E_hr + 2d,
       sum q = 2 E_rr + E_hr, 2E = sum q + K;
  (V4) area decomposition of the envelope slack by component:
       caps+arc-triangles / ring-ring triangles / hub-ring triangles / hub triangle.

All numeric (float screening), not a certificate.
"""
import math, json

ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"
S = 10 ** 17


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


def seg_on_line_in_poly(p0, dirv, poly, eps=1e-12):
    """intersect the line p0 + t*dirv with convex polygon poly -> (t_lo,t_hi) or None.
    orientation-agnostic: inward normals are fixed by testing the polygon centroid."""
    cx = sum(p[0] for p in poly) / len(poly)
    cy = sum(p[1] for p in poly) / len(poly)
    lo, hi = -1e9, 1e9
    n = len(poly)
    for k in range(n):
        a1, a2 = poly[k]; b1, b2 = poly[(k + 1) % n]
        ex, ey = b1 - a1, b2 - a2
        nx, ny = -ey, ex
        # make (nx,ny) the OUTWARD normal (interior = {x : n.(x-a) <= 0})
        if nx * (cx - a1) + ny * (cy - a2) > 0:
            nx, ny = -nx, -ny
        # constraint: n . (p0 + t dirv - a) <= 0
        den = nx * dirv[0] + ny * dirv[1]
        num = nx * (p0[0] - a1) + ny * (p0[1] - a2)
        if abs(den) < 1e-15:
            if num > eps:
                return None
        else:
            t = -num / den
            if den > 0:
                hi = min(hi, t)
            else:
                lo = max(lo, t)
    if hi <= lo + 1e-12:
        return None
    return (lo, hi)


def poly_area(pts):
    n = len(pts)
    if n < 3:
        return 0.0
    s = 0.0
    for k in range(n):
        s += pts[k][0] * pts[(k + 1) % n][1] - pts[(k + 1) % n][0] * pts[k][1]
    return abs(s) / 2


def arc_info(poly, ci):
    """boundary arc endpoints of (poly cap D) and its angular measure at the origin."""
    n = len(poly)
    cross = []
    for k in range(n):
        p = poly[k]; q = poly[(k + 1) % n]
        for (x, y) in ((p, q),):
            rp = math.hypot(*p); rq = math.hypot(*q)
            if (rp - 1) * (rq - 1) < 0:
                dx, dy = q[0] - p[0], q[1] - p[1]
                A = dx * dx + dy * dy
                B = 2 * (p[0] * dx + p[1] * dy)
                Cc = p[0] ** 2 + p[1] ** 2 - 1
                disc = B * B - 4 * A * Cc
                if disc < 0:
                    continue
                for s in (-1, 1):
                    t = (-B + s * math.sqrt(disc)) / (2 * A)
                    if 0 <= t <= 1:
                        cross.append((p[0] + t * dx, p[1] + t * dy))
    if len(cross) != 2:
        return None
    c0, c1 = cross
    # pick the arc lying inside the polygon
    t0 = math.atan2(c0[1], c0[0]); t1 = math.atan2(c1[1], c1[0])
    for (s0, s1, p0, p1) in ((t0, t1, c0, c1), (t1, t0, c1, c0)):
        d = (s1 - s0) % (2 * math.pi)
        mid = s0 + d / 2
        mp = (math.cos(mid), math.sin(mid))
        pos = neg = 0
        for k in range(n):
            x1, y1 = poly[k]; x2, y2 = poly[(k + 1) % n]
            cr = (x2 - x1) * (mp[1] - y1) - (y2 - y1) * (mp[0] - x1)
            if cr > 0:
                pos += 1
            elif cr < 0:
                neg += 1
        if pos == 0 or neg == 0:
            v1 = (p0[0] - ci[0], p0[1] - ci[1]); v2 = (p1[0] - ci[0], p1[1] - ci[1])
            d1 = math.hypot(*v1); d2 = math.hypot(*v2)
            ca = (v1[0] * v2[0] + v1[1] * v2[1]) / (d1 * d2)
            return dict(beta=d, alpha=math.acos(max(-1, min(1, ca))), p0=p0, p1=p1, d1=d1, d2=d2)
    return None


if __name__ == "__main__":
    C = [(int(a) / S, int(b) / S) for a, b in
         json.load(open(ROOT + r"\n11\upper\certified_object.json", encoding="utf-8"))["centers_scaled_1e17"]]
    for r, tag in ((0.3799838531198387090485182, "R_saved"), (0.38, "0.38")):
        cells = {}
        for i in range(11):
            poly = vor_cell(i, C)
            cells[i] = poly
        info = {i: arc_info(cells[i], C[i]) for i in range(11)}
        bnd = [i for i in range(11) if info[i] is not None]
        hub = [i for i in range(11) if info[i] is None]
        print("=" * 78)
        print("r = %s (%s)   boundary cells %s   interior cells %s" % (tag, r, bnd, hub))
        A = sum(info[i]["alpha"] for i in bnd)
        SumBeta = sum(info[i]["beta"] for i in bnd)
        print("   A = sum alpha_i = %.9f (%.4f pi)   sum beta = %.9f (2pi = %.9f)"
              % (A, A / math.pi, SumBeta, 2 * math.pi))
        # other cell areas / sides
        HubArea = {}
        for i in hub:
            HubArea[i] = poly_area(cells[i])
            print("   hub cell %d: area=%.6f" % (i, HubArea[i]))
        # edges
        edges = []
        for a in range(11):
            for b in range(a + 1, 11):
                ca, cb = C[a], C[b]
                dvec = (cb[0] - ca[0], cb[1] - ca[1])
                rhs = (cb[0] ** 2 + cb[1] ** 2) - (ca[0] ** 2 + ca[1] ** 2)
                # line: 2 x . dvec = rhs ; direction perpendicular to dvec
                dirv = (-dvec[1], dvec[0])
                nrm = 2 * (dvec[0] ** 2 + dvec[1] ** 2)
                if nrm == 0:
                    continue
                # a point on the line: x0 = (rhs/2) * dvec / |dvec|^2
                x0 = (rhs / nrm * dvec[0] * 2 * 2 / 2, rhs / nrm * dvec[1] * 2 * 2 / 2)
                x0 = (rhs / (2 * (dvec[0] ** 2 + dvec[1] ** 2)) * dvec[0] * 2,
                      rhs / (2 * (dvec[0] ** 2 + dvec[1] ** 2)) * dvec[1] * 2)
                x0 = (rhs * dvec[0] / (2 * (dvec[0] ** 2 + dvec[1] ** 2)),
                      rhs * dvec[1] / (2 * (dvec[0] ** 2 + dvec[1] ** 2)))
                if cells[a] is None or cells[b] is None:
                    continue
                seg = seg_on_line_in_poly(x0, dirv, cells[a])
                segb = seg_on_line_in_poly(x0, dirv, cells[b])
                if seg is None or segb is None:
                    continue
                t0 = max(seg[0], segb[0]); t1 = min(seg[1], segb[1])
                # clip to the unit disk: the cellulation under study is D itself
                Aq = dirv[0] ** 2 + dirv[1] ** 2
                Bq = 2 * (x0[0] * dirv[0] + x0[1] * dirv[1])
                Cq = x0[0] ** 2 + x0[1] ** 2 - 1
                disc = Bq * Bq - 4 * Aq * Cq
                if disc <= 0:
                    continue
                r0 = (-Bq - math.sqrt(disc)) / (2 * Aq)
                r1 = (-Bq + math.sqrt(disc)) / (2 * Aq)
                t0 = max(t0, r0); t1 = min(t1, r1)
                if t1 <= t0 + 1e-12:
                    continue          # bisector line meets both cells but not on a common edge
                seg = (t0, t1)
                p0 = (x0[0] + t0 * dirv[0], x0[1] + t0 * dirv[1])
                p1 = (x0[0] + t1 * dirv[0], x0[1] + t1 * dirv[1])
                L = math.dist(p0, p1)
                # apex angles at both centres
                def apex(cc, p0, p1):
                    v1 = (p0[0] - cc[0], p0[1] - cc[1]); v2 = (p1[0] - cc[0], p1[1] - cc[1])
                    d1 = math.hypot(*v1); d2 = math.hypot(*v2)
                    return math.acos(max(-1, min(1, (v1[0] * v2[0] + v1[1] * v2[1]) / (d1 * d2)))), d1, d2
                ta, da1, da2 = apex(ca, p0, p1)
                tb, db1, db2 = apex(cb, p0, p1)
                # triangle area = 1/2 * base * perpendicular distance; the base lies on the
                # perpendicular bisector of c_a c_b, so the height is |c_a - c_b| / 2 (exact).
                hh = 0.5 * math.hypot(cb[0] - ca[0], cb[1] - ca[1])
                edges.append(dict(a=a, b=b, L=L, tau_a=ta, tau_b=tb, p0=p0, p1=p1,
                                  tri_a=0.5 * L * hh, tri_b=0.5 * L * hh))
        E = len(edges)
        rr = [e for e in edges if e["a"] in bnd and e["b"] in bnd]
        hr = [e for e in edges if (e["a"] in hub) != (e["b"] in hub)]
        hh = [e for e in edges if e["a"] in hub and e["b"] in hub]
        dcount = len(hh)
        print("   edges: E=%d  ring-ring=%d  hub-ring=%d  hub-hub=%d  (E<=21: %s ; E_rr>=9: %s)"
              % (E, len(rr), len(hr), len(hh), E <= 21, len(rr) >= 9))
        K = sum(len([1 for e in edges if e["a"] == i or e["b"] == i]) for i in hub)
        print("   K = hub sides = %d  ; E_hr + 2 d = %d  ; sum q = 2E_rr + E_hr = %d  ; 2E = %d"
              % (K, len(hr) + 2 * dcount, 2 * len(rr) + len(hr), 2 * E))
        # congruence check
        worst = max((abs(e["tau_a"] - e["tau_b"]) for e in edges), default=0.0)
        print("   (V1) max |tau_a - tau_b| over all interior edges = %.3e  (congruence)" % worst)
        T_hr = sum(e["tau_a"] + e["tau_b"] for e in hr) / 2 if hr else 0.0
        tau_hh = (hh[0]["tau_a"] if hh else 0.0)
        T_rr_double = sum(e["tau_a"] + e["tau_b"] for e in rr)
        print("   (V2) T_hr = %.9f   vs  4pi - 2 d tau = %.9f   diff %.2e"
              % (T_hr, 4 * math.pi - 2 * dcount * tau_hh, T_hr - (4 * math.pi - 2 * dcount * tau_hh)))
        print("        sum(2 tau over ring-ring) = %.9f  vs 14pi - A + 2 d tau = %.9f  diff %.2e"
              % (T_rr_double, 14 * math.pi - A + 2 * dcount * tau_hh,
                 T_rr_double - (14 * math.pi - A + 2 * dcount * tau_hh)))
        # area decomposition of the envelope slack
        caps = 0.0; truecap = 0.0
        for i in bnd:
            inf = info[i]
            b = 2 * math.asin(min(1.0, r * math.sin(inf["alpha"] / 2)))
            caps += (b - math.sin(b)) / 2 + 0.5 * r * r * math.sin(inf["alpha"])
            truecap += (inf["beta"] - math.sin(inf["beta"])) / 2 + 0.5 * inf["d1"] * inf["d2"] * math.sin(inf["alpha"])
        tri_rr_env = 2 * sum(0.5 * r * r * math.sin(e["tau_a"]) for e in rr)
        tri_rr_true = sum(e["tri_a"] + e["tri_b"] for e in rr)
        tri_hr_env = 2 * sum(0.5 * r * r * math.sin(e["tau_a"]) for e in hr)
        tri_hr_true = sum(e["tri_a"] + e["tri_b"] for e in hr)
        tri_hh_env = 2 * sum(0.5 * r * r * math.sin(e["tau_a"]) for e in hh)
        tri_hh_true = sum(e["tri_a"] + e["tri_b"] for e in hh)
        hubenv = sum(0.5 * r * r * len([1 for e in edges if e["a"] == i or e["b"] == i]) * math.sin(2 * math.pi / len([1 for e in edges if e["a"] == i or e["b"] == i])) for i in hub)
        hubtrue = sum(HubArea.values())
        print("   (V4) area decomposition (true / envelope / slack):")
        print("        arc caps + arc triangles : %.6f / %.6f / %+.6f" % (truecap, caps, caps - truecap))
        print("        ring-ring edge triangles : %.6f / %.6f / %+.6f" % (tri_rr_true, tri_rr_env, tri_rr_env - tri_rr_true))
        print("        hub-ring edge triangles  : %.6f / %.6f / %+.6f" % (tri_hr_true, tri_hr_env, tri_hr_env - tri_hr_true))
        print("        hub-hub edge triangles   : %.6f / %.6f / %+.6f" % (tri_hh_true, tri_hh_env, tri_hh_env - tri_hh_true))
        print("        hub cells (polygon UB)   : %.6f / %.6f / %+.6f" % (hubtrue, hubenv, hubenv - hubtrue))
        tot_true = truecap + tri_rr_true + tri_hr_true + tri_hh_true + hubtrue
        tot_env = caps + tri_rr_env + tri_hr_env + tri_hh_env + hubenv
        print("        TOTAL                    : %.6f / %.6f / %+.6f   (pi = %.6f)"
              % (tot_true, tot_env, tot_env - tot_true, math.pi))
