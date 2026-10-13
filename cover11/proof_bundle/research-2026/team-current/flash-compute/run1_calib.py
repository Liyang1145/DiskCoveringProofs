# -*- coding: utf-8 -*-
"""run1_calib.py -- two mandatory calibrations (read-only, numeric where stated).

C1  MEC instrument: a circumradius is NOT a lower bound for the MEC of an obtuse
    triangle.  Exact rational controls, plus the correct 3-point rule.
C2  The saved certified 11-disk object (R_saved <= 0.38) must NOT be excluded at
    r = 38/100 by the opposite-pair criterion used on the lambda5/L1-prime line.

Writes nothing except stdout.
"""
import os, sys, json, hashlib, math
from fractions import Fraction as F

ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"
S = 10 ** 17


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ------------------------------------------------------------------ C1
def circumradius_sq(pa, pb, pc):
    ax, ay = pa; bx, by = pb; cx, cy = pc
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if d == 0:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) +
          (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) +
          (cx * cx + cy * cy) * (bx - ax)) / d
    return (ax - ux) ** 2 + (ay - uy) ** 2


def dot2(o, p, q):
    return (p[0] - o[0]) * (q[0] - o[0]) + (p[1] - o[1]) * (q[1] - o[1])


def tri_class(pa, pb, pc):
    ds = [dot2(pa, pb, pc), dot2(pb, pa, pc), dot2(pc, pa, pb)]
    if any(d == 0 for d in ds):
        return "right"
    return "acute" if all(d > 0 for d in ds) else "obtuse"


def mec3(pa, pb, pc):
    d2 = sorted([(pa[0] - pb[0]) ** 2 + (pa[1] - pb[1]) ** 2,
                 (pa[0] - pc[0]) ** 2 + (pa[1] - pc[1]) ** 2,
                 (pb[0] - pc[0]) ** 2 + (pb[1] - pc[1]) ** 2])
    half_longest = d2[2] / 4
    cls = tri_class(pa, pb, pc)
    cr2 = circumradius_sq(pa, pb, pc)
    if cls == "acute":
        return cr2, cls, cr2
    return half_longest, cls, cr2


def part_c1():
    print("=" * 74)
    print("C1 -- MEC instrument controls (exact rational)")
    print("=" * 74)
    ctrls = [
        ("obtuse  (0,0),(4,0),(1,1)", (F(0), F(0)), (F(4), F(0)), (F(1), F(1))),
        ("right   (0,0),(2,0),(0,2)", (F(0), F(0)), (F(2), F(0)), (F(0), F(2))),
        ("acute   (0,0),(4,0),(2,3)", (F(0), F(0)), (F(4), F(0)), (F(2), F(3))),
        ("obtuse  (0,0),(4,0),(3,1/2)", (F(0), F(0)), (F(4), F(0)), (F(3), F(1, 2))),
    ]
    for lab, a, b, c in ctrls:
        m2, cls, cr2 = mec3(a, b, c)
        mM = math.sqrt(float(m2)); cM = math.sqrt(float(cr2))
        flag = "  <-- circumradius NOT a valid lower bound here" if cls == "obtuse" else ""
        print("  %-28s class=%-6s MEC=%.9f  circumradius=%.9f  gap=%.9f%s"
              % (lab, cls, mM, cM, cM - mM, flag))
    cr2 = circumradius_sq((F(0), F(0)), (F(4), F(0)), (F(1), F(1)))
    assert cr2 == F(5), cr2
    print("  exact: obtuse control circumradius^2 = 5 > MEC^2 = 4  (R=%.6f > MEC=2)"
          % math.sqrt(5))
    print("  correct rule: 3-point MEC^2 = max( half-longest-side^2 , circumradius^2 if acute )")
    print("  an instrument that drops the acute test OVER-bounds MEC and can wrongly exclude.")


# ------------------------------------------------------------------ C2
def part_c2():
    print()
    print("=" * 74)
    print("C2 -- saved certified 11-disk object must not be excluded at r = 38/100")
    print("=" * 74)
    p = ROOT + r"\n11\upper\certified_object.json"
    print("  input sha256 = %s" % sha256(p))
    J = json.load(open(p, encoding="utf-8"))
    C = [(F(int(a), S), F(int(b), S)) for a, b in J["centers_scaled_1e17"]]
    R_SAVED = F(3799838531198387090485182, 10 ** 25)
    for r, lab in ((F(38, 100), "38/100"), (R_SAVED, "R_saved")):
        rf = float(r)
        rho = [math.hypot(float(x), float(y)) for x, y in C]
        print("  --- r=%s (%.12f): |c_i| = %s"
              % (lab, rf, " ".join("%.6f" % v for v in rho)))
        bnd = sorted([i for i in range(11) if rho[i] >= 1 - rf],
                     key=lambda i: math.atan2(float(C[i][1]), float(C[i][0])))
        inn = [i for i in range(11) if i not in bnd]
        print("      boundary disks %d: %s ; interior disks %d: %s" % (len(bnd), bnd, len(inn), inn))
        tips = []
        for k in range(len(bnd)):
            i1, i2 = bnd[k], bnd[(k + 1) % len(bnd)]
            x1, y1 = float(C[i1][0]), float(C[i1][1])
            x2, y2 = float(C[i2][0]), float(C[i2][1])
            dx, dy = x2 - x1, y2 - y1
            L = math.hypot(dx, dy)
            hh = math.sqrt(max(rf ** 2 - L * L / 4, 0.0))
            mx, my = (x1 + x2) / 2, (y1 + y2) / 2
            px, py = -dy / L, dx / L
            sg = 1.0 if (mx * px + my * py) > 0 else -1.0
            tips.append((mx - sg * hh * px, my - sg * hh * py))
        n = len(tips)
        step = n // 2
        diag = [math.dist(tips[i], tips[(i + step) % n]) for i in range(n)]
        i0 = diag.index(min(diag))
        print("      n_tips=%d  opposite-pair distances ; 2r=%.9f" % (n, 2 * rf))
        print("      min_i |v_i - v_{i+%d}| = %.9f (i=%d)   max = %.9f"
              % (step, min(diag), i0, max(diag)))
        excl = min(diag) > 2 * rf
        print("      pair criterion all-opposite-pairs > 2r ? %s  =>  %s"
              % (excl, "EXCLUDED (contradiction -- BAD)" if excl else "not excluded (calibration OK)"))
        # the covering disks of the ring disks: disk k covers the two arcs next to its arc
        cov = []
        for k in range(n):
            best = min(range(11), key=lambda i: math.dist(tips[k], (float(C[i][0]), float(C[i][1]))))
            cov.append(best)
        print("      nearest center of each tip: %s" % cov)
        print("      all tips inside a radius-r disk: %s"
              % all(math.dist(tips[k], (float(C[cov[k]][0]), float(C[cov[k]][1]))) <= rf + 1e-12
                    for k in range(n)))
    print("  reading: at r=38/100 the saved object is a FEASIBLE n=11 cover (its radii")
    print("  R_saved=0.3799838531 <= 0.38), so any exclusion claim at r=38/100 that keeps")
    print("  it inside scope is unsound; the pair criterion correctly FAILS to exclude it.")


if __name__ == "__main__":
    part_c1()
    part_c2()
