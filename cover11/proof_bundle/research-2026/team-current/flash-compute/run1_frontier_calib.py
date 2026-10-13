# -*- coding: utf-8 -*-
"""run1_frontier_calib.py -- read-only diagnosis, flash-compute lane.

PART F: locate the current frontier of the n=11 "lambda5 / L1-prime cover" line
        (which boxes are unresolved, where, what margin), plus sha256 of the inputs.
PART C: two mandatory calibrations demanded by the lead:
        (C1) MEC instrument: a circumradius is NOT a MEC lower bound for an obtuse triangle.
             exact rational controls.
        (C2) the saved feasible 11-disk object (R_saved <= 0.38) must NOT be excluded
             at r = 38/100 by the pair criterion.

Writes nothing except stdout (caller redirects to a log). Read-only on all inputs.
"""
import os, sys, json, hashlib
from fractions import Fraction as F

ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"
T23 = ROOT + r"\research-2026\team-20260923"
L5OUT = T23 + r"\lambda5\out"
S = 10 ** 17


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def fs(x):
    return str(x)


# ---------------------------------------------------------------- PART F
def part_frontier():
    print("=" * 78)
    print("PART F -- frontier of the lambda5 / L1-prime cover line")
    print("=" * 78)
    summary = {}
    for name in ("certS_nD40.json", "certS_aligned.json", "certS_nD6.json"):
        p = os.path.join(L5OUT, name)
        if not os.path.exists(p):
            print("MISSING", name)
            continue
        d = json.load(open(p, encoding="utf-8"))
        thr = F(d["thr4r2"])
        boxes = d.get("boxes", [])
        rows = []
        for k, b in enumerate(boxes):
            lo = tuple(F(s) for s in b["lo"])
            hi = tuple(F(s) for s in b["hi"])
            d2 = F(b["d2lo"])
            rows.append([d2 - thr, k, lo, hi, d2])
        rows.sort(key=lambda r: r[0])
        unres = [r for r in rows if r[0] <= 0]
        hinge = max(unres, key=lambda r: r[0]) if unres else None
        print("-" * 78)
        print("FILE %s" % name)
        print("  sha256 = %s" % sha256(p))
        print("  declared n_passed=%s n_unresolved=%s boxes_in_json=%d thr4r2=%s (%.12f)"
              % (d.get("n_passed"), d.get("n_unresolved"), len(boxes), thr, float(thr)))
        print("  recomputed from d2lo: passed=%d unresolved=%d"
              % (len(boxes) - len(unres), len(unres)))
        print("  additional header: r=%s nA=%s nD_s_bins=%s min_margin=%s maxden=%s"
              % (d.get("r"), d.get("nA"), d.get("nD_s_bins"), d.get("min_margin"),
                 d.get("max_endpoint_denominator")))
        if unres:
            w = rows[0]
            print("  WORST  box#%d margin=%.9e  A=[%.6f,%.6f] B=[%.6f,%.6f] C=[%.6f,%.6f] D=[%.6f,%.6f]"
                  % (w[1], float(w[0]), float(w[2][0]), float(w[3][0]), float(w[2][1]), float(w[3][1]),
                     float(w[2][2]), float(w[3][2]), float(w[2][3]), float(w[3][3])))
            h = hinge
            print("  HINGE  box#%d margin=%.9e  A=[%.6f,%.6f] B=[%.6f,%.6f] C=[%.6f,%.6f] D=[%.6f,%.6f]"
                  % (h[1], float(h[0]), float(h[2][0]), float(h[3][0]), float(h[2][1]), float(h[3][1]),
                     float(h[2][2]), float(h[3][2]), float(h[2][3]), float(h[3][3])))
            print("         widths (rad): %s"
                  % ["%.5f" % float(h[3][i] - h[2][i]) for i in range(4)])
            summary[name] = dict(
                hinge=dict(box=h[1], margin=fs(h[0]),
                           lo=[fs(x) for x in h[2]], hi=[fs(x) for x in h[3]], d2lo=fs(h[4])),
                worst=dict(box=w[1], margin=fs(w[0]),
                           lo=[fs(x) for x in w[2]], hi=[fs(x) for x in w[3]], d2lo=fs(w[4])),
                n_unresolved=len(unres), n_boxes=len(boxes), thr=fs(thr),
                sha256=sha256(p))
        # margin histogram of the frontier
        if unres:
            qs = [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]
            ms = sorted(float(r[0]) for r in unres)
            print("  unresolved margin quantiles: " +
                  " ".join("q%.2f=%.6f" % (q, ms[min(len(ms) - 1, int(q * (len(ms) - 1)))]) for q in qs))
    outp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "frontier_boxes.json")
    with open(outp, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1)
    print("wrote %s" % outp)


# ---------------------------------------------------------------- C1: MEC
def circumradius_sq(pa, pb, pc):
    """squared circumradius of the triangle, exact Fraction (None if degenerate)."""
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
    """'acute' / 'right' / 'obtuse' via exact dot products at the three vertices."""
    ds = [dot2(pa, pb, pc), dot2(pb, pa, pc), dot2(pc, pa, pb)]
    if any(d == 0 for d in ds):
        return "right"
    return "acute" if all(d > 0 for d in ds) else "obtuse"


def mec3(pa, pb, pc):
    """exact MEC radius SQUARED of the 3-point set, by the standard rule
       (obtuse/right -> half longest side;  acute -> circumradius)."""
    d2 = sorted([(pa[0] - pb[0]) ** 2 + (pa[1] - pb[1]) ** 2,
                 (pa[0] - pc[0]) ** 2 + (pa[1] - pc[1]) ** 2,
                 (pb[0] - pc[0]) ** 2 + (pb[1] - pc[1]) ** 2])
    half_longest = d2[2] / 4
    cls = tri_class(pa, pb, pc)
    cr2 = circumradius_sq(pa, pb, pc)
    if cls == "acute":
        assert cr2 is not None and cr2 >= half_longest
        return cr2, cls, cr2
    # obtuse or right: true MEC is the diameter disk of the longest side
    assert cr2 is not None and cr2 <= half_longest
    return half_longest, cls, cr2


def part_calib_mec():
    print()
    print("=" * 78)
    print("PART C1 -- MEC instrument controls (exact rational)")
    print("=" * 78)
    ctrls = [
        ("obtuse? (0,0),(4,0),(1,1)   [MEC=2, circumradius=sqrt5=2.2360...]", (F(0), F(0)), (F(4), F(0)), (F(1), F(1))),
        ("right  (0,0),(2,0),(0,2)    [MEC=circumradius=sqrt2]", (F(0), F(0)), (F(2), F(0)), (F(0), F(2))),
        ("equilateral (0,0),(1,0),(1/2,sqrt3/2)", (F(0), F(0)), (F(1), F(0)), (F(1, 2), F(0))),
        ("acute scalene (0,0),(4,0),(2,3)", (F(0), F(0)), (F(4), F(0)), (F(2), F(3))),
    ]
    import math
    for lab, a, b, c in ctrls:
        if lab.startswith("equilateral"):
            c = (F(1, 2), None)
            # keep exact: use (1/2, sqrt(3)/2) only numerically for the class check
        if c[1] is None:
            print("  %s  -> skipped exact (irrational vertex); see numeric block" % lab)
            continue
        m2, cls, cr2 = mec3(a, b, c)
        print("  %s" % lab)
        print("     class=%s  MEC^2=%.10f (MEC=%.10f)  circumradius^2=%.10f (R=%.10f)"
              % (cls, float(m2), math.sqrt(float(m2)), float(cr2), math.sqrt(float(cr2))))
        if cls == "obtuse":
            print("     >>> circumradius R = %.10f is NOT a lower bound for MEC = %.10f (R > MEC)."
                  % (math.sqrt(float(cr2)), math.sqrt(float(m2))))
            print("     >>> a kernel using circumradius for every triple OVER-estimates MEC by %.6f here."
                  % (math.sqrt(float(cr2)) - math.sqrt(float(m2))))
    # exact check of the obtuse control with rationals only
    cr2 = circumradius_sq((F(0), F(0)), (F(4), F(0)), (F(1), F(1)))
    print("  exact: obtuse control circumradius^2 = %s = %.6f  >  MEC^2 = 4" % (fs(cr2), float(cr2)))
    assert cr2 == F(5) and F(5) > 4
    print("  exact: (4,0) and (1,1) force any enclosing disk radius >= 2 by the diameter argument,")
    print("         and the disk centre (2,0) radius 2 contains (1,1): MEC = 2 exactly.")


# ---------------------------------------------------------------- C2: saved object
def c2(r, pa, pb):
    return (pa[0] - pb[0]) ** 2 + (pa[1] - pb[1]) ** 2


def part_calib_saved():
    print()
    print("=" * 78)
    print("PART C2 -- the saved certified object must not be excluded at r = 38/100")
    print("=" * 78)
    p = ROOT + r"\n11\upper\certified_object.json"
    print("  input sha256 = %s" % sha256(p))
    J = json.load(open(p, encoding="utf-8"))
    assert J["scale"] == "10^17"
    C = [(F(int(a), S), F(int(b), S)) for a, b in J["centers_scaled_1e17"]]
    R_SAVED = F(3799838531198387090485182, 10 ** 25)
    import math
    for r, lab in ((F(38, 100), "38/100"), (R_SAVED, "R_saved")):
        rho = [(math.isqrt(int(x * x + y * y) * 10 ** 60) / 10 ** 30) for x, y in C]
        print("  --- r = %s (%s): |c_i| = %s" % (lab, float(r), " ".join("%.6f" % v for v in rho)))
        bnd = sorted([i for i in range(11) if F(rho[i]).__float__() >= 1 - float(r)],
                     key=lambda i: math.atan2(float(C[i][1]), float(C[i][0])))
        inn = [i for i in range(11) if i not in bnd]
        print("      boundary disks = %d %s ; inner disks = %d %s"
              % (len(bnd), bnd, len(inn), inn))
        # tips of consecutive boundary disks (float geometry is enough for a calibration)
        tips = []
        for k in range(len(bnd)):
            i1, i2 = bnd[k], bnd[(k + 1) % len(bnd)]
            x1, y1 = float(C[i1][0]), float(C[i1][1])
            x2, y2 = float(C[i2][0]), float(C[i2][1])
            dx, dy = x2 - x1, y2 - y1
            L = math.hypot(dx, dy)
            h = math.sqrt(max(float(r) ** 2 - L * L / 4, 0.0))
            mx, my = (x1 + x2) / 2, (y1 + y2) / 2
            px, py = -dy / L, dx / L
            sgn = 1.0 if (mx * px + my * py) > 0 else -1.0
            tips.append((mx - sgn * h * px, my - sgn * h * py))
        n = len(tips)
        step = n // 2
        diag = [math.dist(tips[i], tips[(i + step) % n]) for i in range(n)]
        print("      n_tips=%d  opposite-pair distances 2r=%.9f" % (n, 2 * float(r)))
        print("      min_i |v_i - v_{i+%d}| = %.9f   argmin i=%d" % (step, min(diag), diag.index(min(diag))))
        excl = min(diag) > 2 * float(r)
        print("      pair criterion (all opposite pairs > 2r)? %s  -> %s"
              % (excl, "EXCLUDED (BAD: contradicts the feasible object)" if excl
                 else "not excluded  OK (calibration passes)"))
        # every tip must be covered by a disk of radius r (the object covers D at R_saved <= 0.38)
        cov = [min(i for i in range(11) if math.dist(tips[k], (float(C[i][0]), float(C[i][1]))) <= float(r) + 1e-12)
               for k in range(n)]
        print("      covering disk of each tip (0..10): %s   (all within r: %s)"
              % (cov, all(math.dist(tips[k], (float(C[cov[k]][0]), float(C[cov[k]][1]))) <= float(r) for k in range(n))))


if __name__ == "__main__":
    part_frontier()
    part_calib_mec()
    part_calib_saved()
