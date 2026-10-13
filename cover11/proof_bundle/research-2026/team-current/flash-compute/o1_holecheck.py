# -*- coding: utf-8 -*-
"""o1_holecheck.py -- is the O1-negative ledger extendable to a genuine 11-disk cover?

If D \\ (union of the nine ring disks) can be covered by two disks of radius r, then the
ledger is a genuine 9+2 cover and the O1-based criterion (which rejects it) is UNSOUND.
Method: polar grid hole extraction, then a two-centre covering test (grid + local refine,
minimal enclosing circle of the residual by Welzl).  Numeric only.
"""
import json, math, os, random
import numpy as np

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
R = 0.38


def rho(t):
    return math.cos(t) - math.sqrt(max(R * R - math.sin(t) ** 2, 0.0))


def load(tag):
    p = os.path.join(OUT, "o1_counterexample_%s.json" % tag)
    d = json.load(open(p, encoding="utf-8"))
    return d


def welzl(P):
    """minimal enclosing circle, O(n) expected (iterative Welzl)."""
    random.seed(12345)
    P = [(float(x), float(y)) for x, y in P]
    random.shuffle(P)

    def circle2(a, b):
        c = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
        return (c, math.dist(a, b) / 2)

    def circle3(a, b, c):
        ax, ay = a; bx, by = b; cx, cy = c
        d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if abs(d) < 1e-18:
            return None
        ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
        uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
        return ((ux, uy), math.hypot(ax - ux, ay - uy))

    def inside(C, p):
        return math.dist(C[0], p) <= C[1] + 1e-12

    C = (P[0], 0.0)
    for i, p in enumerate(P):
        if not inside(C, p):
            C = (p, 0.0)
            for j in range(i):
                q = P[j]
                if not inside(C, q):
                    C = circle2(p, q)
                    for k in range(j):
                        s = P[k]
                        if not inside(C, s):
                            c3 = circle3(p, q, s)
                            C = c3 if c3 else C
    return C


def main():
    for tag in ("scan-min", "worst-opt"):
        d = load(tag)
        t = d["t"]; psi = d["psi"]
        C = [(rho(t[k]) * math.cos(psi[k]), rho(t[k]) * math.sin(psi[k])) for k in range(9)]
        # hole on a polar grid
        NR, NT = 260, 1440
        hole = []
        for i in range(NR):
            rr = (i + 0.5) / NR
            for j in range(NT):
                th = 2 * math.pi * (j + 0.5) / NT
                x, y = rr * math.cos(th), rr * math.sin(th)
                cov = False
                for c in C:
                    if (x - c[0]) ** 2 + (y - c[1]) ** 2 <= R * R:
                        cov = True
                        break
                if not cov:
                    hole.append((x, y))
        print("=" * 78)
        print("ledger %s : %d ring disks ; hole grid points = %d of %d" % (tag, 9, len(hole), NR * NT))
        if not hole:
            print("  hole empty -> the nine ring disks already cover D (no hubs needed)")
            continue
        hx = np.array([p[0] for p in hole]); hy = np.array([p[1] for p in hole])
        print("  hole radius range: %.6f .. %.6f ; angular spread %.1f deg"
              % (min(np.hypot(hx, hy)), max(np.hypot(hx, hy)),
                 np.degrees(np.ptp(np.unwrap(np.sort(np.arctan2(hy, hx)))))))
        # two-centre cover: coarse grid for h1, MEC of residual, then refine
        best = None
        for i in range(26):
            for j in range(26):
                h1 = ((i + 0.5) / 26 * 1.6 - 0.8, (j + 0.5) / 26 * 1.6 - 0.8)
                if math.hypot(*h1) > 1:
                    continue
                dx = hx - h1[0]; dy = hy - h1[1]
                m = dx * dx + dy * dy > R * R
                if not m.any():
                    best = (0.0, h1, None)
                    break
                res = list(zip(hx[m], hy[m]))
                if len(res) > 4000:
                    idx = np.linspace(0, len(res) - 1, 4000).astype(int)
                    res = [res[k] for k in idx]
                cc, rad = welzl(res)
                if best is None or rad < best[0]:
                    best = (rad, h1, cc)
            if best is not None and best[0] == 0.0:
                break
        # local refine
        step = 0.05
        for _ in range(40):
            improved = False
            for ddx in (-step, 0, step):
                for ddy in (-step, 0, step):
                    h1 = (best[1][0] + ddx, best[1][1] + ddy)
                    if math.hypot(*h1) > 1:
                        continue
                    dx = hx - h1[0]; dy = hy - h1[1]
                    m = dx * dx + dy * dy > R * R
                    if not m.any():
                        best = (0.0, h1, None); improved = False; break
                    res = list(zip(hx[m], hy[m]))
                    if len(res) > 4000:
                        idx = np.linspace(0, len(res) - 1, 4000).astype(int)
                        res = [res[k] for k in idx]
                    cc, rad = welzl(res)
                    if rad < best[0] - 1e-12:
                        best = (rad, h1, cc); improved = True
                if not (best[0] > 0):
                    break
            if not improved:
                step *= 0.5
                if step < 1e-5:
                    break
        print("  best two-centre cover of the hole: h1=(%.6f,%.6f)  residual MEC radius = %.6f  vs r = %.6f"
              % (best[1][0], best[1][1], best[0], R))
        if best[2] and best[0] <= R:
            print("  => the hole IS coverable by two radius-r disks -> genuine 9+2 cover exists")
            print("     (h2 = (%.6f, %.6f))  with margin r - MEC = %+.3e" % (best[2][0], best[2][1], R - best[0]))
        else:
            print("  => the hole is NOT coverable by two radius-r disks in this grid search")
            print("     (residual MEC exceeds r by %+.3e; grid resolution 1/260 radial)" % (best[0] - R))
        out = dict(tag=tag, hole_points=int(len(hole)), best_h1=list(best[1]),
                   residual_MEC=best[0], h2=list(best[2]) if best[2] else None, r=R)
        with open(os.path.join(OUT, "o1_holecheck_%s.json" % tag), "w", encoding="utf-8") as f:
            json.dump(out, f, indent=1)
        print("  wrote out/o1_holecheck_%s.json" % tag)


if __name__ == "__main__":
    main()
