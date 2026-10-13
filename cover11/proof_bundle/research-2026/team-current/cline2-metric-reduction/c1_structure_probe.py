"""C1: exact-structure probe of the saved certified upper candidate (n11).

Goal: read the 22 integer-scaled centers, rebuild the refined nearest-site
structure (face circumcenters, boundary switches, Voronoi vertices), and
record the exact incidence data that our lower-dimensional representation
will have to reproduce. Numeric calibration only; no exclusion claimed.
"""
import json, math, cmath, sys
from pathlib import Path

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent            # workspace root
CAND = ROOT / "n11" / "upper" / "certified_object.json"
OUT = HERE / "out"

pi = math.pi
D = 10**17


def load_candidate():
    txt = CAND.read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    sc = j["centers_scaled_1e17"]
    pts = [(int(a) / D, int(b) / D) for a, b in sc]
    return j, pts


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def circumcenter(p, q, r):
    ax, ay = p; bx, by = q; cx, cy = r
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(d) < 1e-300:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy)


def main():
    j, pts = load_candidate()
    n = len(pts)
    R = math.sqrt(max(sum(p[i] ** 2 for i in range(2)) for p in pts))
    print("n =", n, " R(candidate) =", R)

    # nearest site radius function
    def rad(p):
        return min(dist(p, c) for c in pts)

    # Delaunay triangles from the saved graph listing (q0 no-ear k=4 graph)
    graphs = json.loads((ROOT / "research-2026" / "team-current" / "lead" / "q0_graphs.json").read_text())
    rep = {}
    for row in graphs:
        k = row["span"]
        degs = sorted((sum(1 for e in row["edges"] if e[0] == h or e[1] == h) for h in (9, 10)), reverse=True)
        rep[k] = (row, degs)

    cand_pts0 = sorted(range(n), key=lambda i: math.hypot(*pts[i]), reverse=True)
    print("radii sorted desc (idx, |c|):", [(i, round(math.hypot(*pts[i]), 9)) for i in cand_pts0])

    for k, (row, degs) in sorted(rep.items()):
        faces = [tuple(f) for f in row["faces"]]
        print(f"\n=== q0 graph span k={k}  hub degrees {degs} ===")
        rads = []
        ccs = []
        ok_trivial = True
        for f in faces:
            cc = circumcenter(pts[f[0]], pts[f[1]], pts[f[2]])
            ccs.append(cc)
            rr = rad(cc)
            rads.append(rr)
            if abs(rr - R) > 1e-14:
                ok_trivial = False
        print("  face circumradii: max=", max(rads), " min=", min(rads),
              " all==R within 1e-14:", ok_trivial)

    # --- calibrated structure: use Delaunay triangulation computed directly ---
    # scipy Delaunay of the 11 centers restricted to conv hull of centers,
    # then check which triangles' circumcenters are nearest-site vertices.
    from scipy.spatial import Delaunay
    tri = Delaunay([(p[0], p[1]) for p in pts])
    print("\n=== scipy Delaunay simplices (calibrated) ===")
    kept = []
    for s in tri.simplices:
        cc = circumcenter(*[pts[i] for i in s])
        rr = rad(cc)
        if abs(rr - R) < 1e-12:
            kept.append((tuple(sorted(s)), cc, rr))
    for s, cc, rr in kept:
        print("  ", s, " cc=", (round(cc[0], 9), round(cc[1], 9)), " rad-R=", rr - R)
    print("  #kept =", len(kept), " #simplices =", len(tri.simplices))

    # --- boundary switches: intersection of bisector of consecutive hull ring
    #     sites with the unit circle.
    hull_points = tri.convex_hull  # indices of hull vertices
    hull_idx = sorted(set(hull_points.ravel()))
    print("\n=== convex hull vertices (ring sites) ===", hull_idx)
    angles = {i: math.atan2(pts[i][1], pts[i][0]) for i in hull_idx}
    order = sorted(hull_idx, key=lambda i: angles[i])
    print("  angular order:", order)

    def bisector_unit_intersect(i, j):
        """Return the two intersection points of the bisector of (i,j) with S^1."""
        mx = (pts[i][0] + pts[j][0]) / 2
        my = (pts[i][1] + pts[j][1]) / 2
        dx = pts[j][0] - pts[i][0]
        dy = pts[j][1] - pts[i][1]
        # bisector: (x-mx)*dx + (y-my)*dy = 0  =>  dx*x + dy*y = dx*mx + dy*my
        c0 = dx * mx + dy * my
        nrm2 = dx * dx + dy * dy
        # param: closest point to origin on line
        t = c0 / nrm2
        fx, fy = dx * t, dy * t
        # distance from origin to line
        h = math.hypot(fx, fy)
        if h > 1:
            return []
        # direction along line
        ux, uy = -dy / math.sqrt(nrm2), dx / math.sqrt(nrm2)
        s = math.sqrt(max(0.0, 1 - h * h))
        return [(fx + s * ux, fy + s * uy), (fx - s * ux, fy - s * uy)]

    switches = []
    m = len(order)
    for a in range(m):
        i, j2 = order[a], order[(a + 1) % m]
        cands = bisector_unit_intersect(i, j2)
        # keep the switch that lies on the arc between the two sites (i.e. between
        # the two site directions) and is a nearest-site point for both
        ai, aj = angles[i], angles[j2]
        best = None
        for p in cands:
            tp = math.atan2(p[1], p[0])
            # signed angular gap test
            def gap(x, y):
                d = (y - x) % (2 * pi)
                return d
            if gap(ai, tp) < gap(ai, aj) and gap(tp, aj) < gap(ai, aj):
                if abs(rad(p) - R) < 1e-9:
                    best = p
        switches.append((i, j2, best))
    print("\n=== boundary switches (site pair, point, radius) ===")
    for i, j2, p in switches:
        if p is None:
            print(f"  ({i},{j2}): NO valid unit-circle switch")
        else:
            print(f"  ({i},{j2}): ({p[0]:.15f},{p[1]:.15f}) r={rad(p):.15f} dR={rad(p)-R:+.3e}")

    res = {
        "R": R,
        "radii": {int(i): math.hypot(*pts[i]) for i in range(n)},
        "kept_triangles": [{"simplex": list(s), "cc": list(cc), "rad_minus_R": rr - R} for s, cc, rr in kept],
        "switches": [{"pair": [int(i), int(j2)],
                      "point": None if p is None else list(p),
                      "rad": None if p is None else rad(p)} for i, j2, p in switches],
    }
    OUT.mkdir(exist_ok=True)
    (OUT / "c1_structure_probe.json").write_text(json.dumps(res, indent=2))
    print("\nwrote", OUT / "c1_structure_probe.json")


if __name__ == "__main__":
    main()
