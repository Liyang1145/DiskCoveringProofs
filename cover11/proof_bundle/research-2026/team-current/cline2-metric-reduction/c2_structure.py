"""C2: rebuild the true nearest-site structure of the saved certified candidate.

Deliberately avoids scipy's convex_hull attribute confusion: sites are
classified by their distance to the origin and by whether their Voronoi cell
touches |x| = 1. Everything is recomputed from the exact integer literals.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.spatial import Voronoi

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def main():
    P = load()
    n = len(P)
    rho = np.hypot(P[:, 0], P[:, 1])
    print("site radii:", np.round(rho, 9).tolist())

    # covering radius per site: max over its Voronoi cell (clipped to disk)
    vor = Voronoi(P)
    R = 0.0
    info = []
    for i, reg in enumerate(vor.regions):
        if not reg or -1 in reg:
            continue                       # unbounded -> dealt with separately
        poly = vor.vertices[reg]
        # sample the polygon densely; also candidate extreme points inside unit disk
        for k in range(len(poly)):
            a, b = poly[k], poly[(k + 1) % len(poly)]
            for t in np.linspace(0, 1, 201):
                x = a + t * (b - a)
                if x @ x <= 1.0:
                    d = np.hypot(*(x - P[i]))
                    if d > R:
                        R = d
        # interior extremes: Voronoi vertices inside the disk
        for x in poly:
            if x @ x <= 1.0:
                d = np.hypot(*(x - P[i]))
                if d > R:
                    R = d

    print("numeric covering radius (polygon sampling) R =", R)

    # all Voronoi vertices with radius >= 0.999*R
    print("\n=== Voronoi vertices with minimal site distance >= 0.999 R ===")
    for v in vor.vertices:
        dd = np.hypot(*(P - v[None, :]).T)
        j = int(np.argmin(dd))
        if dd[j] >= 0.999 * R:
            sites = [int(k) for k in range(n) if abs(dd[k] - dd[j]) < 1e-9]
            print(f"  v=({v[0]:+.12f},{v[1]:+.12f}) |v|={np.hypot(*v):.9f} r={dd[j]:.12f} deg={len(sites)} sites={sites}")

    # boundary switches: for each hull edge of the SITE set, find the farthest
    # point on the unit circle that is closest to those two sites.
    print("\n=== boundary switches (unit-circle farthest points) ===")
    # candidate switches: intersections of all bisectors with the unit circle
    sw = []
    for i in range(n):
        for j in range(i + 1, n):
            mx, my = (P[i] + P[j]) / 2
            dx, dy = P[j] - P[i]
            c0 = dx * mx + dy * my
            nn = dx * dx + dy * dy
            if nn == 0:
                continue
            t = c0 / nn
            fx, fy = dx * t, dy * t
            h = math.hypot(fx, fy)
            if h > 1:
                continue
            ux, uy = -dy / math.sqrt(nn), dx / math.sqrt(nn)
            s = math.sqrt(max(0.0, 1 - h * h))
            for sgn in (1, -1):
                p = np.array([fx + sgn * s * ux, fy + sgn * s * uy])
                d = np.hypot(*(P - p[None, :]).T)
                r = d.min()
                if r >= 0.999 * R:
                    sw.append((float(r), tuple(np.round(p, 15)), [int(k) for k in range(n) if abs(d[k] - r) < 1e-9]))
    sw.sort(reverse=True)
    for r, p, sites in sw:
        print(f"  p=({p[0]:+.12f},{p[1]:+.12f}) r={r:.12f} sites={sites}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c2_structure.json").write_text(json.dumps({
        "R_numeric": R,
        "site_radii": rho.tolist(),
        "high_vertices": [{"v": v.tolist(),
                           "r": float(np.hypot(*(P - v[None, :]).T).min()),
                           "sites": [int(k) for k in range(n) if abs(np.hypot(*(P - v[None, :]).T)[k] - np.hypot(*(P - v[None, :]).T).min()) < 1e-9]}
                          for v in vor.vertices],
        "switches": [{"p": p, "r": r, "sites": s} for r, p, s in sw],
    }, indent=2))


if __name__ == "__main__":
    main()
