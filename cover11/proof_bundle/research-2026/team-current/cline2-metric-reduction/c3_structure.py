"""C3: correct structural probe.  The covering radius of the 11-disk cover is

    R(C) = max over sites i of max_{x in cell(i) cap D} |x - c_i|

sum of cell-local maxima.  We compute it by clipping each Voronoi cell with the
unit disk (Sutherland-Hodgman) and sampling the clipped polygon plus its
boundary edges densely, then also using Voronoi vertices inside D.
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


def clip_disk(poly):
    """Sutherland-Hodgman clip of convex polygon against |x|<=1."""
    def inside(p):
        return p @ p <= 1.0
    def inter(a, b):
        # solve |a + t(b-a)|^2 = 1
        d = b - a
        A = d @ d
        B = 2 * (a @ d)
        C = a @ a - 1.0
        disc = B * B - 4 * A * C
        t = (-B + math.sqrt(max(disc, 0.0))) / (2 * A) if A != 0 else 0.0
        t = min(max(t, 0.0), 1.0)
        return a + t * d
    out = []
    m = len(poly)
    for k in range(m):
        a, b = poly[k], poly[(k + 1) % m]
        ia, ib = inside(a), inside(b)
        if ia:
            out.append(a)
            if not ib:
                out.append(inter(a, b))
        elif ib:
            out.append(inter(a, b))
    return np.array(out)


def main():
    P = load()
    n = len(P)
    rho = np.hypot(P[:, 0], P[:, 1])
    vor = Voronoi(P)
    R = 0.0
    cellmax = np.zeros(n)
    tight = []          # (radius, point, sites)
    for i, reg in enumerate(vor.regions):
        if not reg or -1 in reg:
            continue
        poly = vor.vertices[reg]
        cl = clip_disk(poly)
        if len(cl) < 3:
            continue
        # sample polygon interior + boundary
        for a in range(len(cl)):
            b = cl[(a + 1) % len(cl)]
            for t in np.linspace(0, 1, 401):
                x = a + t * (b - a)
                cellmax[i] = max(cellmax[i], np.hypot(*(x - P[i])))
        # fan samples
        for a in range(1, len(cl) - 1):
            for s in np.linspace(0, 1, 41):
                for u in np.linspace(0, 1 - s, 41):
                    x = s * cl[a] + u * cl[a + 1] + (1 - s - u) * cl[0]
                    cellmax[i] = max(cellmax[i], np.hypot(*(x - P[i])))
    R = cellmax.max()
    print("per-site cell max:", np.round(cellmax, 12).tolist())
    print("R(C) =", R)

    # tight points: Voronoi vertices inside the disk
    print("\n=== Voronoi vertices with min-site distance >= R - 1e-12 ===")
    for v in vor.vertices:
        if v @ v > 1.0:
            continue
        dd = np.hypot(*(P - v[None, :]).T)
        r = dd.min()
        if r >= R - 1e-12:
            sites = [int(k) for k in range(n) if abs(dd[k] - r) < 1e-9]
            print(f"  v=({v[0]:+.12f},{v[1]:+.12f}) |v|={np.hypot(*v):.9f} r={r:.12f} deg={len(sites)} sites={sites}")

    # boundary tight points: scan the unit circle
    print("\n=== boundary arcs (unit circle) where nearest distance >= R - 1e-12 ===")
    th = np.linspace(0, 2 * pi, 2000001)
    circ = np.stack([np.cos(th), np.sin(th)], 1)
    dm = np.min(np.hypot(circ[:, 0:1] - P[None, :, 0], circ[:, 1:2] - P[None, :, 1]), axis=1)
    arg = np.argmax(dm)
    print("  max over circle of nearest-site distance =", dm.max(), "at theta=", th[arg])
    idx = np.where(dm >= R - 1e-12)[0]
    # group into arcs
    def group(idx):
        arcs = []
        if len(idx) == 0:
            return arcs
        s = idx[0]; prev = idx[0]
        for k in idx[1:]:
            if k != prev + 1:
                arcs.append((s, prev)); s = k
            prev = k
        arcs.append((s, prev))
        return arcs
    for a, b in group(idx):
        tm = (th[a] + th[b]) / 2
        p = np.array([math.cos(tm), math.sin(tm)])
        d = np.hypot(*(P - p[None, :]).T)
        print(f"  arc theta in [{th[a]:.9f},{th[b]:.9f}] mid={tm:.9f} nearest r={d.min():.12f} sites={[int(k) for k in range(n) if abs(d[k]-d.min())<1e-9]}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c3_structure.json").write_text(json.dumps({
        "R": R, "cellmax": cellmax.tolist(), "site_radii": rho.tolist(),
        "vor_vertices": vor.vertices.tolist(), "vor_ridge_points": vor.ridge_points.tolist(),
    }, indent=2))
    print("\nwrote", OUT / "c3_structure.json")


if __name__ == "__main__":
    main()
