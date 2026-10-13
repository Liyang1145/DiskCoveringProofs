"""C6: combinatorial core of the candidate (what any reduction must reproduce).

Prints, for the certified candidate:
  * boundary arc ownership: which site owns which unit-circle arc;
  * the cyclic sequence of tight points around the disk;
  * site->tight-point incidence;
  * per-site cell structure (number of Voronoi facets, degree).
All data from the exact integer literals.
"""
import json, math
from pathlib import Path
import numpy as np

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
    R = 0.37998385311983884

    # --- dense boundary scan: owner of each unit-circle point
    th = np.linspace(0, 2 * pi, 720001)
    circ = np.stack([np.cos(th), np.sin(th)], 1)
    dd = np.hypot(circ[:, 0:1] - P[None, :, 0], circ[:, 1:2] - P[None, :, 1])
    own = np.argmin(dd, 1)
    order = np.argsort(np.arctan2(P[:, 1], P[:, 0]))
    print("sites sorted by angle:", order.tolist())
    print("\n=== boundary arc ownership (cyclic runs) ===")
    runs = []
    start = 0
    for k in range(1, len(own)):
        if own[k] != own[start]:
            runs.append((own[start], th[start], th[k - 1]))
            start = k
    runs.append((own[start], th[start], th[-1]))
    # merge wrap
    if len(runs) > 1 and runs[0][0] == runs[-1][0]:
        s, a, b = runs.pop(0)
        runs[-1] = (runs[-1][0], runs[-1][1], b)
    tot = 0.0
    for site, a, b in runs:
        w = b - a
        tot += w
        print(f"  site {site:2d}: theta in [{a:+.9f},{b:+.9f}]  width={w:.9f}  chord={2*math.sin(w/2):.9f}")
    print("  total covered angle =", tot, " (=2pi within sampling error)")

    # --- tight points cyclic order
    tight = json.loads((OUT / "c5_tight.json").read_text())
    pts = []
    for e in tight["vor_tight"]:
        pts.append(("V", np.array(e["p"]), e["sites"], e["r"]))
    for e in tight["switch_tight"]:
        pts.append(("S", np.array(e["p"]), e["sites"], e["r"]))
    pts.sort(key=lambda t: math.atan2(t[1][1], t[1][0]))
    print(f"\n=== tight points in cyclic order ({len(pts)} of them) ===")
    for kind, p, sites, r in pts:
        print(f"  {kind} theta={math.atan2(p[1],p[0]):+.9f} |p|={np.hypot(*p):.9f} sites={sites} r={r:.12f}")

    # --- per-site incidence among tight points
    print("\n=== tight-point incidence per site ===")
    for i in range(n):
        inc = [(k, kind) for k, (kind, p, sites, r) in enumerate(pts) if i in sites]
        print(f"  site {i:2d} |c|={np.hypot(*P[i]):.9f}: {[(k, kind) for k, kind in inc]}")

    # --- Voronoi degrees (number of distinct facets)
    from scipy.spatial import Voronoi
    vor = Voronoi(P)
    deg = {i: 0 for i in range(n)}
    for (a, b) in vor.ridge_points:
        deg[int(a)] += 1
        deg[int(b)] += 1
    print("\n=== Voronoi neighbour counts ===")
    for i in range(n):
        nbrs = sorted(int(b) if int(a) == i else int(a) for a, b in vor.ridge_points if i in (int(a), int(b)))
        print(f"  site {i:2d}: deg={deg[i]} nbrs={nbrs}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c6_core.json").write_text(json.dumps({
        "arc_runs": [{"site": int(s), "t0": a, "t1": b} for s, a, b in runs],
        "tight_cyclic": [{"kind": k, "p": p.tolist(), "sites": s, "r": r} for k, p, s, r in pts],
        "vor_deg": {str(k): v for k, v in deg.items()},
    }, indent=2))
    print("\nwrote", OUT / "c6_core.json")


if __name__ == "__main__":
    main()
