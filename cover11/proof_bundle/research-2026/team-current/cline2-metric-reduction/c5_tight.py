"""C5: enumerate the exact tight set of the candidate.

Critical-point list for a fixed nearest-site type:
  * Voronoi vertices inside D  (>=3 sites at equal distance)
  * boundary switches on |x| = 1 (>=2 sites at equal distance; local max of the
    circle restriction of the nearest-site distance)
For each we record the (sorted) nearest-site set, the common radius, and
whether the common radius equals R(C) = 0.37998385311983884...
"""
import json, math
from pathlib import Path
import numpy as np
from itertools import combinations

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def circum(P, i, j, k):
    a, b, c = P[i], P[j], P[k]
    d = 2 * (a[0] * (b[1] - c[1]) + b[0] * (c[1] - a[1]) + c[0] * (a[1] - b[1]))
    if abs(d) < 1e-18:
        return None
    ux = ((a @ a) * (b[1] - c[1]) + (b @ b) * (c[1] - a[1]) + (c @ c) * (a[1] - b[1])) / d
    uy = ((a @ a) * (c[0] - b[0]) + (b @ b) * (a[0] - c[0]) + (c @ c) * (b[0] - a[0])) / d
    return np.array([ux, uy])


def main():
    P = load()
    n = len(P)
    R = 0.37998385311983884

    print("=== interior Voronoi vertices (from site triples) ===")
    vv = []
    for i, j, k in combinations(range(n), 3):
        p = circum(P, i, j, k)
        if p is None or p @ p > 1.0:
            continue
        d = np.hypot(*(P - p[None, :]).T)
        r = d.min()
        near = [int(t) for t in range(n) if abs(d[t] - r) < 1e-12]
        if len(near) < 3:
            continue          # origin lies outside one of the three cells
        vv.append((r, tuple(np.round(p, 15)), near))
    vv.sort(reverse=True)
    seen = set()
    for r, p, near in vv:
        key = tuple(sorted(near))
        if key in seen:
            continue
        seen.add(key)
        tag = "TIGHT" if abs(r - R) < 1e-11 else ""
        print(f"  r={r:.12f} p=({p[0]:+.12f},{p[1]:+.12f}) |p|={math.hypot(*p):.9f} sites={near} {tag}")

    print("\n=== boundary switches on |x|=1 ===")
    sw = []
    for i, j in combinations(range(n), 2):
        mx = (P[i] + P[j]) / 2
        dv = P[j] - P[i]
        c0 = dv @ mx
        nn = dv @ dv
        t = c0 / nn
        f = dv * t
        h = math.hypot(*f)
        if h > 1:
            continue
        u = np.array([-dv[1], dv[0]]) / math.sqrt(nn)
        s = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * s * u
            d = np.hypot(*(P - p[None, :]).T)
            r = d.min()
            if r >= R - 1e-11:
                near = [int(t2) for t2 in range(n) if abs(d[t2] - r) < 1e-12]
                sw.append((r, tuple(np.round(p, 15)), near, (i, j)))
    sw.sort(reverse=True)
    for r, p, near, pr in sw:
        th = math.atan2(p[1], p[0])
        print(f"  r={r:.12f} theta={th:+.12f} p=({p[0]:+.12f},{p[1]:+.12f}) sites={near} pair={pr}")

    print("\n=== tight-site reach report ===")
    reach = {}
    for r, p, near in vv:
        if abs(r - R) < 1e-11:
            for t in near:
                reach.setdefault(t, []).append(("V", p))
    for r, p, near, pr in sw:
        for t in near:
            reach.setdefault(t, []).append(("S", p))
    for t in range(n):
        print(f"  site {t}: {len(reach.get(t, []))} tight points, {sorted(set(k for k, _ in reach.get(t, [])))}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c5_tight.json").write_text(json.dumps({
        "R": R,
        "vor_tight": [{"r": r, "p": list(p), "sites": near} for r, p, near in vv if abs(r - R) < 1e-11],
        "switch_tight": [{"r": r, "p": list(p), "sites": near, "pair": list(pr)} for r, p, near, pr in sw],
    }, indent=2))
    print("\nwrote", OUT / "c5_tight.json")


if __name__ == "__main__":
    main()
