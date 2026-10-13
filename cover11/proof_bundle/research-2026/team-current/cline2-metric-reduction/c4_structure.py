"""C4: exact reconstruction of the candidate's nearest-site structure.

For each site i we reconstruct its (possibly unbounded) Voronoi cell as an
explicit convex polygon:  the cell is the feasible set of the linear system
    <x, c_j - c_i> <= (|c_j|^2 - |c_i|^2)/2      for j != i,
so it is a convex polygon; we compute it by clipping a large box with these
half-planes.  Then we clip by the unit disk and compute
   max_{x in cell(i) cap D} |x - c_i|
per site, and record where the maximum is attained (vertex / boundary arc).
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


def clip_halfplane(poly, a, c):
    """keep <x,a> <= c."""
    if len(poly) == 0:
        return poly
    out = []
    m = len(poly)
    for k in range(m):
        p, q = poly[k], poly[(k + 1) % m]
        fp = p @ a - c
        fq = q @ a - c
        if fp <= 0:
            out.append(p)
            if fq > 0:
                t = fp / (fp - fq)
                out.append(p + t * (q - p))
        elif fq <= 0:
            t = fp / (fp - fq)
            out.append(p + t * (q - p))
    return np.array(out)


def main():
    P = load()
    n = len(P)
    BIG = 4.0
    box = np.array([[-BIG, -BIG], [BIG, -BIG], [BIG, BIG], [-BIG, BIG]], dtype=float)
    R = 0.0
    report = {}
    for i in range(n):
        poly = box.copy()
        for j in range(n):
            if j == i:
                continue
            a = P[j] - P[i]
            c = (P[j] @ P[j] - P[i] @ P[i]) / 2
            poly = clip_halfplane(poly, a, c)
        if len(poly) < 3:
            print(f"site {i}: empty/degenerate cell ({len(poly)} vertices)")
            continue
        # cell polygon; clip with disk
        cl = clip_halfplane(poly, np.array([0.0, 0.0]), 1.0)  # |x|<=1 is not a halfplane -> use exact disk clip
        # exact disk clip instead:
        def inside(p):
            return p @ p <= 1.0
        def inter(a2, b2):
            d = b2 - a2
            A = d @ d
            B = 2 * (a2 @ d)
            C = a2 @ a2 - 1.0
            disc = max(B * B - 4 * A * C, 0.0)
            t = (-B + math.sqrt(disc)) / (2 * A)
            return a2 + min(max(t, 0.0), 1.0) * d
        disk = []
        m = len(poly)
        for k in range(m):
            p, q = poly[k], poly[(k + 1) % m]
            ip, iq = inside(p), inside(q)
            if ip:
                disk.append(p)
                if not iq:
                    disk.append(inter(p, q))
            elif iq:
                disk.append(inter(p, q))
        disk = np.array(disk) if disk else np.zeros((0, 2))
        best = 0.0; arg = None
        if len(disk) >= 3:
            for k in range(len(disk)):
                for s in np.linspace(0, 1, 2001):
                    x = disk[k] * (1 - s) + disk[(k + 1) % len(disk)] * s
                    d = np.hypot(*(x - P[i]))
                    if d > best:
                        best, arg = d, x
            # fan
            for k in range(1, len(disk) - 1):
                for s in np.linspace(0, 1, 301):
                    for u in np.linspace(0, 1 - s, 301):
                        x = s * disk[k] + u * disk[k + 1] + (1 - s - u) * disk[0]
                        d = np.hypot(*(x - P[i]))
                        if d > best:
                            best, arg = d, x
        report[i] = {"cell": poly.tolist(), "diskcell": disk.tolist(), "max": float(best),
                     "arg": None if arg is None else np.asarray(arg, float).tolist()}
        R = max(R, best)
    print("R(C) =", R)
    print("\nsite |c|, cell max, argmax, argmax radius")
    for i in sorted(report):
        d = report[i]
        arg = d["arg"]
        print(f"  {i:2d} |c|={np.hypot(*P[i]):.9f} max={d['max']:.12f}"
              + (f"  arg=({arg[0]:+.9f},{arg[1]:+.9f}) |arg|={np.hypot(*arg):.9f}" if arg else ""))
    print("\ntight sites (max >= R-1e-10):",
          [i for i in sorted(report) if report[i]['max'] >= R - 1e-10])
    OUT.mkdir(exist_ok=True)
    (OUT / "c4_structure.json").write_text(json.dumps(
        {"R": R, "sites": {str(k): v for k, v in report.items()}, "centers": P.tolist()}, indent=2))
    print("wrote", OUT / "c4_structure.json")


if __name__ == "__main__":
    main()
