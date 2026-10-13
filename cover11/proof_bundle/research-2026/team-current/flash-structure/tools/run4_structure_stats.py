"""Run 4: structural statistics over legal ledgers.

 A  are the 9 tips in convex position (all of them vertices of the convex hull)?
 B  tips lemma (direct margin) -> min over ledgers
 C  line-separable subsets of the tips vs cyclic intervals (contiguous blocks)
 D  hole connectedness + cl(H) subset conv(tips) for a subsample (grid)
"""
import math
import os
import random
import sys

import numpy as np
from scipy import ndimage
from scipy.spatial import ConvexHull

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vgeom as V  # noqa: E402

OUT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "out"))
os.makedirs(OUT, exist_ok=True)
rep = []
def P(*a):
    s = " ".join(str(x) for x in a)
    rep.append(s)


def linsep_subsets(pts):
    """all subsets of pts that are line-separable (cut off by some half plane), |S|<n."""
    n = len(pts)
    seen = set()
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # line through pts[i] (outer) with direction (pts[j]-pts[i]) rotated: take halfplane
            dx, dy = pts[j][0] - pts[i][0], pts[j][1] - pts[i][1]
            for nx, ny in ((dy, -dx), (-dy, dx)):
                # half plane {x : (x - pts[i]).n > 0}, perturbed by tiny rotation two ways
                for ang in (-1e-7, 0.0, 1e-7):
                    ca, sa = math.cos(ang), math.sin(ang)
                    mx, my = nx * ca - ny * sa, nx * sa + ny * ca
                    S = tuple(k for k in range(n)
                              if (pts[k][0] - pts[i][0]) * mx + (pts[k][1] - pts[i][1]) * my > 1e-12)
                    if 0 < len(S) < n:
                        seen.add(S)
    return seen


def contig_subsets(n):
    out = set()
    for a in range(n):
        for L in range(1, n):
            out.add(tuple(sorted((a + t) % n for t in range(L))))
    return out


def main():
    rng = random.Random(7)
    rgrid = [0.3601, 0.3660254, 0.3700, 0.3750, 0.3775, 0.37998385, 0.3800]
    worst = {}
    nonconv, holes_nonconv = [], {}
    for r in rgrid:
        key = round(r, 6)
        mn = math.inf
        nconv = 0
        ntot = 0
        wcase = None
        extra_ls = 0
        for _ in range(1500):
            out = V.sample_ledger(r, rng)
            if out is None:
                continue
            t, o, g, E = out
            ntot += 1
            tc = V.tips_cyclic(r, t, o)
            pts = [e["v"] for e in tc]
            arr = np.array(pts)
            hull = ConvexHull(arr)
            isconv = len(hull.vertices) == 9
            nconv += int(isconv)
            m = min(V.dist(pts[k], tc and V.build_ring(r, t, o)[1][j]) - r
                    for k in range(9) for j in range(9) if j not in (k, (k + 1) % 9))
            if m < mn:
                mn, wcase = m, (t, o, E)
            if not isconv:
                nonconv.append((r, t, o, len(hull.vertices)))
            ls = linsep_subsets(pts)
            ct = contig_subsets(9)
            extra_ls += len([s for s in ls if s not in ct])
        worst[key] = (ntot, mn, nconv, extra_ls, wcase)
        P(f"[r={r}] n={ntot}  min tips-margin={mn:+.4e}  convex-position={nconv}/{ntot}  "
          f"line-separable-subsets-not-contiguous (total over ledgers)={extra_ls}")
    P(f"[A] ledgers with non-convex tips: {len(nonconv)}")
    for r, t, o, nv in nonconv[:5]:
        P(f"    r={r} hull vertices={nv} t(deg)={[round(math.degrees(x),3) for x in t]} "
          f"o(deg)={[round(math.degrees(x),3) for x in o]}")
    if worst:
        kmin = min(worst, key=lambda k: worst[k][1])
        P(f"[B] global worst tips margin {worst[kmin][1]:+.4e} at r={kmin}")
        t, o, E = worst[kmin][4]
        P(f"    ledger: E={math.degrees(E):.4f}deg  t(deg)={[round(math.degrees(x),4) for x in t]}")
        P(f"            o(deg)={[round(math.degrees(x),4) for x in o]}")
    with open(os.path.join(OUT, "run4_structure_stats.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(rep) + "\n")
    print("\n".join(rep))


if __name__ == "__main__":
    main()
