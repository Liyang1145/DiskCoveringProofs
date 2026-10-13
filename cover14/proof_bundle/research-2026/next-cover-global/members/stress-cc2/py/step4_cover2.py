"""step4_cover2.py -- robust covering-radius: candidate enumeration (Voronoi vertices + boundary arc
midpoints) with hp evaluation, plus grid cross-check with exact grid-argmax reporting.
"""
import json, sys, itertools
from pathlib import Path
import mpmath as mp
import numpy as np

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, old_geom_centers, norm, dist

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

def pol2c(th):
    return (mp.cos(th), mp.sin(th))

def cover_scan(C, tag):
    r = None
    W("-- %s --" % tag)
    # (a) all triple circumcentres inside closed disk
    best = (mp.mpf(0), None, None)
    n_in = 0
    for tri in itertools.combinations(range(len(C)), 3):
        p, q, s = (C[t] for t in tri)
        det = 2 * ((p[0] - s[0]) * (q[1] - s[1]) - (p[1] - s[1]) * (q[0] - s[0]))
        if det == 0:
            continue
        b1 = p[0] ** 2 + p[1] ** 2 - s[0] ** 2 - s[1] ** 2
        b2 = q[0] ** 2 + q[1] ** 2 - s[0] ** 2 - s[1] ** 2
        ux = (b1 * (q[1] - s[1]) - (p[1] - s[1]) * b2) / det
        uy = ((p[0] - s[0]) * b2 - b1 * (q[0] - s[0])) / det
        u = (ux, uy)
        if norm(u) > 1:
            continue
        n_in += 1
        f = min(dist(u, C[i]) for i in range(len(C)))
        if f > best[0]:
            best = (f, u, ("tri", tri))
    W("  triples with circumcentre in closed D: %d" % n_in)
    W("  max over those of min-dist = %s at (%s,%s)  [%s]" % (mp.nstr(best[0], 20),
      mp.nstr(best[1][0], 16), mp.nstr(best[1][1], 16), best[2]))
    # (b) boundary: f(theta) = min_i |x(theta)-C_i| ; maximise by dense scan + refinement
    N = 200000
    bs, ba = mp.mpf(0), None
    for k in range(N):
        th = 2 * mp.pi * k / N
        x = pol2c(th)
        f = min(dist(x, C[i]) for i in range(len(C)))
        if f > bs:
            bs, ba = f, th
    # golden refinement in a small window (f is piecewise smooth; refine then compare neighbours)
    lo, hi = ba - 2 * mp.pi / N, ba + 2 * mp.pi / N
    for _ in range(120):
        m1 = lo + (hi - lo) / 3; m2 = hi - (hi - lo) / 3
        f1 = min(dist(pol2c(m1), C[i]) for i in range(len(C)))
        f2 = min(dist(pol2c(m2), C[i]) for i in range(len(C)))
        if f1 < f2:
            lo = m1
        else:
            hi = m2
    bth = (lo + hi) / 2
    bf = min(dist(pol2c(bth), C[i]) for i in range(len(C)))
    W("  max over boundary S^1 = %s at angle %s deg;  point (%s,%s)" % (
        mp.nstr(bf, 20), mp.nstr(bth * 180 / mp.pi, 14),
        mp.nstr(mp.cos(bth), 16), mp.nstr(mp.sin(bth), 16)))
    ds = sorted((dist(pol2c(bth), C[i]), i) for i in range(len(C)))
    W("     nearest at boundary argmax: %s" % [(mp.nstr(d, 18), i) for d, i in ds[:3]])
    # (c) grid cross-check (numpy) reporting the grid argmax in full
    Cnp = np.array([[float(c[0]), float(c[1])] for c in C])
    xs = np.linspace(-1, 1, 1500)
    XX, YY = np.meshgrid(xs, xs)
    P = np.stack([XX.ravel(), YY.ravel()], 1)
    P = P[(P ** 2).sum(1) <= 1.0]
    d = np.sqrt(((P[:, None, :] - Cnp[None, :, :]) ** 2).sum(-1))
    f = d.min(1)
    i = int(f.argmax())
    px = (mp.mpf(float(P[i, 0])), mp.mpf(float(P[i, 1])))
    fp = min(dist(px, C[j]) for j in range(len(C)))
    W("  grid(1500^2) argmax f=%.18f at (%.15f,%.15f); hp min-dist there = %s ; |x|=%s" % (
        f[i], P[i, 0], P[i, 1], mp.nstr(fp, 18), mp.nstr(norm(px), 12)))
    ds2 = sorted((dist(px, C[j]), j) for j in range(len(C)))
    W("     nearest there: %s" % [(mp.nstr(d2, 18), j) for d2, j in ds2[:4]])
    return dict(tri_max=mp.nstr(best[0], 20), tri_argmax=[mp.nstr(best[1][0], 20), mp.nstr(best[1][1], 20)],
                bd_max=mp.nstr(bf, 20), bd_angle_deg=mp.nstr(bth * 180 / mp.pi, 16),
                grid_max=float(f[i]), grid_argmax=[float(P[i, 0]), float(P[i, 1])])

g = new_geom(); Cnew = centers_from(g); r_new = g["r"]
Cold, Rold, _ = old_geom_centers()
W("== step4: covering radius, independent of scipy ==")
W("NEW root declared r* = %s" % mp.nstr(r_new, 40))
a = cover_scan(Cnew, "NEW root (from lead root-scout z,c,r)")
W("")
W("OLD refined root declared R = %s" % mp.nstr(Rold, 40))
b = cover_scan(Cold, "OLD refined root (hprec_sol_refined)")
W("")
json.dump(dict(r_new=mp.nstr(r_new, 40), R_old=mp.nstr(Rold, 40), new=a, old=b),
          open(HERE.parent / "evidence/step4_cover2.json", "w"), indent=1)
(HERE.parent / "logs/step4_cover2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/step4_cover2.txt")

