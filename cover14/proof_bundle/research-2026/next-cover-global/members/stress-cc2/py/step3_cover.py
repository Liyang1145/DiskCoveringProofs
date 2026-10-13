"""step3_cover.py -- what radius does each candidate geometry actually COVER at?
Numerically maximise f(x)=min_i |x-C_i| over the closed unit disk. Grid + local polish.
No root solving. Read-only.

Outputs logs/step3_cover.txt, evidence/step3_cover.json
"""
import json, sys
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


def f_np(X, Cnp):
    """min distance from point(s) X (N,2) to centers Cnp (14,2)"""
    d = np.sqrt(((X[:, None, :] - Cnp[None, :, :]) ** 2).sum(-1))
    return d.min(1)


def covering_radius(C, tag, ngrid=1200):
    Cnp = np.array([[float(c[0]), float(c[1])] for c in C])
    xs = np.linspace(-1, 1, ngrid)
    XX, YY = np.meshgrid(xs, xs)
    P = np.stack([XX.ravel(), YY.ravel()], 1)
    keep = (P ** 2).sum(1) <= 1.0
    P = P[keep]
    f = f_np(P, Cnp)
    W("  [%s] grid %d pts: max f = %.16f  at (%.9f, %.9f)" % (tag, len(P), f.max(), *P[f.argmax()]))
    # polish top candidates with scipy
    from scipy.optimize import minimize
    idx = np.argsort(-f)[:400]
    best = -1; bx = None
    def obj(x):
        return -f_np(x.reshape(1, 2), Cnp)[0]
    cons = [{'type': 'ineq', 'fun': lambda x: 1.0 - x[0] ** 2 - x[1] ** 2}]
    for i in idx:
        res = minimize(obj, P[i], method='SLSQP', constraints=cons,
                       options=dict(ftol=1e-18, maxiter=300))
        v = -res.fun
        if v > best:
            best = v; bx = res.x
    # also polish points on the boundary circle explicitly
    for th in np.linspace(0, 2 * np.pi, 2001)[:-1]:
        x0 = np.array([np.cos(th), np.sin(th)])
        res = minimize(obj, x0, method='SLSQP', constraints=cons, options=dict(ftol=1e-20, maxiter=300))
        v = -res.fun
        if v > best:
            best = v; bx = res.x
    W("  [%s] polished max f = %.18f at (%.15f, %.15f)  |x|=%s" % (
        tag, best, bx[0], bx[1], mp.nstr(mp.sqrt(mp.mpf(bx[0]) ** 2 + mp.mpf(bx[1]) ** 2), 12)))
    # high precision verification of the found point
    x = (mp.mpf(bx[0]), mp.mpf(bx[1]))
    ds = sorted((dist(x, C[i]), i) for i in range(14))
    W("        hp: nearest 4 distances = %s" % [(mp.nstr(d, 20), i) for d, i in ds[:4]])
    return best, bx, [int(ds[0][1])]


g = new_geom()
Cnew = centers_from(g)
r_new = g["r"]
Cold, Rold, th_old = old_geom_centers()

W("== step3: actual covering radius of each candidate geometry ==")
W("NEW stationary root: r* (as given) = %s" % mp.nstr(r_new, 40))
bn, xn, nn = covering_radius(Cnew, "NEW root")
W("OLD refined (nonstationary) root: R_old = %s" % mp.nstr(Rold, 40))
bo, xo, no = covering_radius(Cold, "OLD root")
W("")
W("SUMMARY")
W("  new root : covering radius = %.18f ; declared r* = %.18f ; gap = %.3e" % (bn, float(r_new), bn - float(r_new)))
W("  old root : covering radius = %.18f ; declared R  = %.18f ; gap = %.3e" % (bo, float(Rold), bo - float(Rold)))
W("  improved-upper threshold T (lead) = 0.3317320342762341226")
W("  old-root cover radius <= T ? %s" % (bo <= 0.3317320342762341226))
W("  new-root cover radius <= T ? %s" % (bn <= 0.3317320342762341226))

# Voronoi-vertex candidate list (all triples, circumcentre anywhere) for NEW root:
import itertools
W("")
W("### NEW root: triples with circumcentre inside D, no empty-circle filter, radius>=r*-0.02")
cand = []
for tri in itertools.combinations(range(14), 3):
    p, q, s = (Cnew[t] for t in tri)
    d = 2 * ((p[0] - s[0]) * (q[1] - s[1]) - (p[1] - s[1]) * (q[0] - s[0]))
    if d == 0:
        continue
    b1 = p[0] ** 2 + p[1] ** 2 - s[0] ** 2 - s[1] ** 2
    b2 = q[0] ** 2 + q[1] ** 2 - s[0] ** 2 - s[1] ** 2
    ux = (b1 * (q[1] - s[1]) - (p[1] - s[1]) * b2) / d
    uy = ((p[0] - s[0]) * b2 - b1 * (q[0] - s[0])) / d
    u = (ux, uy)
    if norm(u) > 1:
        continue
    R3 = dist(u, p)
    if R3 < r_new - mp.mpf("0.02"):
        continue
    m = min(dist(u, Cnew[l]) for l in range(14) if l not in tri)
    cand.append((tri, u, R3, m - R3))
for tri, u, R3, marg in sorted(cand, key=lambda z: -float(z[2])):
    W("   tri%-16s u=(%s,%s) R=%s  R-r*=%s  empty-margin=%s" % (
        str(tri), mp.nstr(u[0], 14), mp.nstr(u[1], 14), mp.nstr(R3, 18), mp.nstr(R3 - r_new, 5), mp.nstr(marg, 5)))

json.dump(dict(r_new=mp.nstr(r_new, 40), R_old=mp.nstr(Rold, 40),
               new_cover=bn, old_cover=bo,
               new_argmax=list(map(float, xn)), old_argmax=list(map(float, xo))),
          open(HERE.parent / "evidence/step3_cover.json", "w"), indent=1)
(HERE.parent / "logs/step3_cover.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\nwrote logs/step3_cover.txt")
