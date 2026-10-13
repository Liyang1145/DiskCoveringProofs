# -*- coding: utf-8 -*-
"""P7: fast covering-radius evaluator + local optimality probe on the saved candidate.

Evaluator (vectorised, float64):
   given flat center array (11,2), R_area = max over
     (a) a fine Cartesian grid in D of  min_k |p - c_k|
     (b) a fine polar grid of the boundary
   The maximum over the grid is a LOWER bound on the true covering radius; for the
   *candidate* we also evaluate the exact argmax by local refinement so that the
   regression runs do not lose precision.

Probe: perturb only the 9 rings (hubs stay fixed -- they are the tight hubs, and the
covering radius problem with fixed hubs is exactly min over rings of the max distance).
Also: perturb everything including hubs.
"""
import os, sys, math, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
_obj = os.path.join(OUT, "certified_object_copy.json")
with open(_obj, "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C0 = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R0 = 0.3799838531198387090485181795734298538115979028

XS = np.linspace(-1, 1, 801)
GX, GY = np.meshgrid(XS, XS)
MK = GX**2+GY**2 <= 1.0
GRID = np.stack([GX[MK], GY[MK]], axis=1)          # ~500k points
NPHI = 200000
PH = np.linspace(0, 2*np.pi, NPHI, endpoint=False)
BD = np.stack([np.cos(PH), np.sin(PH)], axis=1)


def cover_radius(C, refine=True):
    d = np.linalg.norm(GRID[:, None, :]-C[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d)); best = d[i]
    # local refinement: worst point = a Voronoi vertex or boundary point; use scipy
    from scipy.optimize import minimize as _m
    def neg(p):
        if p[0]**2+p[1]**2 > 1.0:
            return 10.0 + p[0]**2+p[1]**2
        return -np.min(np.linalg.norm(C-p, axis=1))
    res = _m(neg, GRID[i], method='Nelder-Mead',
             options=dict(xatol=1e-14, fatol=1e-16, maxiter=4000))
    r_in = -res.fun
    db = np.linalg.norm(BD[:, None, :]-C[None, :, :], axis=2).min(axis=1).max()
    return max(r_in, db), r_in, db, GRID[i], res.x


def fan_class(C):
    from scipy.spatial import Delaunay
    mod = np.linalg.norm(C, axis=1)
    ring = sorted(j for j in range(11) if mod[j]+R0 >= 1)
    hub = sorted(j for j in range(11) if mod[j]+R0 < 1)
    tri = Delaunay(C)
    deg = {}
    leaves = 0
    for s in tri.simplices:
        s = [int(x) for x in s]
        h = [x for x in s if x in hub]
        if not h:
            return None
        if len(h) == 2:
            for x in h:
                deg[x] = deg.get(x, 0)+1
        elif len(h) == 1:
            deg[h[0]] = deg.get(h[0], 0)+1
            leaves += 1
    return ring, hub, deg, leaves, len(tri.simplices)


if __name__ == "__main__":
    lines = []
    def P(s=""):
        lines.append(s); print(s)

    r, ri, db, p0, pref = cover_radius(C0)
    P("candidate: cover radius = %.17f  (interior %.17f, boundary %.17f)" % (r, ri, db))
    P("  R_claim-R = %+.3e" % (r-R0))
    P("  interior argmax %s -> refined %s" % (np.round(p0, 8).tolist(), np.round(pref, 10).tolist()))
    fc = fan_class(C0)
    P("  fan class: ring=%s hub=%s deg=%s leaves=%d nfaces=%d" % fc)

    rng = np.random.default_rng(7)
    P("")
    P("=== perturb ONLY the 9 rings (hubs fixed) ===")
    ring = fc[0]
    best_dn = 0.0
    for t in range(120):
        C = C0.copy()
        C[ring] += rng.standard_normal((9, 2))*0.002
        rr, _, _, _, _ = cover_radius(C, refine=True)
        if rr < r:
            d = r-rr
            if d > best_dn:
                best_dn = d
                P("   t=%3d  cover=%.17f   improvement %+.3e" % (t, rr, -d))
    P("   max improvement over 120 ring perturbations: %+.3e" % (-best_dn))
    P("")
    P("=== perturb ALL 11 centres ===")
    best_dn2 = 0.0
    for t in range(120):
        C = C0 + rng.standard_normal((11, 2))*0.002
        rr, _, _, _, _ = cover_radius(C, refine=True)
        if rr < r:
            d = r-rr
            if d > best_dn2:
                best_dn2 = d
                P("   t=%3d  cover=%.17f   improvement %+.3e" % (t, rr, -d))
    P("   max improvement over 120 full perturbations: %+.3e" % (-best_dn2))
    P("")
    P("=== scaled perturbations (1e-4 .. 1e-2) on rings ===")
    for h in [1e-4, 1e-3, 1e-2]:
        m = 0.0
        for t in range(60):
            C = C0.copy()
            C[ring] += rng.standard_normal((9, 2))*h
            rr, _, _, _, _ = cover_radius(C, refine=True)
            m = max(m, r-rr)
        P("   h=%.0e : max improvement %+.3e" % (h, -m))

    with open(os.path.join(OUT, "p7_local_opt.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
