# -*- coding: utf-8 -*-
"""P20: local/global search around the sharp candidate + finite-criterion check on all classes."""
import os, sys, math, json
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C0 = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R0 = 0.3799838531198387090485181795734298538115979028
RING = [1, 3, 4, 5, 6, 7, 8, 9, 10]
HUB = [0, 2]
lines = []
def P(s=""):
    lines.append(s); print(s)


def build(rho, psi, h1, h2):
    C = np.stack([rho*np.cos(psi), rho*np.sin(psi)], axis=1)
    H = np.stack([h1, h2], axis=0)
    return np.vstack([C, H])


def cov(ALL, refine=True, pts=None):
    if pts is None:
        pts = PTSREF
    d = np.linalg.norm(pts[:, None, :]-ALL[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d)); best = float(d[i])
    if refine:
        def neg(p):
            if p[0]**2+p[1]**2 > 1.0:
                return 1e4*(p[0]**2+p[1]**2-1.0)
            return -float(np.min(np.linalg.norm(ALL-p, axis=1)))
        res = minimize(neg, pts[i], method='Nelder-Mead',
                       options=dict(xatol=1e-15, fatol=1e-17, maxiter=6000))
        best = max(best, -res.fun)
    return best


NR, NTH = 800, 4000
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTSREF = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)


def xvec():
    rho = np.linalg.norm(C0[RING], axis=1)
    psi = np.arctan2(C0[RING, 1], C0[RING, 0])
    return np.concatenate([rho, psi, C0[0], C0[2]])


def fromx(x):
    return build(np.abs(x[:9]), x[9:18], x[18:20], x[20:22])


if __name__ == "__main__":
    x0 = xvec()
    ALL0 = fromx(x0)
    # verify
    d = np.linalg.norm(ALL0[:, None, :]-C0[None, :, :], axis=2)
    P("seed reconstruction: max min-distance both ways = %.3e" % max(d.min(axis=1).max(), d.min(axis=0).max()))
    v0 = cov(ALL0)
    P("candidate covering radius = %.17f" % v0)
    P("")

    # ----- finite criterion cross-check on the candidate -----
    P("=== finite criterion cross-check: max over {switches} u {tips} ===")
    mod = np.linalg.norm(ALL0, axis=1)
    psi = np.arctan2(ALL0[:, 1], ALL0[:, 0])
    order = sorted(range(9), key=lambda j: psi[j])
    def circum(h, i, j):
        a, b, c = ALL0[h], ALL0[i], ALL0[j]
        dd = 2*(a[0]*(b[1]-c[1])+b[0]*(c[1]-a[1])+c[0]*(a[1]-b[1]))
        a2 = a@a; b2 = b@b; c2 = c@c
        return np.array([(a2*(b[1]-c[1])+b2*(c[1]-a[1])+c2*(a[1]-b[1]))/dd,
                         (a2*(c[0]-b[0])+b2*(a[0]-c[0])+c2*(b[0]-a[0]))/dd])
    def swt(i, j):
        a, b = ALL0[i], ALL0[j]
        dd = np.linalg.norm(a-b); m = (a+b)/2
        hh = math.sqrt(max(R0*R0-dd*dd/4, 0.0))
        pp = np.array([-(b-a)[1], (b-a)[0]])/dd
        p1 = m+hh*pp; p2 = m-hh*pp
        return p1 if np.linalg.norm(p1) <= np.linalg.norm(p2) else p2
    S = []
    for k in range(9):
        a = order[k]; b = order[(k+1) % 9]
        S.append(("SW(%d,%d)" % (a, b), swt(a, b)))
        for h in (9, 10):
            t = circum(h, a, b)
            if np.linalg.norm(t-ALL0[h]) <= R0+1e-6:
                S.append(("TIP(%d,%d|h%d)" % (a, b, h-9), t))
    vals = sorted(((float(np.min(np.linalg.norm(ALL0-p, axis=1))), nm) for nm, p in S), reverse=True)
    P("top-8 values over S: %s" % [(nm, round(v, 12)) for v, nm in vals[:8]])
    P("max over S = %.17f ; true candidate radius = %.17f ; diff = %+.3e"
      % (vals[0][0], v0, vals[0][0]-v0))
    P("")

    # ----- local search -----
    P("=== local search (Nelder-Mead, 22 vars) ===")
    def f(x):
        return cov(fromx(x))
    best = (v0, x0.copy())
    rng = np.random.default_rng(99)
    P("start %.17f" % v0)
    for sc, ntr in [(0.0, 1), (2e-3, 2), (8e-3, 2)]:
        for t in range(ntr):
            xs = x0.copy() if sc == 0 else x0 + np.concatenate([
                sc*rng.standard_normal(9), sc*rng.standard_normal(9), 2*sc*rng.standard_normal(4)])
            r = minimize(f, xs, method='Nelder-Mead',
                         options=dict(maxiter=20000, maxfev=20000, xatol=1e-12, fatol=1e-16, adaptive=True))
            v = f(r.x)
            P("  sc=%.0e t=%d: %.12f -> %.12f  (delta %+.3e)" % (sc, t, f(xs), v, v-best[0]))
            if v < best[0]-1e-15:
                best = (v, r.x.copy()); P("     *** better")
    P("")
    P("BEST = %.17f   (candidate %+.3e)" % (best[0], best[0]-v0))
    ALLb = fromx(best[1])
    dd = np.linalg.norm(ALLb[:, None, :]-C0[None, :, :], axis=2)
    P("best-to-candidate Hausdorff = %.3e" % max(dd.min(axis=1).max(), dd.min(axis=0).max()))
    with open(os.path.join(OUT, "p20_search.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
