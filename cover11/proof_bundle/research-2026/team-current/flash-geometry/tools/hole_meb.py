import numpy as np, io, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import min_enclosing_ball
r = 0.38
d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in d['centers_scaled_1e17']])
rho = np.hypot(C[:, 0], C[:, 1]); R9 = C[rho >= 0.62]; H2 = C[rho < 0.62]

nth, nd = 3600, 2000
th = np.linspace(0, 2*np.pi, nth, endpoint=False)
U = np.stack([np.cos(th), np.sin(th)], 1)
dg = np.linspace(0, 1, nd)
pts = []
D = np.zeros(nth)
for i in range(nth):
    P = dg[:, None]*U[i]
    v = np.sqrt(((P[:, None, :] - R9[None, :, :])**2).sum(-1)).min(1)
    m = v > r + 1e-12
    if m.any():
        pts.append(P[m]); D[i] = dg[m].max()
pts = np.concatenate(pts)
print("hole samples:", len(pts), " depth D: min %.6f max %.6f" % (D.min(), D.max()))
# MEB of the hole (numeric, via welzl)
try:
    from welzl import welzl  # may not exist
except Exception:
    welzl = None
c, R = min_enclosing_ball(list(pts[::7]))
print("MEB (numeric, subsampled):", np.round(c, 6), "R = %.6f" % R)
print("  |c| = %.6f ; R - r = %.6f" % (np.hypot(*c), R - r))
# is the hole coverable by two discs of radius r?  measure the "2-centre radius"
# via the standard split: try all directions of separation (numeric search)
best = 1e9; bestinfo = None
for t in np.linspace(0, np.pi, 361):
    u = np.array([np.cos(t), np.sin(t)])
    proj = pts @ u
    order = np.argsort(proj)
    P = pts[order]; pr = proj[order]
    # split by a line: left = proj <= s ; find best s by trying a few quantiles
    for frac in np.linspace(0.05, 0.95, 19):
        k = int(frac*len(P))
        c1, r1 = min_enclosing_ball(list(P[:k][::13]))
        c2, r2 = min_enclosing_ball(list(P[k:][::13]))
        m = max(r1, r2)
        if m < best:
            best = m; bestinfo = (t, frac, r1, r2)
print("best linear-split 2-centre radius (numeric, subsampled): %.6f" % best, bestinfo)
print("compare r = 0.38 :", best <= r)
