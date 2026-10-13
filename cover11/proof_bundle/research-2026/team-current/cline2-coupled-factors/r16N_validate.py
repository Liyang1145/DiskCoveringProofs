"""cline2-coupled-factors R16N: validate the Jacobian gradient of G and test whether the
mean-value certificate can converge (rate check)."""
import sys, math
from pathlib import Path
from mpmath import iv
sys.path.insert(0, str(Path(__file__).parent))
import r16M_cert as M

# ---- 1. validate G and grad G against high-precision finite differences ----
print('=== gradient validation (G at a point, central differences in float64) ===')
import numpy as np


def Gf(x):
    r, b1, b2, dl = x
    q = M.build(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    if q is None:
        return float('nan')
    res = M.G_and_grad(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    return float(res[0].a), float(res[1].a), float(res[2].a), float(res[3].a)


for x0 in [(0.379, 1.02, 1.02, -0.45), (0.376, 1.05, 1.10, 0.10), (0.3795, 1.10, 1.05, -0.20)]:
    g = Gf(x0)[1:]
    fd = []
    h = 1e-7
    for j in range(4):
        xp = list(x0); xp[j] += h
        xm = list(x0); xm[j] -= h
        fd.append((Gf(xp)[0]-Gf(xm)[0])/(2*h))
    print(f'  x0={x0}')
    print(f'    analytic  = {[round(v,8) for v in g]}')
    print(f'    finite-diff = {[round(v,8) for v in fd]}')
    print(f'    max abs diff = {max(abs(a-b) for a,b in zip(g,fd)):.2e}')

# ---- 2. convergence rate: shrink a box around the worst region and watch the bound ----
print('\n=== mean-value bound vs box size (worst region) ===')
ctr = (0.379375, 1.0233, 1.0233, -0.4449)
for h in [0.04, 0.02, 0.01, 0.005, 0.0025]:
    lo = [c-h for c in ctr]; hi = [c+h for c in ctr]
    bnd = M.G_and_grad(iv.mpf([lo[0], hi[0]]), iv.mpf([lo[1], hi[1]]),
                       iv.mpf([lo[2], hi[2]]), iv.mpf([lo[3], hi[3]]))
    pt = M.G_and_grad(*[iv.mpf(repr(c)) for c in ctr])
    if bnd is None or pt is None:
        print(f'  h={h}: infeasible'); continue
    G, Gr, Gb1, Gb2, Gd = bnd
    L = (float(abs(Gr).b)+float(abs(Gb1).b)+float(abs(Gb2).b)+float(abs(Gd).b))*h
    print(f'  h={h:7.4f}: G0={float(pt[0].a):+.6f}  |grad|max=({float(abs(Gr).b):.3f},'
          f'{float(abs(Gb1).b):.3f},{float(abs(Gb2).b):.3f},{float(abs(Gd).b):.3f})  '
          f'L={L:.4f}  lo={float(pt[0].a)-L:+.6f}')

# ---- 3. how negative does G actually get on the admissible set? (bounded probe) ----
print('\n=== is G>=0.15 even plausible? bounded numerical min of G over the admissible set ===')
best = None
for i in range(41):
    r = 0.375+(0.38-0.375)*i/40
    bhi = math.acos(r)
    for j in range(31):
        b1 = 1+(bhi-1)*j/30
        for k in range(31):
            b2 = 1+(bhi-1)*k/30
            for m in range(61):
                dl = -bhi+(bhi+ (-bhi))*0
                dl = -b2+(b1+b2)*m/60
                res = Gf((r, b1, b2, dl))
                if res != res:
                    continue
                # admissibility
                q = M.build(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
                s = q['s']
                H = q['H']
                cap2 = 2*r*math.sin(2*b2+dl)
                beta = float(H.a)**2-2*float(s.a)*math.cos(dl)*float(H.a)+2*r*(1-r)
                if float(H.a) > cap2 or beta > 0:
                    continue
                if best is None or res < best[0]:
                    best = (res, (r, b1, b2, dl))
print(f'  numerical minimum of G over the admissible set: {best[0]:.6f} at {best[1]}')
