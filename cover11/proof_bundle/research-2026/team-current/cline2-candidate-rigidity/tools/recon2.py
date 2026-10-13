"""Reconstruct the lead's closure configuration and measure its ACTUAL covering radius.

Face-based geometry (verified to reproduce the lead's own residual 9.99e-16):
  * 11 triangular faces; face t has angles x[3t:3t+3] (sum pi); hub angle sums = 2 pi.
  * x[42:53] are log(rho_face/R) for t=0..10, x[53:62] are log(rho_switch/R) for the 9
    boundary switches, x[62] = log R.
  * edge e shared by faces t,t':  rho_t sin A_e = rho_t' sin B_e   (A from the face angle
    opposite e in t, B likewise in t').
  * boundary switch i: rho_i = switch radius, angles A = pi/2 - gamma_i, B = b_i
    (from the code: B[ei, 3*nf+bi] = -1, bc = pi/2; alpha[i, 3*nf+bi] is the sector).
Then: the ring sector angle is alpha_i = b_i + b_{i+1}, the ring-ring chord is
  L^2 = u^2 + v^2 - 2 u v cos(alpha_i), and the switch radius is the distance from the
switch point to the ring centre.  This gives 9 ring centres on a polygonal chain; the two
hubs are placed by the hub-face metric.  We only need the RING part plus the two hubs;
the ring chain closes because there are exactly 9 boundary edges.

Instead of re-deriving the whole tiling we do something simpler and decisive:  we take the
configuration's ring distances from the closure variables and test whether the resulting
covering radius can equal the lead's reported R.  If the closure family is correct the
total area must be exactly pi at the optimum; we verify that and then compare R.
"""
import json, io, math
import numpy as np
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAD = ROOT / 'research-2026' / 'team-current' / 'lead'
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
L = json.load(io.open(LEAD / 'q0_exact_closure_radius.json', encoding='utf-8-sig'))
G = json.load(io.open(LEAD / 'q0_graphs.json', encoding='utf-8-sig'))
x = np.array(L['x0'])
pi = math.pi
faces = G[2]['faces']; edges = G[2]['edges']
nf = len(faces); na = 3 * nf + 9; nv = na + nf + 9 + 1
print('nf=%d na=%d cols=%d  len(x)=%d' % (nf, na, nv, len(x)))
eq = np.zeros((nf + 2, nv)); rhs = np.r_[np.ones(nf) * pi, [2 * pi, 2 * pi]]
alpha = np.zeros((9, nv)); ac = np.ones(9) * pi
A = np.zeros((len(edges), nv)); B = np.zeros_like(A); bc = np.zeros(len(edges))
U = np.zeros_like(A); V = np.zeros_like(A)
for t, f in enumerate(faces):
    eq[t, 3 * t:3 * t + 3] = 1
    for k, i in enumerate(f):
        if i < 9:
            alpha[i, 3 * t + k] = -1
        else:
            eq[nf + i - 9, 3 * t + k] = 1
for ei, (i, j) in enumerate(edges):
    adj = [(t, f.index(next(v for v in f if v not in (i, j)))) for t, f in enumerate(faces) if i in f and j in f]
    t, k = adj[0]; A[ei, 3 * t + k] = 1; U[ei, na + t] = 1
    if len(adj) == 2:
        t, k = adj[1]; B[ei, 3 * t + k] = 1; V[ei, na + t] = 1
    else:
        bi = next(b for b in range(9) if {b, (b + 1) % 9} == {i, j})
        B[ei, 33 + bi] = -1; bc[ei] = pi / 2; V[ei, na + nf + bi] = 1
        alpha[i, 33 + bi] = -1; alpha[j, 33 + bi] = -1

def calc(xx):
    a = A @ xx; b = B @ xx + bc; al = ac + alpha @ xx
    u = np.exp(U @ xx + xx[62]); v = np.exp(V @ xx + xx[62])
    return a, b, al, u, v

def ceq(xx):
    a, b, al, u, v = calc(xx)
    ang = np.r_[eq @ xx - rhs, (U - V) @ xx + np.log(np.sin(A @ xx)) - np.log(np.sin(B @ xx + bc))]
    y = np.exp(xx[53:62] + xx[62]); yp = np.roll(y, 1)
    ch2 = yp * yp + y * y - 2 * yp * y * np.cos(al)
    w = 2 * np.arcsin(np.sqrt(np.clip(ch2, 1e-16, 3.99)) / 2)
    L_ = np.arctan2(y * np.sin(al), yp - y * np.cos(al))
    T = pi - al - L_
    closure = T + np.roll(L_, -1) + 2 * xx[33:42] + (w + np.roll(w, -1)) / 2 - pi
    return ang, closure, (al, u, v, w, y)

ang, closure, extra = ceq(x)
print('max |angle rows|   : %.3e' % np.max(np.abs(ang)))
print('max |closure rows| : %.3e' % np.max(np.abs(closure)))
al, u, v, w, y = extra
print('sector angles al   :', np.round(al, 6), ' (sum %.12f)' % al.sum())
print('switch radii y     :', np.round(y, 9), ' y/R =', np.round(y / 0.38, 6))
print('face radii u       :', np.round(u, 9))
print('face radii v       :', np.round(v, 9))
print('max over the 20 radii of (rho/R) = %.12f' % (max(u.max(), v.max(), y.max()) / 0.38))
print('boundary arc widths w: sum = %.15f  (2pi = %.15f)' % (w.sum(), 2 * pi))
print('X_T = R*exp(x62) = %.20f' % (0.38 * math.exp(x[62])))
print('reported opt R   = %.20f' % L['runs'][0]['radius'])
print('certified R      = %s' % D['certified_interval']['lo'][:32])

# Ring chain: ring i is the "hub" of the switch sector i (between switch i and i+1).
# The switch point S_i is at distance y_i from ring centre c_i (and y_{i+1} from c_{i+1}).
# The sector angle at switch i belonging to ring i is  A_i = pi/2 - gamma_i = pi/2 - b_i? 
# From the code: the switch rows use A -> from face t (a ring face) and B = pi/2 - b_i.
# So the boundary switch is a "virtual face" with two angles: (pi/2 - gamma) and b_i.
print()
print('b_i (switch angles) =', np.round(x[33:42], 6), 'sum =%.9f' % x[33:42].sum())
print('switch (pi/2-b_i)   =', np.round(pi / 2 - x[33:42], 6))
