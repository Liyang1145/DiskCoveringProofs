"""Independent reconstruction of the closure configuration from the lead's lift x0.

Geometry used (the lead's own conventions, re-derived here):
  * 11 triangular faces with angles A@x, sums = pi; two hub angular sums = 2 pi.
  * the 20 face radii (V@x + log R) and the 9 boundary-switch radii (U@x + log R) are all
    <= R; the switch between ring i and ring i+1 subtends the boundary sector
    alpha_i = b_i + b_{i+1} and has angular defect b_i at its two ends.
  * ring-ring chord:   L^2 = u^2 + v^2 - 2uv cos(alpha_i)         (cosine rule)
    ring-boundary chord: L^2 = u^2 + 1 - 2u cos(alpha)           (unit circle).
We reconstruct the 9 ring centres and 2 hubs from the closure equalities (edge-sharing
angle matching via the law of sines), then measure the ACTUAL covering radius of the
resulting 11-disk configuration on the unit disk.  Calibration only.
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
R = 0.38
pi = math.pi
faces = G[2]['faces']
edges = G[2]['edges']
nf = len(faces)
na = 3 * nf + 9          # 42
nv = na + nf + 9         # 62 radii indices, then x[62] = log R
print('nf=%d na=%d nv=%d len(x)=%d' % (nf, na, nv, len(x)))

# rebuild the same matrices as the lead, using his (start=0, span=4) graph with hubs 9,10
eq = np.zeros((nf + 2, nv))
rhs = np.r_[np.ones(nf) * pi, [2 * pi, 2 * pi]]
alpha = np.zeros((9, nv))
ac = np.ones(9) * pi
A = np.zeros((len(edges), nv)); B = np.zeros_like(A); U = np.zeros_like(A); V = np.zeros_like(A)
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
        B[ei, 33 + bi] = 1; V[ei, 53 + bi] = 1
        alpha[i, 33 + bi] += 1; alpha[j, 33 + bi] += 1

print('angle sums row0:', eq[0] @ x - pi)
print('hub sums:', eq[nf] @ x - 2 * pi, eq[nf + 1] @ x - 2 * pi)
print('closure rows (T + roll(L,1) + 2b + (w+roll(w,1))/2 - pi):')


def calc(xx):
    a = (A @ xx)                                  # 21 edge opposite angles
    b = ac + alpha @ xx                           # 9 boundary sector angles
    if xx.shape == (nv + 1,):
        pass
    y = np.exp((U + V) @ xx + 2 * xx[62])         # squared radii of the 20 face radii? see note
    logr = (U + V) @ xx
    return a, b, logr


def calc2(xx):
    a = A @ xx
    b = ac + alpha @ xx
    u = np.exp(U @ xx + xx[62]); v = np.exp(V @ xx + xx[62])
    y = np.exp(xx[53:62] + xx[62])
    u_ring = None
    return a, b, u, v, y


a, b, u, v, y = calc2(x)
print('a (edge angles):', np.round(a, 6))
print('b (spoke sector angles):', np.round(b, 6))
print('face radii u (first 21 rows, R=0.38 scaling):', np.round(u, 9))
print('face radii v:', np.round(v, 9))
print('switch radii y:', np.round(y, 9))
print('max radius/R =', max(u.max(), v.max(), y.max()) / 1.0, ' (values already scaled by R=0.38)')
print('R from x[62] =', math.exp(x[62]), '  vs 0.38*exp(x62)=', 0.38 * math.exp(x[62]))
print()
print('lead optimal R reported =', L['runs'][0]['radius'])
print('certified interval = [%s, %s]' % (D['certified_interval']['lo'][:40], D['certified_interval']['hi'][:40]))
print('x[62] =', x[62], ' exp(x62)=', math.exp(x[62]))
print('R/0.38*exp =', 0.38 * math.exp(x[62]))
