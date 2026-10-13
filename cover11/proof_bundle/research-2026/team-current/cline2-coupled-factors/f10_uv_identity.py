"""cline2-coupled-factors f10: is the endpoint-copy equality u_i = v_i an exact identity?

The saved certified candidate has u_k = v_k to 3.3e-16 for all nine ring sectors (f8).
If that is an identity for every legal inward-root representative, the dual can add the
EQUALITY row u_i - v_i = 0 with a free multiplier, which removes the split
(-z_rr(2i) u^2 - z_rr(2i+1) v^2) into (-z_rr(2i)) (u^2+v^2), a strictly stronger row.

This script tests the identity numerically on a large random family of genuine diagrams
built only from the geometric definitions, and reports the worst |u-v|.

Geometric definitions used (all from the saved normalized model):
  slot k owns the arc from switch P_{k-1} to switch P_k;
  u_k = |P_{k-1}-c_k|/r, v_k = |P_k-c_k|/r,  w_k = arc width;
  a switch is a boundary point equidistant (distance r) from its two sites.
"""
import numpy as np, math, json
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
rng = np.random.default_rng(20260924)
pi = math.pi
r = 0.38

worst = 0.0; arg = None; n = 0
recs = []
for trial in range(200000):
    # random 9 ring sites in the annulus [sqrt(1-r^2)... ] no: inward-root means |c|<=sqrt(1-r^2)
    ang = np.sort(rng.uniform(0, 2*pi, 9))
    rad = rng.uniform(0.45, math.sqrt(1-r*r)*0.999, 9)
    c = np.stack([rad*np.cos(ang), rad*np.sin(ang)], 1)
    # consecutive boundary switches: unit-circle points at distance r from both sites
    ok = True; us = []; vs = []; ws = []
    Pt = []
    for k in range(9):
        a = c[k]; b = c[(k+1) % 9]
        m = (a+b)/2; d = b-a
        nv = np.array([-d[1], d[0]]); nv /= np.linalg.norm(nv)
        # points p with |p|=1 and |p-a|=|p-b| lie on the line m + t nv
        Bc = 2*m @ nv; Cc = m @ m-1
        disc = Bc*Bc-4*Cc
        if disc <= 0:
            ok = False; break
        cand = [m+t*nv for t in (-Bc+np.array([1.0, -1.0])*math.sqrt(disc))/2]
        # pick the one with |p-a| == r  (i.e. the actual switch)
        good = [p for p in cand if abs(np.linalg.norm(p-a)-r) < 1e-3]
        if not good:
            ok = False; break
        Pt.append(good[0])
    if not ok:
        continue
    Pt = np.array(Pt)
    # w_k = arc P_{k-1} -> P_k (ccw)
    th = np.unwrap(np.arctan2(Pt[:, 1], Pt[:, 0]))
    W = np.array([(th[k]-th[(k-1) % 9]) + (2*pi if k == 0 else 0) for k in range(9)])
    # u,v per slot
    uu = np.array([np.linalg.norm(Pt[(k-1) % 9]-c[k])/r for k in range(9)])
    vv = np.array([np.linalg.norm(Pt[k]-c[k])/r for k in range(9)])
    if np.any(uu > 1+1e-9) or np.any(vv > 1+1e-9):
        continue
    if abs(W.sum()-2*pi) > 1e-8:
        continue
    n += 1
    dv = np.abs(uu-vv).max()
    if dv > worst:
        worst = dv; arg = (uu.copy(), vv.copy(), W.copy(), c.copy())
    if n % 5000 == 0:
        recs.append((n, worst))
print(f'accepted genuine diagrams: {n}')
print(f'worst max_k |u_k - v_k| = {worst:.3e}')
if arg is not None:
    print('  u =', np.round(arg[0], 12))
    print('  v =', np.round(arg[1], 12))
print('progression (sample count, worst |u-v|):', recs[:10])
np.save(OUT/'uv_identity_probe.npy', np.array(recs))
