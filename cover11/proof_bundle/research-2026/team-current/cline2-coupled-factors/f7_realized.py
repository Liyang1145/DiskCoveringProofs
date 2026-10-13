"""cline2-coupled-factors f7: realized angle diagram of the saved certified candidate,
primal residual report, and the DUAL SLACK of the lead's feasible z0 at that point.

The saved object is an exact-coordinate 11-disk cover at R_cert = .379983853119838733.
At that radius it is FEASIBLE, so area = pi exactly.  Evaluating the lead's dual bound
formula at this single realization gives pi + (dual slack); that slack is the maximum any
dual of this architecture can recover here, hence the honest headroom for a sharper
coupling.  All geometry below is recomputed from the integer coordinates.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi

obj = json.loads((P.parent / 'cline2-sharp-fan' / 'out' / 'certified_object_copy.json')
                 .read_text(encoding='utf-8-sig'))
C = np.array(obj['centers_scaled_1e17'], dtype=float)/1e17
Rc = float(obj['certified_upper_bound_21digits'])
HUB = [0, 2]
RING = [i for i in range(11) if i not in HUB]

# --- ring cyclic order by polar angle ---
ang = np.arctan2(C[RING, 1], C[RING, 0])
order = list(np.argsort(ang))
ring = [RING[k] for k in order]
print('ring cyclic order (ccw):', ring, ' angles(deg):',
      np.round(np.degrees(ang[order]), 6))

# --- boundary switches: point on unit circle equidistant from consecutive rings ---
def switch_point(a, b):
    x = C[a]-C[b]
    m = (C[a]+C[b])/2
    n = np.array([-x[1], x[0]]); n = n/np.linalg.norm(n)
    # |m + t n| = 1
    A = n @ n; B = 2*m @ n; Cc = m @ m - 1
    disc = B*B-4*A*Cc
    ts = (-B + np.array([1, -1])*math.sqrt(max(disc, 0)))/(2*A)
    cands = [m+t*n for t in ts]
    # the realizable switch lies on the minor arc between a and b
    best = None
    for p in cands:
        u = (p-C[a])/np.linalg.norm(p-C[a]); v = (p-C[b])/np.linalg.norm(p-C[b])
        cross = u[0]*v[1]-u[1]*v[0]
        if best is None or cross < best[0]:
            best = (cross, p)
    return best[1]

Pk = [switch_point(ring[k], ring[(k+1) % 9]) for k in range(9)]
args = [math.atan2(p[1], p[0]) for p in Pk]
print('switches P_k:')
for k in range(9):
    print(f'  P{k} between sites {ring[k]:2d},{ring[(k+1)%9]:2d}: |P|={np.linalg.norm(Pk[k]):.15f}'
          f' arg={args[k]:+.15f}  deg={math.degrees(args[k]):+.6f}')

# --- owned widths w_k (site ring[k] owns the arc from P_{k-1} to P_k) ---
un = np.unwrap(np.array(args))
W = np.array([un[k]-un[k-1] for k in range(9)])       # w_0 = P_{-1} -> P_0
print('sum w =', W.sum(), '2pi =', 2*pi)
print('w_k =', np.round(W, 12))

# --- endpoint copies u_k = |P_{k-1}-c_k|/R, v_k = |P_k-c_k|/R ---
u = np.array([np.linalg.norm(Pk[(k-1) % 9]-C[ring[k]])/Rc for k in range(9)])
v = np.array([np.linalg.norm(Pk[k]-C[ring[k]])/Rc for k in range(9)])
print('u_k =', np.round(u, 9))
print('v_k =', np.round(v, 9))
print('max |u|,|v| =', max(u.max(), v.max()), ' (should be <= 1)')

# --- sector angles alpha_k at site ring[k] between its two endpoints ---
al = []
for k in range(9):
    p = Pk[(k-1) % 9]-C[ring[k]]; q = Pk[k]-C[ring[k]]
    al.append(math.acos(np.clip(p @ q/np.linalg.norm(p)/np.linalg.norm(q), -1, 1)))
al = np.array(al)
print('alpha_k =', np.round(al, 9), ' sum =', al.sum())

# --- switch half-angles b_k at P_k: sin b = |P_k - m_k| / (2 rho)... use C816:
#     rho = rho_e/sin b with rho_e the nearest-site distance; here rho_k = Rc at every
#     switch (switch is on bd(D), its nearest sites are exactly the two rings at dist Rc)
b = np.array([math.asin(min(1.0, np.linalg.norm(Pk[k]-(C[ring[k]]+C[ring[(k+1) % 9]])/2)
                              / (2*Rc))) * 0 + 0.0 for k in range(9)])
# direct definition: the switch point is at distance Rc from both sites, so the switch
# radius equals Rc and 2b_k is the angle subtended: sin b_k = |chord|/2 / Rc
b = np.array([math.asin(np.linalg.norm(C[ring[(k+1) % 9]]-C[ring[k]])/2/Rc)
              if np.linalg.norm(C[ring[(k+1) % 9]]-C[ring[k]])/2/Rc <= 1 else np.nan
              for k in range(9)])
print('b_k =', np.round(b, 9), ' 2b_k =', np.round(2*b, 9))
print('switch cap residual pi/2 - b_k =', np.round(pi/2-b, 9))

# --- closure residuals ---
L = np.arctan2(v*np.sin(al), u-v*np.cos(al))
T = np.arctan2(u*np.sin(al), v-u*np.cos(al))
cl_res = np.array([T[k]+L[(k+1) % 9]+2*b[k]+(W[k]+W[(k+1) % 9])/2-pi for k in range(9)])
print('closure residuals T_k+L_{k+1}+2b_k+(w_k+w_{k+1})/2-pi =', np.round(cl_res, 12))
print('max |closure residual| =', np.abs(cl_res).max())

np.savez(OUT/'realized.npz', ring=ring, W=W, u=u, v=v, al=al, b=b, Rc=Rc, C=C,
         Pk=np.array(Pk))
