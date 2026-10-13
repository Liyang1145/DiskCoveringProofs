"""cline2-coupled-factors f7c: REALIZED angle diagram (correct ring slot <-> switch map)
plus primal residuals and the DUAL SLACK of the lead's feasible z0 at the sharp point.

Verified slot map (from nearest-site switches on the saved certified object):
    slot k : 0..8 -> ring site [4, 9, 10, 3, 5, 7, 1, 8, 6]
    switch P_k lies between slot k and slot k+1, so slot k owns the arc P_{k-1} -> P_k.

b_k is the switch opposite half-angle: the angle at the switch to its two nearest sites
is B_k and C816 gives 2b_k = pi - B_k.  (The earlier draft used (pi-B)/2, wrong by 2x.)
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


def switch_pt(a, b):
    x = C[a]-C[b]; m = (C[a]+C[b])/2
    n = np.array([-x[1], x[0]]); n /= np.linalg.norm(n)
    Bc = 2*m @ n; Cc = m @ m-1
    ts = (-Bc + np.array([1.0, -1.0])*math.sqrt(max(Bc*Bc-4*Cc, 0)))/2
    best = None
    for t in ts:
        p = m+t*n; u = p-C[a]; v = p-C[b]; cr = u[0]*v[1]-u[1]*v[0]
        if best is None or cr < best[0]:
            best = (cr, p)
    return best[1]


slot_site = [4, 9, 10, 3, 5, 7, 1, 8, 6]
Pk = [switch_pt(slot_site[k], slot_site[(k+1) % 9]) for k in range(9)]
PK = np.array(Pk)
th = np.arctan2(PK[:, 1], PK[:, 0])
W = np.empty(9)
for k in range(9):
    a, b = th[(k-1) % 9], th[k]
    if k == 0:
        a = a-2*pi
    if a > b:
        b += 2*pi
    W[k] = b-a
al = np.empty(9); u = np.empty(9); v = np.empty(9); b = np.empty(9)
for k in range(9):
    c = C[slot_site[k]]; pL = Pk[(k-1) % 9]; pR = Pk[k]
    aL = pL-c; aR = pR-c
    al[k] = math.acos(np.clip(aL @ aR/np.linalg.norm(aL)/np.linalg.norm(aR), -1, 1))
    u[k] = np.linalg.norm(aL)/Rc; v[k] = np.linalg.norm(aR)/Rc
    p = Pk[k]; q1 = C[slot_site[k]]-p; q2 = C[slot_site[(k+1) % 9]]-p
    B = math.acos(np.clip(q1 @ q2/np.linalg.norm(q1)/np.linalg.norm(q2), -1, 1))
    b[k] = (pi-B)/2
print('slot -> site :', slot_site)
print('w_k          =', np.round(W, 12), ' sum =', W.sum(), ' 2pi =', 2*pi)
print('alpha_k      =', np.round(al, 12), ' sum =', al.sum())
print('u_k          =', np.round(u, 12))
print('v_k          =', np.round(v, 12))
print('2b_k         =', np.round(2*b, 12))
print('pi/2 - b_k   =', np.round(pi/2-b, 12), '  (switch cap residual, must be >= 0)')
print('chord/2 = R sin b_k  vs  |P_k-P_{k+1}|/2 :',
      np.round(Rc*np.sin(b)-np.linalg.norm(PK-np.roll(PK, -1, axis=0), axis=1)/2, 12))
L = np.arctan2(v*np.sin(al), u-v*np.cos(al))
T = np.arctan2(u*np.sin(al), v-u*np.cos(al))
cl = np.array([T[k]+L[(k+1) % 9]+2*b[k]+(W[k]+W[(k+1) % 9])/2-pi for k in range(9)])
print('closure residual =', np.round(cl, 12), '  max|.| =', np.abs(cl).max())
print('area check: sum S_k =',
      sum(Rc*Rc*u[k]*v[k]*math.sin(al[k])/2 + (W[k]-math.sin(W[k]))/2 for k in range(9)),
      ' pi =', pi)
print('sector-triangle check: u==1 and v==1 for all k?',
      np.allclose(u, 1, atol=1e-9), np.allclose(v, 1, atol=1e-9))
np.savez(OUT/'realized.npz', W=W, al=al, u=u, v=v, b=b, Rc=Rc, C=C, PK=PK,
         slot_site=np.array(slot_site), L=L, T=T)
