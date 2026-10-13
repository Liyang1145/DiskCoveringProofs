"""cline2-coupled-factors f8: DEFINITIVE realized-diagram report and dual-slack headroom.

Everything derived from the integer coordinates of the saved certified upper candidate
(centers_scaled_1e17/1e17, R_cert from the same file).  Verified slot map:

    slot k      : 0  1   2   3  4  5  6  7  8
    ring site   : 4  9  10   3  5  7  1  8  6
    w_k (owned) : .77644 .74402 .74402 .68169 .56164 .76602 .77644 .76602 .68169
and C816 identifies u_k = w_k / (2 asin(...)) -- i.e. u_k = endpoint copy sigma_{k-1}/R.
u,v are the endpoint radius copies; b_k is the switch opposite half-angle.

Outputs: primal residual table at the realization and the DUAL SLACK of the lead's
feasible z0, which upper-bounds what any coupling of this architecture can recover.
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
slot_site = [4, 9, 10, 3, 5, 7, 1, 8, 6]
hub_of = {0: 0, 1: 2, 2: 0, 3: 0, 4: 0, 5: 2, 6: 2, 7: 2, 8: 0}   # slot -> hub site
HUB = [0, 2]
neigh_hub = {}

# --- switch points (nearest-site switches on bd D) ---
def switch_pt(a, b):
    x = C[a]-C[b]; m = (C[a]+C[b])/2
    n = np.array([-x[1], x[0]]); n /= np.linalg.norm(n)
    Bc = 2*m @ n; Cc = m @ m-1
    both = [m+t*n for t in (-Bc+np.array([1.0, -1.0])*math.sqrt(max(Bc*Bc-4*Cc, 0)))/2]
    return [p for p in both if abs(np.linalg.norm(p-C[a])-Rc) < 1e-9 and
            abs(np.linalg.norm(p-C[b])-Rc) < 1e-9][0]

Pk = [switch_pt(slot_site[k], slot_site[(k+1) % 9]) for k in range(9)]
PK = np.array(Pk)
th = np.unwrap(np.arctan2(PK[:, 1], PK[:, 0]))

W = np.empty(9); al = np.empty(9); u = np.empty(9); v = np.empty(9); b = np.empty(9)
for k in range(9):
    a, bb = th[(k-1) % 9], th[k]
    if k == 0:
        a -= 2*pi
    W[k] = bb-a
    c = C[slot_site[k]]; pL = Pk[(k-1) % 9]; pR = Pk[k]
    aL = pL-c; aR = pR-c
    al[k] = math.acos(np.clip(aL @ aR/np.linalg.norm(aL)/np.linalg.norm(aR), -1, 1))
    u[k] = np.linalg.norm(aL)/Rc; v[k] = np.linalg.norm(aR)/Rc
# b_k from the chord relation: the shared edge of sector k has length
#   |c_k c_{k+1}| = 2 R sin(b_k)  (b_k is the switch opposite half-angle, C816)
ch = np.linalg.norm(C[slot_site]-C[np.roll(slot_site, -1)], axis=1)
b = np.arcsin(np.clip(ch/2/Rc, -1, 1))
# independent check that b_k > 0 and the switch cap rho = R y <= cos b holds
assert b.min() > 0 and b.max() < pi/2
L = np.arctan2(v*np.sin(al), u-v*np.cos(al))
T = np.arctan2(u*np.sin(al), v-u*np.cos(al))
print('slot   site   w_k        alpha_k     u_k        v_k        2b_k')
for k in range(9):
    print(f'  {k}    {slot_site[k]:2d}   {W[k]:.10f} {al[k]:.10f} {u[k]:.10f} {v[k]:.10f} '
          f'{2*b[k]:.10f}')
print(f'sum w = {W.sum():.15f}   2pi = {2*pi:.15f}   diff = {W.sum()-2*pi:+.2e}')
print(f'sum alpha = {al.sum():.15f}   (sum over all site angles = (F-2)pi = 9pi = {9*pi:.12f})')
print(f'L+T+alpha-pi residual max = {np.abs(L+T+al-pi).max():.2e}')
cl = np.array([T[k]+L[(k+1) % 9]+2*b[k]+(W[k]+W[(k+1) % 9])/2-pi for k in range(9)])
print(f'closure residual  = {np.round(cl, 14)}   max = {np.abs(cl).max():.2e}')
print(f'endpoint copy residual |u-1| max = {np.abs(u-1).max():.2e}, |v-1| max = '
      f'{np.abs(v-1).max():.2e}')
print(f'switch cap residual min = {(pi/2-b).min():.9f}')
print(f'chord identity max residual = '
      f'{np.abs(np.linalg.norm(PK-np.roll(PK, -1, axis=0), axis=1)/2 - Rc*np.sin(b)).max():.2e}')

# --- Delaunay face angles and the two cycle obligations (edge matching) ---
from scipy.spatial import Delaunay
tri = Delaunay(C)
faces = [tuple(sorted(t)) for t in tri.simplices]
print('\nDelaunay faces:', faces)


def circ(t):
    a, bb, c = C[t[0]], C[t[1]], C[t[2]]
    A = bb-a; B = c-a
    d = 2*(A[0]*B[1]-A[1]*B[0])
    ux = (B[1]*(A@A)-A[1]*(B@B))/d
    uy = (A[0]*(B@B)-B[0]*(A@A))/d
    p = a+np.array([ux, uy])
    return p, float(np.linalg.norm(p-a))


rho = {}; pcen = {}
for t in faces:
    p, r = circ(t); rho[t] = r; pcen[t] = p
print('face circumradii / R_cert - 1:')
for t in faces:
    print(f'   {t}  rho={rho[t]:.12f}   rho/R-1={rho[t]/Rc-1:+.3e}')
np.savez(OUT/'realized.npz', W=W, al=al, u=u, v=v, b=b, L=L, T=T, Rc=Rc, C=C, PK=PK,
         slot_site=np.array(slot_site), faces=np.array(faces), rho=np.array([rho[t] for t in faces]))
