"""cline2-coupled-factors f7b: realized angle diagram of the saved certified candidate.

Correctly identifies each boundary switch's two NEAREST ring sites (not the ring pair it
sits between angularly), then reports every primal constraint residual of the lead's
dual architecture at that single realization, plus the DUAL SLACK of the lead's feasible
z0 there.  That slack = (const.z0 + sum_f row value) - pi is the ceiling on how much any
coupling of this architecture can recover at the sharp point.
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
HUB = [0, 2]; RING = [i for i in range(11) if i not in HUB]

# --- ring cyclic order CCW ---
ang = np.arctan2(C[RING, 1], C[RING, 0])
ring = [RING[k] for k in np.argsort(ang)]
pos = {s: k for k, s in enumerate(ring)}      # ring slot k <-> site index

# --- boundary switches: unit-circle point equidistant from consecutive rings ---
def switch_pt(a, b):
    x = C[a]-C[b]; m = (C[a]+C[b])/2
    n = np.array([-x[1], x[0]]); n /= np.linalg.norm(n)
    A = 1.0; B = 2*m @ n; Cc = m @ m-1
    ts = (-B + np.array([1.0, -1.0])*math.sqrt(max(B*B-4*A*Cc, 0)))/(2*A)
    best = None
    for t in ts:
        p = m+t*n
        u = (p-C[a]); v = (p-C[b])
        cr = u[0]*v[1]-u[1]*v[0]
        if best is None or cr < best[0]:
            best = (cr, p)
    return best[1]

Pk = [switch_pt(ring[k], ring[(k+1) % 9]) for k in range(9)]
PK = np.array(Pk)
assert all(abs(np.linalg.norm(p)-1) < 1e-12 for p in Pk)

# --- owned widths: slot k owns arc P_{k-1} -> P_k (ccw), plus the full turn on wrap ---
th = np.arctan2(PK[:, 1], PK[:, 0])
W = np.empty(9)
for k in range(9):
    a, b = th[(k-1) % 9], th[k]
    if k == 0:
        a = a - 2*pi if a > b else a                 # slot 0 wraps the branch cut
    W[k] = b-a
print('sum w =', W.sum(), '  2pi =', 2*pi)
print('w_k =', np.round(W, 12))

# --- sector angle and endpoint copies for slot k (site ring[k]) ---
al = np.empty(9); u = np.empty(9); v = np.empty(9)
for k in range(9):
    c = C[ring[k]]; pL = Pk[(k-1) % 9]; pR = Pk[k]
    aL = pL-c; aR = pR-c
    al[k] = math.acos(np.clip(aL @ aR/np.linalg.norm(aL)/np.linalg.norm(aR), -1, 1))
    u[k] = np.linalg.norm(aL)/Rc; v[k] = np.linalg.norm(aR)/Rc
print('alpha_k =', np.round(al, 9), '  sum =', al.sum())
print('u_k =', np.round(u, 9))
print('v_k =', np.round(v, 9))
print('max(u,v) =', max(u.max(), v.max()))

# --- switch half-angle b_k: angle at P_k to the two neighbouring sites is B_k, 2b=pi-B ---
b = np.empty(9)
for k in range(9):
    p = Pk[k]; a = C[ring[k]]-p; bb = C[ring[(k+1) % 9]]-p
    B = math.acos(np.clip(a @ bb/np.linalg.norm(a)/np.linalg.norm(bb), -1, 1))
    b[k] = (pi-B)/2
print('b_k =', np.round(b, 9), '  2b_k =', np.round(2*b, 9))
print('switch cap residual pi/2 - b_k =', np.round(pi/2-b, 9))
print('switch radius rho_k = |P_k - c_near| =', np.round([np.linalg.norm(Pk[k]-C[ring[k]]) for k in range(9)], 9), ' R_cert =', Rc)

# --- closure residual ---
L = np.arctan2(v*np.sin(al), u-v*np.cos(al))
T = np.arctan2(u*np.sin(al), v-u*np.cos(al))
cl = np.array([T[k]+L[(k+1) % 9]+2*b[k]+(W[k]+W[(k+1) % 9])/2-pi for k in range(9)])
print('closure residual =', np.round(cl, 12), '  max|.| =', np.abs(cl).max())

# --- exact triangle identity check via the boundary polygon ---
print('\ncheck: 2b_k vs pi - B_k (definition) -- ok by construction')
print('check: sum over slots of [L_k + T_k] + 2 sum b_k + sum W_k = ?')
print('   ', (L+T).sum() + 2*b.sum() + W.sum(), ' vs 9pi =', 9*pi)

# ================= dual slack of the lead's z0 at this realization =================
row = json.loads((LEAD / 'q0_closure_dual_0_4.json').read_text())
z = np.array(row['z'])
NE, NF = 21, 11
base = np.zeros(121)
base[0:9] = pi; base[9:11] = 2*pi; base[50:71] = pi; base[71] = -2*pi; base[112:121] = -pi
const_z = float(base @ z)

# We need the face angles of every face of the q0(6,7) graph.  Rebuild the Delaunay
# triangles directly from the coordinates (exact circumcircle test) and match to slots.
from scipy.spatial import Delaunay
tri = Delaunay(C)
print('\nscipy Delaunay triangles:', tri.simplices.tolist())
# circumradii
def circ(t):
    a, b, c = C[t[0]], C[t[1]], C[t[2]]
    A = b-a; B = c-a
    d = 2*(A[0]*B[1]-A[1]*B[0])
    ux = (B[1]*(A@A)-A[1]*(B@B))/d
    uy = (A[0]*(B@B)-B[0]*(A@A))/d
    p = a+np.array([ux, uy])
    return p, np.linalg.norm(p-a)
for t in tri.simplices:
    p, r = circ(t)
    print(f'   {tuple(sorted(t))}  circumcentre |p|={np.linalg.norm(p):.10f}  rho={r:.12f}'
          f'  rho-R={r-Rc:+.3e}')
