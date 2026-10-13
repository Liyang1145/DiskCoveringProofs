"""cline2-coupled-factors f22: verify the exact shared-side identity on the saved object,
and test the feasibility of the lead's z0 in the boxed LP (numerical sanity of f18/f20).
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
LEAD = P.parent / 'lead'
pi = math.pi
R = 19/50

obj = json.loads((P.parent/'cline2-sharp-fan'/'out'/'certified_object_copy.json')
                 .read_text(encoding='utf-8-sig'))
C = np.array(obj['centers_scaled_1e17'], dtype=float)/1e17
Rc = float(obj['certified_upper_bound_21digits'])
row = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
ei = {e: k for k, e in enumerate(edges)}
d = np.load(OUT/'realized.npz', allow_pickle=True)
slot = [int(s) for s in d['slot_site']]
hub = {9: 0, 10: 2}


def site(lab):
    return C[slot[lab]] if lab < 9 else C[hub[lab]]


def circum(f):
    a, b, c = site(f[0]), site(f[1]), site(f[2])
    A = b-a; B = c-a
    dd = 2*(A[0]*B[1]-A[1]*B[0])
    p = a+np.array([(B[1]*(A@A)-A[1]*(B@B))/dd, (A[0]*(B@B)-B[0]*(A@A))/dd])
    return p, [np.linalg.norm(p-site(s)) for s in f]


def ang_at(f, s):
    o = [x for x in f if x != s]
    u1 = site(o[0])-site(s); u2 = site(o[1])-site(s)
    return math.acos(np.clip(u1 @ u2/np.linalg.norm(u1)/np.linalg.norm(u2), -1, 1))


print('face  circumradius  |p-c| for the three vertices        (must be equal)')
rho = {}
for t, f in enumerate(faces):
    p, ds = circum(f)
    rho[t] = ds[0]
    print(f'  face{t} {str(f):12s} rho={ds[0]:.12f}  radii={np.round(ds, 12)}  '
          f'spread={max(ds)-min(ds):.2e}')

print('\nexact shared-side identity  rho_f sin(A_f) = rho_g sin(B_g)  per internal edge:')
worst = 0.0
for e in edges:
    ts = [t for t, f in enumerate(faces) if e[0] in f and e[1] in f]
    if len(ts) != 2:
        continue
    vals = []
    for t in ts:
        f = faces[t]
        # the angle OPPOSITE the edge e is the one at the remaining vertex
        opp = [s for s in f if s not in e][0]
        vals.append(rho[t]*math.sin(ang_at(f, opp)))
    worst = max(worst, abs(vals[0]-vals[1]))
    print(f'  {str(e):10s} {vals[0]:.12f}  {vals[1]:.12f}   diff={vals[0]-vals[1]:+.2e}')
print(f'worst discrepancy = {worst:.3e}   (exact identity, so this must be ~1e-16)')
