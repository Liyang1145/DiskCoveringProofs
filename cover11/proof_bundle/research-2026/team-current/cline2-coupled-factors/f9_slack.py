"""cline2-coupled-factors f9: dual slack of the lead's feasible z0 at the sharp point.

The saved certified candidate is FEASIBLE at R_cert = .379983853119838733, so its area is
exactly pi (the primal objective).  Evaluating the lead's dual bound formula at this one
realization gives
     const.z0 + sum_f <row_f(z0), realization>  =  pi + (dual slack),
and since each factor's max dominates its realized value, ub(z0) >= pi + slack.  Hence
the slack is the share of the gap pi..ub(z0) that is FORCED by this realization; the
remaining part, ub(z0) - (pi+slack), is what a sharper coupling could in principle claw
back at this point.

All rows are the lead's own coefficients (q0_closure_dual.py / certify_q0_closure.py),
evaluated on the verified realized diagram of f8_realized2.py.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi
R = 19/50

d = np.load(OUT/'realized.npz', allow_pickle=True)
C = d['C']; RK = float(d['Rc']); W = d['W']; al = d['al']; u = d['u']; v = d['v']
slot_site = d['slot_site']; PK = d['PK']
# The q0(6,7) JSON labels ring sites 0..8 in CYCLIC order; the physical site of slot k is
# slot_site[k] = [4,9,10,3,5,7,1,8,6][k].  Faces are therefore taken verbatim from the JSON.
row = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
deg = {}
for f in faces:
    for k in range(3):
        e = tuple(sorted((f[k], f[(k+1) % 3])))
        deg[e] = deg.get(e, 0)+1
print('edge degree pattern:', {v: list(deg.values()).count(v) for v in set(deg.values())})
assert len(deg) == 21 and sorted(deg.values()) == [1]*9+[2]*12
print('q0(6,7) face list consistent: 21 edges, 9 boundary + 12 internal')
# corrected switch half-angles from the chord relation
ch = np.linalg.norm(C[slot_site]-C[np.roll(slot_site, -1)], axis=1)
b = np.arcsin(np.clip(ch/2/RK, -1, 1))
L = np.arctan2(v*np.sin(al), u-v*np.cos(al))
T = np.arctan2(u*np.sin(al), v-u*np.cos(al))
print('closure residual max =', np.abs(T+L[np.r_[1:9, 0]]+2*b+(W+W[np.r_[1:9, 0]])/2-pi).max())

z = np.array(row['z'])
base = np.zeros(121)
base[0:9] = pi; base[9:11] = 2*pi; base[50:71] = pi; base[71] = -2*pi; base[112:121] = -pi
CZ = float(base @ z)
print(f'const.z0 = {CZ:.9f}')

# --- edges and adjacency of the q0(6,7) graph ---
edges = sorted(tuple(e) for e in row['edges'])
ej = {e: k for k, e in enumerate(edges)}
edge_faces = {e: [t for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
sgn = {e: ({} if len(edge_faces[e]) == 1 else
           {edge_faces[e][0]: 1.0, edge_faces[e][1]: -1.0}) for e in edges}
for e in edges:
    if len(edge_faces[e]) == 1:
        sgn[e] = {edge_faces[e][0]: 1.0}


def angle_at(t, site):
    o = [x for x in t if x != site]
    a = C[o[0]]-C[site]; bb = C[o[1]]-C[site]
    return math.acos(np.clip(a @ bb/np.linalg.norm(a)/np.linalg.norm(bb), -1, 1))


def circum(t):
    a, bb, c = C[t[0]], C[t[1]], C[t[2]]
    A = bb-a; B = c-a
    dd = 2*(A[0]*B[1]-A[1]*B[0])
    ux = (B[1]*(A@A)-A[1]*(B@B))/dd; uy = (A[0]*(B@B)-B[0]*(A@A))/dd
    p = a+np.array([ux, uy])
    return p, float(np.linalg.norm(p-a))


# --- evaluate every row at the realization ---
tot = CZ
report = []
HUBSITE = {9: 0, 10: 2}

def site(lab):
    return C[int(slot_site[lab])] if lab < 9 else C[HUBSITE[lab]]
def circum_lab(f):
    a, bb, c = site(f[0]), site(f[1]), site(f[2])
    A = bb-a; B = c-a
    dd = 2*(A[0]*B[1]-A[1]*B[0])
    ux = (B[1]*(A@A)-A[1]*(B@B))/dd; uy = (A[0]*(B@B)-B[0]*(A@A))/dd
    p = a+np.array([ux, uy])
    return p, float(np.linalg.norm(p-a))
def angle_at_lab(f, lab):
    o = [x for x in f if x != lab]
    a = site(o[0])-site(lab); bb = site(o[1])-site(lab)
    return math.acos(np.clip(a @ bb/np.linalg.norm(a)/np.linalg.norm(bb), -1, 1))
for t, f in enumerate(faces):
    p, rho = circum_lab(f)
    xr = (rho/RK)**2
    val = 2*R*R*xr*math.prod([math.sin(angle_at_lab(f, s)) for s in f])
    r = np.zeros(121)
    for i in f:
        e = tuple(sorted(j for j in f if j != i)); k = ej[e]
        sg = sgn[e][t]
        r[i] -= angle_at_lab(f, i); r[50+k] -= angle_at_lab(f, i)
        r[11+k] += sg*xr*math.sin(angle_at_lab(f, i))**2
        r[73+k] += sg*math.sqrt(xr)*math.sin(angle_at_lab(f, i))
    tot += val + r @ z
    report.append((f'face{t} {f}', val + r @ z, xr))
for k in range(9):
    i, j = k, (k+1) % 9          # slots labels 0..8 are the ring sites in cyclic order
    e = tuple(sorted((i, j))); kk = ej[e]
    bb = b[k]
    val = R*R*math.sin(2*bb)/2
    r = np.zeros(121)
    r[i] += bb; r[j] += bb; r[50+kk] -= bb; r[112+k] += 2*bb
    r[11+kk] -= math.sin(bb)**2; r[73+kk] -= math.sin(bb)
    r[32+2*i+1] += 1.0; r[32+2*j] += 1.0
    r[94+2*i+1] += 1.0; r[94+2*j] += 1.0
    tot += val + r @ z
    report.append((f'switch{k} w={W[k]:.6f}', val + r @ z, math.cos(bb)**2))
for k in range(9):
    a_, u_, v_ = al[k], u[k], v[k]
    w_ = W[k]
    S = R*R*u_*v_*math.sin(a_)/2 + (w_-math.sin(w_))/2
    r = np.zeros(121)
    r[112+(k-1) % 9] += L[k]+w_/2
    r[112+k] += T[k]+w_/2
    r[k] -= a_
    r[32+2*k] -= u_*u_; r[32+2*k+1] -= v_*v_
    r[71] += w_
    r[94+2*k] -= u_; r[94+2*k+1] -= v_
    tot += S + r @ z
    report.append((f'ring{k} site{slot_site[k]}', S + r @ z, None))

print(f'\n=== realized-value sum: const.z0 + sum_f <row> = {tot:.9f}')
print(f'    pi = {pi:.9f}      DUAL SLACK at this point = {tot-pi:+.3e}')
print(f'    lead reported ub(z0) = 3.175702558  ->  forced share = {tot-pi:.3e},')
print(f'    recoverable by a sharper coupling at this point = {3.175702557547944-tot:+.3e}')
print('\nper-factor realized contribution:')
for n, val, extra in report:
    print(f'   {n:24s} {val: .9f}' + (f'   x={extra:.9f}' if extra else ''))
