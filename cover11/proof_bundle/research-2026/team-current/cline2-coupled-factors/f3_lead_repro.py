"""cline2-coupled-factors f3: line-by-line independent reconstruction of the lead's
q0_closure_dual.py proposer, run on the SAVED z-vector, with three outputs:

  (1) the lead's own reported quantity  const.z + sum_f max_i (vals + M_fi.z),
  (2) a direct dual-FEASIBILITY test of every coefficient row on the real saved
      certified configuration (where every primal constraint is tight/known),
  (3) a decomposition of (1) into const + face + switch + ring contributions.

Written from scratch against the lead's source text, no reuse of my earlier helpers.
"""
import numpy as np, json, math, sys
from pathlib import Path

P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96

row = json.loads((LEAD / 'q0_closure_dual_0_4.json').read_text())
z = np.array(row['z'])
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
assert all(a < b for a, b in edges), 'edges not sorted'
ei = {e: k for k, e in enumerate(edges)}
ne, nf = len(edges), len(faces)
assert (ne, nf) == (21, 11), (ne, nf)

side0, rr0, kap0, lam0, eta0, lin0, cl0 = 11, 32, 50, 71, 72, 73, 112
nz = cl0 + 9
print('nz =', nz)

# adjacency exactly as the lead builds it
adj = {e: [(t, next(k for k in f if k not in e))
           for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
for e in edges:
    assert 1 <= len(adj[e]) <= 2, (e, adj[e])
sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
        {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}

# ---- constant block exactly as certify_q0_closure.py line 110 ----
const = np.zeros(nz)
const[0:9] = pi
const[9:11] = 2*pi
const[kap0:lam0] = pi
const[lam0] = -2*pi
assert const[eta0] == 0
const[cl0:cl0+9] = -pi
Cz = float(const @ z)
print(f'const.z = {Cz:.9f}')

# ---- factor construction exactly as the lead's script ----
aa = np.array([(i*pi/N, j*pi/N, (N-i-j)*pi/N) for i in range(N+1) for j in range(N+1-i)])
factors = []
for t, f in enumerate(faces):
    xx = np.linspace(0, 1, 31)**2
    ang = np.tile(aa, (len(xx), 1)); x = np.repeat(xx, len(aa))
    v = 2*R*R*x*np.prod(np.sin(ang), axis=1)
    M = np.zeros((len(v), nz))
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i)); ee = ei[e]
        sg = 1 if adj[e][0][0] == t else -1
        M[:, i] -= ang[:, k]; M[:, kap0+ee] -= ang[:, k]
        M[:, side0+ee] += sg*x*np.sin(ang[:, k])**2
        M[:, lin0+ee] += sg*np.sqrt(x)*np.sin(ang[:, k])
    factors.append((f'face{t}', v, M))
for bi in range(9):
    i, j = bi, (bi+1) % 9; e = tuple(sorted((i, j))); ee = ei[e]
    assert len(adj[e]) == 1
    b = np.tile(np.linspace(0, pi/2, 4*N+1), 31)
    x = np.repeat(np.linspace(0, 1, 31)**2, 4*N+1)
    v = R*R*x*np.sin(2*b)/2
    M = np.zeros((len(v), nz))
    M[:, cl0+bi] += 2*b
    M[:, i] += b; M[:, j] += b; M[:, kap0+ee] -= b
    M[:, side0+ee] -= x*np.sin(b)**2; M[:, lin0+ee] -= np.sqrt(x)*np.sin(b)
    M[:, rr0+2*i+1] += x; M[:, rr0+2*j] += x
    M[:, lin0+21+2*i+1] += np.sqrt(x); M[:, lin0+21+2*j] += np.sqrt(x)
    factors.append((f'switch{bi}', v, M))
grid = np.array([(a, u, v) for a in np.linspace(0, pi, NA+1)
                 for u in np.linspace(0, 1, NR+1) for v in np.linspace(0, 1, NR+1)])
a, u, v = grid.T
ch = R*np.sqrt(np.maximum(0, u*u+v*v-2*u*v*np.cos(a)))
w = 2*np.arcsin(ch/2)
S = R*R*u*v*np.sin(a)/2 + (w-np.sin(w))/2
left = np.arctan2(v*np.sin(a), u-v*np.cos(a))
right = np.arctan2(u*np.sin(a), v-u*np.cos(a))
for i in range(9):
    M = np.zeros((len(a), nz))
    M[:, cl0+(i-1) % 9] = left + w/2
    M[:, cl0+i] = right + w/2
    M[:, i] = -a
    M[:, rr0+2*i] = -u*u; M[:, rr0+2*i+1] = -v*v
    M[:, lam0] = w
    M[:, lin0+21+2*i] = -u; M[:, lin0+21+2*i+1] = -v
    factors.append((f'ring{i}', S, M))

ub = Cz
print(f'{"factor":10s} {"max(vals+M.z)":>16s} {"argmax":>8s}')
for name, v, M in factors:
    vals = v + M @ z
    j = int(np.argmax(vals)); ub += vals[j]
    print(f'{name:10s} {vals[j]:16.9f} {j:8d}')
print(f'TOTAL (lead reported form) = {ub:.9f}   lead sample_upper = {row["sample_upper"]:.9f}')

# ---- direct feasibility test on the SAVED configuration ----
print('\n--- dual feasibility test at the saved certified configuration ---')
Rp = 0.379983853119838709048518179573429853811597902802
rho = [0.14942849894640002, 0.892521729905327334, 0.272977466357097934,
       0.761798271819979915, 0.761798271775430687, 0.700870053859786043,
       0.700870054167046975, 0.85881093766316644, 0.858810938020323736,
       0.820853262044791348, 0.820853265563645613]
arc2b = [None, 0.879563185851316847, None, 1.04442396932971458, 1.04442396939702426,
         1.14601163121340383, 1.1460116317791296, 0.916665259275717998,
         0.916665259686080867, 0.962557968829425068, 0.962557973306907126]
# hub triangles (9,10,h): from p2_tips, hub-hub-ring triangles with circumradius == R
hhR = {5: 0.321865057899, 6: 0.321865058183}
# ring sectors: alpha, u, v from the saved geometry (owned arcs w_i are given)
W = [0.61886121795187108963, 0.653697482805171132, 0.65369747275257024292,
     0.61886122100748230652, 0.97812041539259229522, 0.52983601032304524243,
     0.72215506164839572311, 0.52983601076243079378, 0.97812041453602765131]
print('sum w =', sum(W), ' 2pi =', 2*pi)


def row_ring(i, al, u_, v_, w_):
    r = np.zeros(nz)
    r[cl0+(i-1) % 9] = np.arctan2(v_*np.sin(al), u_-v_*np.cos(al)) + w_/2
    r[cl0+i] = np.arctan2(u_*np.sin(al), v_-u_*np.cos(al)) + w_/2
    r[i] = -al
    r[rr0+2*i] = -u_*u_; r[rr0+2*i+1] = -v_*v_
    r[lam0] = w_
    r[lin0+21+2*i] = -u_; r[lin0+21+2*i+1] = -v_
    return r


def val_ring(al, u_, v_, w_):
    return Rp*Rp*u_*v_*np.sin(al)/2 + (w_-np.sin(w_))/2


# reconstruct the saved configuration's per-sector (alpha,u,v) from the geometry file
# (alpha_i = angle at ring site i between its two neighbours; u,v = endpoint copies)
import re
txt = (P.parent / 'cline2-sharp-fan' / 'out' / 'p1_geometry.txt').read_text(encoding='utf-8')
print('geometry file lines:', len(txt.splitlines()))
