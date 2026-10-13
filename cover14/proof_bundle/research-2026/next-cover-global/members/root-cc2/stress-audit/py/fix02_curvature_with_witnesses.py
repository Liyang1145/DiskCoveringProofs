"""root-cc2 stress-audit: explicit energy along the certificate path, WITH witnesses moving.

This is the interface the lead flagged: stress_obstruction_certificate.py stores velocities
for ALL free central nodes including the face witnesses (24+f) and uses them in its
second-variation sum.  My earlier evaluation froze the witnesses and therefore measured a
different (larger) curvature.  Here the witnesses move linearly with their stored
velocities, exactly as the certificate does.

Outputs: E(0), symmetric second differences for several eps, and the second variation
computed from the certificate's own formula, so the two can be compared.
"""
import json
import sys
from pathlib import Path
import mpmath as mp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 50
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

cert = json.loads((LEAD / 'root-integer-certificate.json').read_text())
X = [I(int(Q(a)*S), int(Q(b)*S), True) for a, b in cert['box_dyadic']]
z_i, c_i, r_i = X
s_i = (1 - r_i*r_i).sqrt(); a_i = (s_i + z_i)/2
t_i = r_i + (r_i*r_i - z_i*z_i).sqrt()
b_i = r_i + (r_i*r_i - (a_i - z_i)**2).sqrt()
d_i = 1 - (r_i*r_i - c_i*c_i).sqrt()
def mf(ivl):
    fr = Q(ivl.lo + ivl.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator
C = [(sx*a_i, sy*b_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(sx*c_i, sy*d_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(-s_i, I(0)), (s_i, I(0)), (z_i, I(0)), (-z_i, I(0)), (I(0), -t_i), (I(0), t_i)]
v1 = (1 + a_i*a_i + b_i*b_i - r_i*r_i)/2
v2 = (1 + c_i*c_i + d_i*d_i - r_i*r_i)/2
det = a_i*d_i - b_i*c_i
px_i = (v1*d_i - v2*b_i)/det
py_i = (a_i*v2 - c_i*v1)/det
anc = [(s_i, r_i), (px_i, py_i), (I(0), I(1)), (-px_i, py_i), (-s_i, r_i),
       (-s_i, -r_i), (-px_i, -py_i), (I(0), I(-1)), (px_i, -py_i), (s_i, -r_i)]
bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
outcert = json.loads((LEAD / 'stress-obstruction-certificate.json').read_text())
faces = bary['faces']
orbits = outcert['orbits']
var = {i: j for j, orb in enumerate(orbits) for i in orb}
keep_faces = [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)]
def norm(p): return sum(x*x for x in p)
def solve_iv(M, v):
    A = [list(r) + [x] for r, x in zip(M, v)]
    n = len(v)
    for k in range(n):
        piv = next(i for i in range(k, n) if A[i][k].lo*A[i][k].hi > 0)
        A[k], A[piv] = A[piv], A[k]
        q = A[k][k]; A[k] = [x/q for x in A[k]]
        for i in range(n):
            if i == k: continue
            q = A[i][k]; A[i] = [x - q*y for x, y in zip(A[i], A[k])]
    return [r[-1] for r in A]
W = {}; edges = []
for f in keep_faces:
    ids = faces[f]['ids']; p, q, v = [C[i] for i in ids]
    w = solve_iv([[2*(q[j]-p[j]) for j in range(2)], [2*(v[j]-p[j]) for j in range(2)]],
                 [norm(q)-norm(p), norm(v)-norm(p)])
    beta = solve_iv([[C[i][0] for i in ids], [C[i][1] for i in ids], [I(1)]*3], [*w, I(1)])
    W[f] = w
    for i, bb in zip(ids, beta):
        edges.append((10+i, 24+f, var[f], bb))
keep = keep_faces + [14 + j for j, (k, i) in
                     enumerate((k, i) for k, xx in enumerate(bary['anchors']) for i in xx['owners'])
                     if i not in (8, 9)]
idx = 14
for k, anchor in enumerate(bary['anchors']):
    for i in anchor['owners']:
        if idx in keep:
            edges.append((k, 10+i, var[idx], I(1)))
        idx += 1
rows = []
for i in range(14):
    for axis in range(2):
        row = [I(0) for _ in range(6)]
        for u, v_, j, bb in edges:
            pu = anc[u] if u < 10 else (C[u-10] if u < 24 else W[u-24])
            pv = anc[v_] if v_ < 10 else (C[v_-10] if v_ < 24 else W[v_-24])
            if u == 10+i: row[j] += bb*(C[i][axis] - pv[axis])
            elif v_ == 10+i: row[j] += bb*(C[i][axis] - pu[axis])
        rows.append(row)
rows.append([I(int(j == 0)) for j in range(6)])
chosen = outcert['selected_equilibrium_rows']
weights = solve_iv([rows[i] for i in chosen], [I(int(i == 28)) for i in chosen])
Wm = [mf(w) for w in weights]

ang = [mp.mpf(x) for x in outcert['rational_anchor_angular_velocities']]
fv = {int(k): [mf(I(int(Q(vv[t][0])*S), int(Q(vv[t][1])*S), True)) for t in range(2)]
      for k, vv in outcert['free_velocity_dyadic'].items()}

def pos_of(j):
    return anc[j] if j < 10 else (C[j-10] if j < 24 else W[j-24])

def path_pos(eps):
    pos = {}
    for k, p in enumerate(anc):
        r0 = mp.sqrt(mf(p[0])**2 + mf(p[1])**2)
        th = mp.atan2(mf(p[1]), mf(p[0])) + eps*ang[k]
        pos[k] = (mp.cos(th)*r0, mp.sin(th)*r0)
    for j in range(10, 24):
        base = (mf(C[j-10][0]), mf(C[j-10][1]))
        v = fv.get(j, [mp.mpf(0), mp.mpf(0)])
        pos[j] = (base[0] + eps*v[0], base[1] + eps*v[1])
    for j in range(24, 38):
        if j-24 not in keep_faces:
            continue
        base = (mf(W[j-24][0]), mf(W[j-24][1]))
        v = fv.get(j, [mp.mpf(0), mp.mpf(0)])
        pos[j] = (base[0] + eps*v[0], base[1] + eps*v[1])
    return pos

def energy(eps):
    pos = path_pos(eps)
    tot = mp.mpf(0)
    for u, v_, j, bb in edges:
        w = Wm[j]*mf(bb)
        tot += w*((pos[u][0]-pos[v_][0])**2 + (pos[u][1]-pos[v_][1])**2)
    return tot

P('=' * 78)
P('(1) explicit energy along the path WITH witnesses moving (certificate interface)')
e0 = energy(0)
r2 = mf(r_i)**2
P('   E(0) = %s ; r^2 = %s ; E(0)-r^2 = %s' % (mp.nstr(e0, 18), mp.nstr(r2, 18), mp.nstr(e0-r2, 6)))
for eps in ('1e-4', '1e-3', '1e-2'):
    ee = mp.mpf(eps)
    e1, em1 = energy(ee), energy(-ee)
    P('   eps=%-6s E(+)=%s E(-)=%s  [E(+)+E(-)-2E0]/eps^2 = %.8f'
      % (eps, mp.nstr(e1, 16), mp.nstr(em1, 16), float((e1+em1-2*e0)/(ee*ee))))
P('   certificate value = -0.1445582359335557')

P('')
P('(2) the certificate second-variation formula evaluated with the same data')
curv = mp.mpf(0)
for u, v_, j, bb in edges:
    w = Wm[j]*mf(bb)
    vu = fv.get(u, [mp.mpf(0), mp.mpf(0)]); vv_ = fv.get(v_, [mp.mpf(0), mp.mpf(0)])
    if u < 10:
        p = (mf(anc[u][0]), mf(anc[u][1])); wu = ang[u]
        vu = [-wu*p[1], wu*p[0]]
    if v_ < 10:
        p = (mf(anc[v_][0]), mf(anc[v_][1])); wv = ang[v_]
        vv_ = [-wv*p[1], wv*p[0]]
    term = (vu[0]-vv_[0])**2 + (vu[1]-vv_[1])**2
    for (nd, other) in ((u, v_), (v_, u)):
        if nd < 10:
            pu = (mf(pos_of(nd)[0]), mf(pos_of(nd)[1]))
            po = (mf(pos_of(other)[0]), mf(pos_of(other)[1]))
            term -= ang[nd]**2*((pu[0]-po[0])*pu[0] + (pu[1]-po[1])*pu[1])
    curv += 2*w*term
P('   2 sum_e W_e [|dv|^2 + (x_u-x_v).(a_u-a_v)] = %.10f' % float(curv))
P('   (same expression the certificate evaluates)')

P('')
P('(3) cross-check: second derivative from the explicit E at even smaller eps')
for eps in ('5e-5', '2e-5'):
    ee = mp.mpf(eps)
    f2 = (energy(ee) - 2*e0 + energy(-ee))/(ee*ee)
    P('   eps=%-6s second difference = %.8f' % (eps, float(f2)))

(OUT / 'fix02_curvature_with_witnesses.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'fix02_curvature_with_witnesses.txt')
