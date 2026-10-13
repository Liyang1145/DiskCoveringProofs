"""root-cc2 stress-audit: explicit energy along the certificate's test path (clean).

The witnesses x_f are EQUILIBRIUM points of the triangle they belong to (barycentric
points of the three sites), not centroids; the earlier draft wrongly used centroids.

This script builds the path exactly as stress_obstruction_certificate.py describes
(anchor angles theta_k + eps*v_k, free nodes linear with the stored velocities, X sites
rotating with their anchors, witnesses frozen), evaluates the explicit weighted energy,
and compares with the certified second variation.  It also reports the gap-sum invariant.
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
def lo_(ivl):
    fr = Q(ivl.lo, S); return mp.mpf(fr.numerator)/fr.denominator
def hi_(ivl):
    fr = Q(ivl.hi, S); return mp.mpf(fr.numerator)/fr.denominator

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
g = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
outcert = json.loads((LEAD / 'stress-obstruction-certificate.json').read_text())
keep_faces = [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)]
faces = g['faces']
orbits = outcert['orbits']
var = {i: j for j, orb in enumerate(orbits) for i in orb}

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

# witnesses = area coordinates (beta) of each tight triangle  ->  equilibrium points
W = {}; edges = []; beta_of = {}
for f in keep_faces:
    ids = faces[f]['ids']; p, q, v = [C[i] for i in ids]
    w = solve_iv([[2*(q[j]-p[j]) for j in range(2)], [2*(v[j]-p[j]) for j in range(2)]],
                 [norm(q)-norm(p), norm(v)-norm(p)])
    beta = solve_iv([[C[i][0] for i in ids], [C[i][1] for i in ids], [I(1)]*3], [*w, I(1)])
    W[f] = w; beta_of[f] = beta
    for i, bb in zip(ids, beta):
        edges.append((10+i, 24+f, var[f], bb))
keep = keep_faces + [14 + j for j, (k, i) in
                     enumerate((k, i) for k, xx in enumerate(g['anchors']) for i in xx['owners'])
                     if i not in (8, 9)]
idx = 14
for k, anchor in enumerate(g['anchors']):
    for i in anchor['owners']:
        if idx in keep:
            edges.append((k, 10+i, var[idx], I(1)))
        idx += 1
rows = []
for i in range(14):
    for axis in range(2):
        row = [I(0) for _ in range(6)]
        for u, v_, j, bb in edges:
            if u == 10+i:
                row[j] += bb*(C[i][axis] - (anc[v_][axis] if v_ < 10 else (C[v_-10][axis] if v_ < 24 else W[v_-24][axis])))
            elif v_ == 10+i:
                row[j] += bb*(C[i][axis] - (anc[u][axis] if u < 10 else (C[u-10][axis] if u < 24 else W[u-24][axis])))
        rows.append(row)
rows.append([I(int(j == 0)) for j in range(6)])
chosen = outcert['selected_equilibrium_rows']
weights = solve_iv([rows[i] for i in chosen], [I(int(i == 28)) for i in chosen])
Wm = [mf(w) for w in weights]

ang = [mp.mpf(x) for x in outcert['rational_anchor_angular_velocities']]
fv = {int(k): [mf(I(int(Q(vv[t][0])*S), int(Q(vv[t][1])*S), True)) for t in range(2)]
      for k, vv in outcert['free_velocity_dyadic'].items()}
# X site rotation: find for each X centre the angular velocity of its anchor neighbours
xrot = {}
for i in (8, 9, 10, 11):
    nb = [u for u, v_, j, bb in edges if (u == 10+i and v_ < 10)] + \
         [v_ for u, v_, j, bb in edges if (v_ == 10+i and u < 10)]
    xrot[i] = ang[nb[0]] if nb else mp.mpf(0)

def path_pos(eps):
    pos = {}
    for k, p in enumerate(anc):
        r0 = mp.sqrt(mf(p[0])**2 + mf(p[1])**2)
        th = mp.atan2(mf(p[1]), mf(p[0])) + eps*ang[k]
        pos[k] = (mp.cos(th)*r0, mp.sin(th)*r0)
    for i in range(14):
        base = (mf(C[i][0]), mf(C[i][1]))
        if 10+i in fv:
            pos[10+i] = tuple(base[t] + eps*fv[10+i][t] for t in range(2))
        elif i in xrot:
            r0 = mp.hypot(*base); th0 = mp.atan2(base[1], base[0]) + eps*xrot[i]
            pos[10+i] = (mp.cos(th0)*r0, mp.sin(th0)*r0)
        else:
            pos[10+i] = base
    for f in keep_faces:
        pos[24+f] = (mf(W[f][0]), mf(W[f][1]))
    return pos

def energy(eps):
    pos = path_pos(eps)
    tot = mp.mpf(0)
    for u, v_, j, bb in edges:
        w = Wm[j]*mf(bb)
        tot += w*((pos[u][0]-pos[v_][0])**2 + (pos[u][1]-pos[v_][1])**2)
    return tot

P('=' * 78)
P('(0) consistency with the certificate')
P('   normalized weights (mid): %s' % ['%.6f' % x for x in Wm])
P('   certificate weights      : %s' % outcert['normalized_weight_enclosures'][0])
e0 = energy(0)
r2 = mf(r_i)**2
P('   E(0) = %s   r^2 = %s' % (mp.nstr(e0, 18), mp.nstr(r2, 18)))
P('')
P('(1) explicit energy along the certificate path (before any correction)')
for eps in ('1e-4', '1e-3', '1e-2'):
    ee = mp.mpf(eps)
    e1 = energy(ee); em1 = energy(-ee)
    P('   eps=%-6s E(+eps)=%.15f  E(-eps)=%.15f  [E(+)+E(-)-2E0]/eps^2=%.6f'
      % (eps, float(e1), float(em1), float((e1 + em1 - 2*e0)/(ee*ee))))
P('   certified second variation (their computation) = -0.1445582359335557')
P('')
P('(2) the feasibility invariant along this path')
th0 = [mp.atan2(mf(p[1]), mf(p[0])) for p in anc]
for eps in ('0', '1e-4', '1e-3', '1e-2'):
    ee = mp.mpf(eps)
    tt = [th0[k] + ee*ang[k] for k in range(10)]
    gaps = [(tt[(k+1) % 10] - tt[k]) % (2*mp.pi) for k in range(10)]
    P('   eps=%-6s sum(gaps)-2pi = %+.6e   min gap = %.6f deg   max gap = %.6f deg'
      % (eps, float(sum(gaps) - 2*mp.pi), float(mp.degrees(min(gaps))), float(mp.degrees(max(gaps)))))
P('   (sum(gaps) is invariant only if sum_k v_k = 0; here sum_k v_k = %s)' % mp.nstr(sum(ang), 10))

(OUT / 'path03_empirical.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'path03_empirical.txt')
