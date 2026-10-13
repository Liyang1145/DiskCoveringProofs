"""root-cc2 stress-audit: the test path's feasibility constraint.

The anchors are ordered on S^1 with gaps g_k = theta_{k+1} - theta_k summing to 2*pi.
Under theta_k(eps) = theta_k + eps*v_k the gap sum becomes 2*pi + eps*(v_0 - v_9) + ..., so
FEASIBILITY REQUIRES sum_k v_k = 0 (not merely v_4 = v_9 = 0).

This script:
 (1) recomputes the certificate's second variation exactly as its script does;
 (2) recomputes it along the *feasibility-corrected* path
     v_k -> v_k - (sum v)/10,  which is the unique uniform rotation making the sum zero
     (and keeps both cap gaps' derivatives at zero);
 (3) recomputes the free-node velocities for the corrected boundary velocities by the
     same Schur/Lagrange condition the certificate presumably intends (minimising the
     elastic energy's first derivative), so the corrected path is admissible.
All with the lead's own integer interval kernel where it matters; the correction is an
exact rational uniform rotation.
"""
import json
import sys
from pathlib import Path
import mpmath as mp
import numpy as np
from fractions import Fraction as QF

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 60
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
sym = json.loads((LEAD / 'stress-symmetry-control.json').read_text())
outcert = json.loads((LEAD / 'stress-obstruction-certificate.json').read_text())

# ---- rebuild the certificate's edge/graph structure exactly (its lines 42-67)
keep = [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)] + \
       [14 + j for j, (k, i) in enumerate((k, i) for k, x in enumerate(g['anchors']) for i in x['owners'])
        if i not in (8, 9)]
P('=' * 78)
P('(0) structure')
P('   keep size %d ; selected rows %s' % (len(keep), outcert['selected_equilibrium_rows']))
P('   orbits from the certificate: %s' % outcert['orbits'])
orbits = outcert['orbits']
var = {i: j for j, orb in enumerate(orbits) for i in orb}
faces = g['faces']

def norm(p):
    return sum(x*x for x in p)
def sub(p, q):
    return [x - y for x, y in zip(p, q)]
def solve_int(M, v):
    A = [list(row) + [x] for row, x in zip(M, v)]
    n = len(v)
    for k in range(n):
        piv = next(i for i in range(k, n) if A[i][k].lo*A[i][k].hi > 0)
        A[k], A[piv] = A[piv], A[k]
        q = A[k][k]; A[k] = [x/q for x in A[k]]
        for i in range(n):
            if i == k: continue
            q = A[i][k]; A[i] = [x - q*y for x, y in zip(A[i], A[k])]
    return [row[-1] for row in A]

W = {}; B = {}; edges = []
for f in keep:
    if f >= 14: continue
    ids = faces[f]['ids']; p, q, v = [C[i] for i in ids]
    w = solve_int([[2*(q[j]-p[j]) for j in range(2)], [2*(v[j]-p[j]) for j in range(2)]],
                  [norm(q) - norm(p), norm(v) - norm(p)])
    beta = solve_int([[C[i][0] for i in ids], [C[i][1] for i in ids], [I(1)]*3], [*w, I(1)])
    W[f] = w; B[f] = beta
    for i, bb in zip(ids, beta):
        edges.append((10+i, 24+f, var[f], bb))
idx = 14
for k, anchor in enumerate(g['anchors']):
    for i in anchor['owners']:
        if idx in keep:
            edges.append((k, 10+i, var[idx], I(1)))
        idx += 1
pos = {k: p for k, p in enumerate(anc)}
pos.update({10+k: p for k, p in enumerate(C)})
pos.update({24+k: p for k, p in W.items()})

rows = []
for i in range(14):
    for axis in range(2):
        row = [I(0) for _ in range(6)]
        for u, v_, j, bb in edges:
            if u == 10+i: row[j] += bb*(pos[u][axis] - pos[v_][axis])
            elif v_ == 10+i: row[j] += bb*(pos[v_][axis] - pos[u][axis])
        rows.append(row)
rows.append([I(int(j == 0)) for j in range(6)])
chosen = outcert['selected_equilibrium_rows']
weights = solve_int([rows[i] for i in chosen], [I(int(i == 28)) for i in chosen])
wnum = [float(Q(w.lo + w.hi, 2*S)) for w in weights]
P('   normalized weights (mid): %s' % ['%.6f' % x for x in wnum])

# ---- Laplacian / elastic energy in numeric form (mid of intervals)
used = sorted({x for u, v_, j, bb in edges for x in (u, v_)})
loc = {x: i for i, x in enumerate(used)}
Lm = np.zeros((len(used), len(used)))
for u, v_, j, bb in edges:
    wgt = float(Q(weights[j].lo + weights[j].hi, 2*S))*float(Q(bb.lo + bb.hi, 2*S))
    ii, jj = loc[u], loc[v_]
    Lm[ii, ii] += wgt; Lm[jj, jj] += wgt; Lm[ii, jj] -= wgt; Lm[jj, ii] -= wgt
fi = [loc[i] for i in used if i >= 10]
bi = [loc[i] for i in used if i < 10]
P('   free nodes %s ; boundary nodes %s' % ([i for i in used if i >= 10], [i for i in used if i < 10]))

ang = [QF(0), QF(-1, 4), QF(-2, 3), QF(-13, 12), QF(-4, 3), QF(-4, 3), QF(-13, 12),
       QF(-2, 3), QF(-1, 4), QF(0)]
P('')
P('(1) feasibility constraint sum_k v_k = 0')
P('   sum(ang) = %s = %s' % (sum(ang), float(sum(ang))))
P('   => the certificate\'s angular velocity field does NOT preserve sum(gaps) = 2*pi.')

def boundary_vel(rot):
    """anchor velocity fields for theta_k' = ang_k - rot (rot = uniform rotation)"""
    out = {}
    for k, p in enumerate(anc):
        w = float(Fraction_to_float := 0) if False else float(ang[k]) - rot
        px = float(Q(p[0].lo + p[0].hi, 2*S)); py = float(Q(p[1].lo + p[1].hi, 2*S))
        out[k] = np.array([-w*py, w*px])
    return out

def free_vel(bv):
    rhs = Lm[np.ix_(fi, bi)] @ np.array([bv[i] for i in [x for x in used if x < 10]])
    return np.linalg.solve(Lm[np.ix_(fi, fi)], rhs)

def curvature(bv, fv):
    """exact-formula second variation, as the certificate computes it (float version)"""
    vel = dict(bv)
    for i, val in zip([x for x in used if x >= 10], fv):
        vel[i] = val
    cur = 0.0
    for u, v_, j, bb in edges:
        wgt = float(Q(weights[j].lo + weights[j].hi, 2*S))*float(Q(bb.lo + bb.hi, 2*S))
        term = float(np.sum((vel[u]-vel[v_])**2))
        for (nd, other) in ((u, v_), (v_, u)):
            if nd < 10:
                aa = -float(ang[nd])**2
                pu = np.array([float(Q(pos[nd][t].lo + pos[nd][t].hi, 2*S)) for t in range(2)])
                po = np.array([float(Q(pos[other][t].lo + pos[other][t].hi, 2*S)) for t in range(2)])
                term -= float(ang[nd])**2 * float(np.sum((pu - po)*pu))
        cur += 2*wgt*term
    return cur

bv0 = boundary_vel(0.0)
fv0 = free_vel(bv0)
P('')
P('(2) second variation along the certificate path (rot = 0)')
P('   v_0 - v_9 = %s (gap-sum drift)' % (float(ang[0] - ang[9])))
P('   curvature = %s   (certificate JSON: %s)'
  % ('%.10f' % curvature(bv0, fv0), outcert['second_variation_exact_interval']))

rot_corr = float(sum(ang))/10.0
P('')
P('(3) second variation along the FEASIBILITY-CORRECTED path (rot = %.10f)' % rot_corr)
bvc = boundary_vel(rot_corr)
P('   corrected v: %s' % ['%.6f' % (float(ang[k]) - rot_corr) for k in range(10)])
P('   sum(corrected v) = %.3e' % (sum(float(ang[k]) - rot_corr for k in range(10))))
P('   gap derivatives dg after correction (cap gaps must stay 0): %s'
  % ['%.6f' % ((float(ang[(k+1) % 10]) - rot_corr) - (float(ang[k]) - rot_corr)) for k in range(10)])
fvc = free_vel(bvc)
P('   curvature = %.10f' % curvature(bvc, fvc))

P('')
P('(4) the same two paths, curvature with the certificate\'s own anchor velocities kept')
P('   (i.e. what the certificate actually computes, for comparison):')
P('   curvature (cert)   = %.10f' % curvature(bv0, fv0))

(OUT / 'path01_feasibility.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'path01_feasibility.txt')
