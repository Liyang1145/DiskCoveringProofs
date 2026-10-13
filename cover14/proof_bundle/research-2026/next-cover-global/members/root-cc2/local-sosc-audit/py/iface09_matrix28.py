"""root-cc2 local-sosc-audit: reproduce the certificate's 5x28 matrix and test its weights.

Builds G[k][j] = sum_{contacts m in orbit k} d f_m / d x_j for all 28 coordinate
directions, using the certificate's own contact functions and its branch convention
(sign chosen by the certificate's own rule), then:
  * solves the 5x5 on its selected rows and compares with the published weights;
  * tests sum_k w_k G[k][j] for every j.
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

mp.mp.dps = 60
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

cert = json.loads((LEAD / 'local-sosc-certificate.json').read_text())
from fractions import Fraction as FR
wl = []
for lo, hi in cert['weight_intervals']:
    aa = FR(lo); bb = FR(hi)
    wl.append((mp.mpf(aa.numerator)/aa.denominator + mp.mpf(bb.numerator)/bb.denominator)/2)
root = json.loads((LEAD / 'root-integer-certificate.json').read_text())
zb, cb, rb = [I(int(Q(a)*S), int(Q(b)*S), True) for a, b in root['box_dyadic']]
def mf(x):
    fr = Q(x.lo + x.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator
Z0 = mf(zb); C0 = mf(cb); R0 = mf(rb)
S0 = mp.sqrt(1 - R0*R0); A0 = (S0 + Z0)/2
T0 = R0 + mp.sqrt(R0*R0 - Z0*Z0)
B0 = R0 + mp.sqrt(R0*R0 - (A0 - Z0)**2)
D0 = 1 - mp.sqrt(R0*R0 - C0*C0)
bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
contacts = bary['anchors'] + bary['faces']
orbits = [[0, 4, 5, 9], [1, 3, 6, 8], [2, 7], [10, 13, 16, 19], [12, 15, 18, 21]]
v1 = (1 + A0*A0 + B0*B0 - R0*R0)/2; v2 = (1 + C0*C0 + D0*D0 - R0*R0)/2
det0 = A0*D0 - B0*C0
PX = (v1*D0 - v2*B0)/det0; PY = (A0*v2 - C0*v1)/det0
ref_anchor = [(S0, R0), (PX, PY), (mp.mpf(0), mp.mpf(1)), (-PX, PY), (-S0, R0),
              (-S0, -R0), (-PX, -PY), (mp.mpf(0), mp.mpf(-1)), (PX, -PY), (S0, -R0)]
C0list = [(-A0, -B0), (-A0, B0), (A0, -B0), (A0, B0),
          (C0, -D0), (C0, D0), (-C0, -D0), (-C0, D0),
          (-S0, mp.mpf(0)), (S0, mp.mpf(0)), (Z0, mp.mpf(0)), (-Z0, mp.mpf(0)),
          (mp.mpf(0), -T0), (mp.mpf(0), T0)]

def boundary_pt(p, q, sign):
    dv = [q[k]-p[k] for k in range(2)]
    nn = sum(v*v for v in dv)
    k = (sum(v*v for v in q) - sum(v*v for v in p))/2
    base = [v*k/nn for v in dv]
    rad = mp.sqrt((1 - sum(v*v for v in base))/nn)
    return [base[0] - sign*dv[1]*rad, base[1] + sign*dv[0]*rad]

def boundary_f(p, q, sign):
    pnt = boundary_pt(p, q, sign)
    return sum((pnt[k]-p[k])**2 for k in range(2))

def circum_f(p, q, v):
    u = [q[k]-p[k] for k in range(2)]; w = [v[k]-p[k] for k in range(2)]
    dd = u[0]*w[1] - u[1]*w[0]
    aa = (sum(s2*s2 for s2 in q) - sum(s2*s2 for s2 in p))/2
    bb = (sum(s2*s2 for s2 in v) - sum(s2*s2 for s2 in p))/2
    cx = (aa*w[1]-u[1]*bb)/dd; cy = (u[0]*bb-aa*w[0])/dd
    return (cx-p[0])**2 + (cy-p[1])**2

def branch_for(k, C):
    ids = contacts[k]['owners']
    best = None
    for sgn in (1, -1):
        pnt = boundary_pt(C[ids[0]], C[ids[1]], sgn)
        ref = ref_anchor[k]
        dist = (pnt[0]-ref[0])**2 + (pnt[1]-ref[1])**2
        if best is None or dist < best[0]:
            best = (dist, sgn)
    return best[1]

SIGNS = [branch_for(k, C0list) for k in range(10)]
P('branch signs chosen by the certificate rule: %s' % SIGNS)

def contact_val(k, C):
    e = contacts[k]
    if k < 10:
        ids = e['owners']
        return boundary_f(C[ids[0]], C[ids[1]], SIGNS[k])
    ids = e['ids']
    return circum_f(C[ids[0]], C[ids[1]], C[ids[2]])

def orbit_sum(oi, C):
    return sum(contact_val(k, C) for k in orbits[oi])

P('')
P('=' * 78)
P('(1) the 5x28 matrix by the site-motion convention (all 28 coordinates)')
h = mp.mpf('1e-26')
G = [[None]*28 for _ in range(5)]
for oi in range(5):
    for site in range(14):
        for axis in range(2):
            def val(hh):
                C = [tuple(p) for p in C0list]
                q = list(C[site]); q[axis] = q[axis] + hh
                C[site] = tuple(q)
                return orbit_sum(oi, C)
            G[oi][2*site + axis] = (val(h) - val(-h))/(2*h)

def col(j):
    return [G[k][j] for k in range(5)]

P('    nonzero columns (|.| > 1e-20): %s'
  % [(j, 'xy'[j % 2], j//2) for j in range(28) if max(abs(G[k][j]) for k in range(5)) > mp.mpf('1e-20')])
P('')
P('(2) published weights against every column')
res = []
for j in range(28):
    r = sum(wl[k]*G[k][j] for k in range(5))
    res.append(r)
bad = [(j, r) for j, r in enumerate(res) if abs(r) > mp.mpf('1e-12')]
P('    columns with |residual| > 1e-12: %s' % [(j, mp.nstr(r, 6)) for j, r in bad])
P('    max |residual| = %s' % mp.nstr(max(abs(r) for r in res), 6))
P('    sum of weights = %s' % mp.nstr(sum(wl), 12))
P('')
P('(3) solve the 5x5 on rows [28, 0, 1, 8, 9] with this matrix')
sel = [0, 1, 8, 9]
M = mp.zeros(5, 5)
for i, j in enumerate(sel):
    for k in range(5):
        M[i, k] = G[k][j]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    M[4, k] = nn
P('    det = %s' % mp.nstr(mp.det(M), 14))
if mp.det(M) != 0:
    sol = mp.lu_solve(M, mp.matrix([0, 0, 0, 0, 1]))
    P('    solution:  %s' % [mp.nstr(x, 10) for x in sol])
    P('    published: %s' % [mp.nstr(x, 10) for x in wl])
    P('    all positive (mine): %s ; (published): %s'
      % (all(x > 0 for x in sol), all(x > 0 for x in wl)))
P('')
P('(4) does ANY positive weight vector annihilate all 28 columns? (least squares)')
Mt = mp.matrix([[G[k][j] for k in range(5)] for j in range(28)])
sol_ls, resid_norm = mp.qr_solve(Mt, mp.matrix([0]*28))[:2] if False else (None, None)
A = Mt.T*Mt
b = mp.matrix([0]*5)
wls = mp.lu_solve(A + mp.eye(5)*mp.mpf('1e-30'), b)
P('    least-squares solution (singular normal matrix): %s' % [mp.nstr(x, 8) for x in wls])
P('    sum = %s' % mp.nstr(sum(wls), 8))
vals = [sum(wls[k]*G[k][j] for k in range(5)) for j in range(28)]
P('    max |residual| of that vector: %s' % mp.nstr(max(abs(v) for v in vals), 6))

(OUT / 'iface09_matrix28.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface09_matrix28.txt')
