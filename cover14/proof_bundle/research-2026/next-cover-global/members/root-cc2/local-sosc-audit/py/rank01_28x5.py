"""root-cc2 local-sosc-audit: the exact 28x5 equilibrium matrix and both ranks.

Builds A[j][k] = grad of orbit-k function in the coordinate direction j (site-motion
convention: perturb one centre coordinate, all other centres fixed; for boundary contacts
the switch point is re-solved with the branch fixed at the candidate's sign), then reports
    rank(A) (28 rows x 5 cols) and rank([A; normalization]) (29 x 5),
and compares A's columns with the certificate's own numbers.
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

SIGNS = []
for k in range(10):
    ids = contacts[k]['owners']
    best = None
    for sgn in (1, -1):
        pnt = boundary_pt(C0list[ids[0]], C0list[ids[1]], sgn)
        ref = ref_anchor[k]
        dist = (pnt[0]-ref[0])**2 + (pnt[1]-ref[1])**2
        if best is None or dist < best[0]:
            best = (dist, sgn)
    SIGNS.append(best[1])

def contact_val(k, C):
    e = contacts[k]
    if k < 10:
        ids = e['owners']
        return boundary_f(C[ids[0]], C[ids[1]], SIGNS[k])
    ids = e['ids']
    return circum_f(C[ids[0]], C[ids[1]], C[ids[2]])

def orbit_sum(oi, C):
    return sum(contact_val(k, C) for k in orbits[oi])

h = mp.mpf('1e-26')
A = mp.zeros(28, 5)
for j in range(28):
    site, axis = j//2, j % 2
    for oi in range(5):
        def val(hh):
            C = [tuple(p) for p in C0list]
            q = list(C[site]); q[axis] = q[axis] + hh
            C[site] = tuple(q)
            return orbit_sum(oi, C)
        A[j, oi] = (val(h) - val(-h))/(2*h)

U, Sv, Vt = mp.svd(A)
P('=' * 78)
P('(1) rank of the 28x5 equilibrium matrix A')
P('    singular values: %s' % [mp.nstr(x, 8) for x in Sv])
P('    rank (tol 1e-30): %d' % sum(1 for x in Sv if x > mp.mpf('1e-30')))
B = mp.zeros(29, 5)
for j in range(28):
    for k in range(5):
        B[j, k] = A[j, k]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    B[28, k] = nn
U2, Sv2, Vt2 = mp.svd(B)
P('    rank of [A; normalization] (29x5): %s  singular values %s'
  % (sum(1 for x in Sv2 if x > mp.mpf('1e-30')), [mp.nstr(x, 8) for x in Sv2]))
P('')
P('(2) the null space of the 29x5 system (should be 1-dim, all-positive)')
nul = [Vt2[i, 4] for i in range(5)]
if nul[0] != 0:
    nul = [x/nul[0] for x in nul]
P('    right-null direction of [A; norm]: %s' % [mp.nstr(x, 10) for x in nul])
scaled = [x/sum(nul) for x in nul] if sum(nul) != 0 else nul
P('    normalised to sum 1: %s' % [mp.nstr(x, 10) for x in scaled])
cert = json.loads((LEAD / 'local-sosc-certificate.json').read_text())
from fractions import Fraction as FR
wl = []
for lo, hi in cert['weight_intervals']:
    aa = FR(lo); bb = FR(hi)
    wl.append((mp.mpf(aa.numerator)/aa.denominator + mp.mpf(bb.numerator)/bb.denominator)/2)
P('    published weights:    %s' % [mp.nstr(x, 10) for x in wl])
P('    (the published weights satisfy sum=1 and A^T w = 0 in the certificate)')
P('')
P('(3) which columns are nonzero (effective directions)')
nz = [j for j in range(28) if max(abs(A[j, k]) for k in range(5)) > mp.mpf('1e-20')]
P('    nonzero rows of A: %s' % [(j//2, 'xy'[j % 2]) for j in nz])

(OUT / 'rank01_28x5.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'rank01_28x5.txt')
