"""root-cc2 local-sosc-audit: KKT identity in the certificate's OWN functions.

The boundary contract is NOT a circle-circle intersection: the code's boundary(p,q,sign)
builds the point on S^1 along the perpendicular bisector of the pair (p,q) and returns the
squared distance from it to p.  This script uses exactly that construction, verifies the
ten boundary contacts equal r^2 at the candidate, then builds the 5x6 orbit-gradient
matrix by the site-motion convention and tests the published weights.
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

def base_centres():
    return [(-A0, -B0), (-A0, B0), (A0, -B0), (A0, B0),
            (C0, -D0), (C0, D0), (-C0, -D0), (-C0, D0),
            (-S0, mp.mpf(0)), (S0, mp.mpf(0)), (Z0, mp.mpf(0)), (-Z0, mp.mpf(0)),
            (mp.mpf(0), -T0), (mp.mpf(0), T0)]

def boundary_pt(p, q, sign):
    """the code's construction: point on S^1 along the perpendicular bisector direction"""
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

def branch(k, C):
    ids = contacts[k]['owners']
    best = None
    for sgn in (1, -1):
        pnt = boundary_pt(C[ids[0]], C[ids[1]], sgn)
        ref = ref_anchor[k]
        dist = (pnt[0]-ref[0])**2 + (pnt[1]-ref[1])**2
        if best is None or dist < best[0]:
            best = (dist, sgn)
    return best[1]

def contact_val(k, C):
    e = contacts[k]
    if k < 10:
        ids = e['owners']
        return boundary_f(C[ids[0]], C[ids[1]], branch(k, C))
    ids = e['ids']
    return circum_f(C[ids[0]], C[ids[1]], C[ids[2]])

P('=' * 78)
P('(0) contact values at the candidate (must be r^2 = %s for every listed contact)'
  % mp.nstr(R0*R0, 14))
Cb = base_centres()
for k in range(24):
    v = contact_val(k, Cb)
    tag = 'B ' if k < 10 else 'T '
    flag = 'OK' if abs(v - R0*R0) < mp.mpf('1e-25') else 'MISMATCH'
    P('    %s contact %2d: %-22s value-r^2 = %-12s %s'
      % (tag, k, str(contacts[k]['owners'] if k < 10 else contacts[k]['ids']),
         mp.nstr(v - R0*R0, 6), flag))

def orbit_sum(oi, C):
    return sum(contact_val(k, C) for k in orbits[oi])

h = mp.mpf('1e-26')
dirs = [('a', 3, 0), ('b', 3, 1), ('c', 7, 0), ('d', 7, 1), ('t', 13, 1),
        ('s', 9, 0), ('z', 10, 0)]
G = {}
for nm, site, axis in dirs:
    for oi in range(5):
        def val(hh):
            C = [tuple(p) for p in base_centres()]
            q = list(C[site]); q[axis] = q[axis] + hh
            C[site] = tuple(q)
            return orbit_sum(oi, C)
        G[(nm, oi)] = (val(h) - val(-h))/(2*h)

P('')
P('=' * 78)
P('(1) orbit-gradient rows (site-motion convention), 7 directions x 5 orbits')
P('    dir  ' + '  '.join('%16s' % str(orbits[o]) for o in range(5)))
for nm, _, _ in dirs:
    P('    %-4s ' % nm + '  '.join('%16s' % mp.nstr(G[(nm, o)], 9) for o in range(5)))

P('')
P('(2) KKT residual sum_k w_k dF_k/dx with the PUBLISHED weights')
P('    weights %s' % [mp.nstr(x, 12) for x in wl])
worst = None
for nm, _, _ in dirs:
    r = sum(wl[k]*G[(nm, k)] for k in range(5))
    scale = max(abs(G[(nm, k)]) for k in range(5))
    rel = abs(r)/scale if scale else r
    if worst is None or rel > worst[1]:
        worst = (nm, rel, r)
    P('    %-4s residual = %-16s   scale %-10s  rel = %s'
      % (nm, mp.nstr(r, 8), mp.nstr(scale, 6), mp.nstr(rel, 4)))
P('    worst relative residual: %s (direction %s)' % (mp.nstr(worst[1], 6), worst[0]))

P('')
P('(3) the 5x5 system the certificate selects (a,b,c,d rows + normalization)')
cols = ['a', 'b', 'c', 'd']
M = mp.zeros(5, 5)
for i, nm in enumerate(cols):
    for k in range(5):
        M[i, k] = G[(nm, k)]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    M[4, k] = nn
P('    det = %s' % mp.nstr(mp.det(M), 14))
if mp.det(M) != 0:
    sol = mp.lu_solve(M, mp.matrix([0, 0, 0, 0, 1]))
    P('    my solution:  %s' % [mp.nstr(x, 10) for x in sol])
    P('    published:    %s' % [mp.nstr(x, 10) for x in wl])
    P('    all positive: %s' % all(x > 0 for x in sol))
M5 = mp.zeros(5, 5)
for i, nm in enumerate(['a', 'b', 'c', 'd', 't']):
    for k in range(5):
        M5[i, k] = G[(nm, k)]
U, Sv, Vt = mp.svd(M5)
P('    (a,b,c,d,t) block singular values: %s' % [mp.nstr(x, 8) for x in Sv])
P('    rank (tol 1e-30): %d' % sum(1 for x in Sv if x > mp.mpf('1e-30')))

(OUT / 'iface08_kkt_ownfuncs.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface08_kkt_ownfuncs.txt')
