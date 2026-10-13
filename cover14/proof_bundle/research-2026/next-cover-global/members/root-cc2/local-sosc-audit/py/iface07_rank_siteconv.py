"""root-cc2 local-sosc-audit: the rank interface in the certificate's OWN convention.

Convention (this is what the certificate's gradient rows mean):
  * the contact functions f_k depend on site positions only;
  * a coordinate direction perturbs ONE site coordinate, all other sites fixed, the
    radius/contact points re-solved (here: r fixed, contact points recomputed);
  * each orbit row is the sum over the contacts belonging to that orbit of
    partial f_k / partial x_j.
This differs from varying a family parameter (which moves several sites at once); the
earlier drafts of this audit mixed the two, which is why they disagreed with the
certificate.

Outputs: the 5x6 block on (a,b,c,d,t,s) and the 5x5 block on (a,b,c,d,t) - rank, kernel,
and the 5x5 system the certificate selects.
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
    a = FR(lo); b = FR(hi)
    wl.append((mp.mpf(a.numerator)/a.denominator + mp.mpf(b.numerator)/b.denominator)/2)
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
    a, b, c, d, s, z, t = A0, B0, C0, D0, S0, Z0, T0
    return [(-a, -b), (-a, b), (a, -b), (a, b),
            (c, -d), (c, d), (-c, -d), (-c, d),
            (-s, mp.mpf(0)), (s, mp.mpf(0)), (z, mp.mpf(0)), (-z, mp.mpf(0)),
            (mp.mpf(0), -t), (mp.mpf(0), t)]

def boundary_pt(p, q, sign):
    dv = [q[k]-p[k] for k in range(2)]
    nn = sum(v*v for v in dv)
    k = (sum(v*v for v in q) - sum(v*v for v in p))/2
    base = [v*k/nn for v in dv]
    rad = mp.sqrt((1 - sum(v*v for v in base))/nn)
    return [base[0] - sign*dv[1]*rad, base[1] + sign*dv[0]*rad]

def contact_val(k, C):
    e = contacts[k]
    if k < 10:
        ids = e['owners']; best = None
        for sgn in (1, -1):
            pnt = boundary_pt(C[ids[0]], C[ids[1]], sgn)
            ref = ref_anchor[k]
            dist = (pnt[0]-ref[0])**2 + (pnt[1]-ref[1])**2
            if best is None or dist < best[0]:
                best = (dist, sgn)
        pnt = boundary_pt(C[ids[0]], C[ids[1]], best[1])
        return sum((pnt[k2]-C[ids[0]][k2])**2 for k2 in range(2))
    ids = e['ids']
    p, q, v = C[ids[0]], C[ids[1]], C[ids[2]]
    u = [q[k2]-p[k2] for k2 in range(2)]; w = [v[k2]-p[k2] for k2 in range(2)]
    dd = u[0]*w[1] - u[1]*w[0]
    aa = (sum(s2*s2 for s2 in q) - sum(s2*s2 for s2 in p))/2
    bb = (sum(s2*s2 for s2 in v) - sum(s2*s2 for s2 in p))/2
    cx = (aa*w[1]-u[1]*bb)/dd; cy = (u[0]*bb-aa*w[0])/dd
    return (cx-p[0])**2 + (cy-p[1])**2

def orbit_sum(oi, C):
    return sum(contact_val(k, C) for k in orbits[oi])

# coordinate directions: perturb ONE centre coordinate, all else fixed (r fixed).
# state vector: the 14 centre positions
def perturbed_state(site, axis, h):
    C = [tuple(p) for p in base_centres()]
    p = list(C[site]); p[axis] = p[axis] + h
    C[site] = tuple(p)
    return C

h = mp.mpf('1e-26')
# map: family parameter name -> (site, axis, sign) for the representative coordinate
dirs = [('a', 3, 0, 1), ('b', 3, 1, 1), ('c', 7, 0, 1), ('d', 7, 1, 1),
        ('t', 13, 1, 1)]
Gs = {}
for nm, site, axis, sgn in dirs:
    for oi in range(5):
        fp = orbit_sum(oi, perturbed_state(site, axis, sgn*h))
        fm = orbit_sum(oi, perturbed_state(site, axis, -sgn*h))
        Gs[(nm, oi)] = (fp - fm)/(2*h)

P('=' * 78)
P('(1) orbit-gradient rows, site-motion convention (partials of the orbit sums)')
P('    dir  ' + '  '.join('%16s' % str(orbits[o]) for o in range(5)))
for nm, _, _, _ in dirs:
    P('    %-4s ' % nm + '  '.join('%16s' % mp.nstr(Gs[(nm, o)], 10) for o in range(5)))
P('')
P('    weights: %s' % [mp.nstr(x, 12) for x in wl])
P('(2) KKT residual sum_k w_k dF_k/dx:')
for nm, _, _, _ in dirs:
    r = sum(wl[k]*Gs[(nm, k)] for k in range(5))
    P('    %-4s %s' % (nm, mp.nstr(r, 10)))
P('')
P('(3) the 5x5 on (a,b,c,d,t) and its system')
cols = ['a', 'b', 'c', 'd', 't']
M = mp.zeros(5, 5)
for i, nm in enumerate(cols):
    for k in range(5):
        M[i, k] = Gs[(nm, k)]
U, Sv, Vt = mp.svd(M)
P('    singular values: %s' % [mp.nstr(x, 10) for x in Sv])
P('    rank (tol 1e-30): %d' % sum(1 for x in Sv if x > mp.mpf('1e-30')))
nul = [Vt[i, 4] for i in range(5)]
nz = nul[0]
P('    kernel direction (first comp 1): %s' % [mp.nstr(x/nz, 10) for x in nul])
P('    (columns are a,b,c,d,t)')
P('')
M5 = mp.zeros(5, 5)
for i, nm in enumerate(['a', 'b', 'c', 'd']):
    for k in range(5):
        M5[i, k] = Gs[(nm, k)]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    M5[4, k] = nn
P('    det of (a,b,c,d rows + normalization) = %s' % mp.nstr(mp.det(M5), 12))
if mp.det(M5) != 0:
    sol = mp.lu_solve(M5, mp.matrix([0, 0, 0, 0, 1]))
    P('    solution:   %s' % [mp.nstr(x, 10) for x in sol])
    P('    all positive: %s' % all(x > 0 for x in sol))
    P('    printed weights: %s' % [mp.nstr(x, 10) for x in wl])

(OUT / 'iface07_rank_siteconv.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface07_rank_siteconv.txt')
