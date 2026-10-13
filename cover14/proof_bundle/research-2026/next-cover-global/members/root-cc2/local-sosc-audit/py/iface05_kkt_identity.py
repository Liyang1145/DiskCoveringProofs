"""root-cc2 local-sosc-audit: the KKT identity test, done two independent ways.

Test: with the certificate's weights w (from local-sosc-certificate.json), compute
    R_j = sum_k w_k * (orbit-k gradient component in coordinate direction j)
for every physical direction j, in the two coordinate pictures:
  (A) the certificate's own 28-coordinate picture: the orbit-averaged function uses the
      shared family parameters (a,b,c,d,s,z,t) as functions of the *coordinate*, so
      moving one centre coordinate updates the dependent quantities;
  (B) the naive "independent centre coordinates" picture (r fixed, parameters
      independent), for contrast.
Absolute magnitudes decide which picture the identity holds in; a nonzero residual in a
picture means the certificate's weights do not satisfy stationarity there.
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

cert = json.loads((LEAD / 'local-sosc-certificate.json').read_text())
wl = [mp.mpf(str(mp.mpf(a))) if False else None for a in []]
wl = []
for lo, hi in cert['weight_intervals']:
    from fractions import Fraction as FR
    a = FR(lo); b = FR(hi)
    wl.append((mp.mpf(a.numerator)/a.denominator + mp.mpf(b.numerator)/b.denominator)/2)
P('weights (midpoints of the certificate enclosures): %s' % [mp.nstr(x, 14) for x in wl])
P('sum = %s' % mp.nstr(sum(wl), 14))

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
    aa = (sum(s*s for s in q)-sum(s*s for s in p))/2
    bb = (sum(s*s for s in v)-sum(s*s for s in p))/2
    x = (aa*w[1]-u[1]*bb)/dd; y = (u[0]*bb-aa*w[0])/dd
    return (x-p[0])**2 + (y-p[1])**2

v1 = (1 + A0*A0 + B0*B0 - R0*R0)/2; v2 = (1 + C0*C0 + D0*D0 - R0*R0)/2
det0 = A0*D0 - B0*C0
PX = (v1*D0 - v2*B0)/det0; PY = (A0*v2 - C0*v1)/det0
ref_anchor = [(S0, R0), (PX, PY), (mp.mpf(0), mp.mpf(1)), (-PX, PY), (-S0, R0),
              (-S0, -R0), (-PX, -PY), (mp.mpf(0), mp.mpf(-1)), (PX, -PY), (S0, -R0)]

def centres(a, b, c, d, t, s, z):
    return [(-a, -b), (-a, b), (a, -b), (a, b),
            (c, -d), (c, d), (-c, -d), (-c, d),
            (-s, mp.mpf(0)), (s, mp.mpf(0)), (z, mp.mpf(0)), (-z, mp.mpf(0)),
            (mp.mpf(0), -t), (mp.mpf(0), t)]

def fk(k, a, b, c, d, t, s, z):
    C = centres(a, b, c, d, t, s, z)
    e = contacts[k]
    if k < 10:
        ids = e['owners']; best = None
        for sgn in (1, -1):
            pnt = boundary_pt(C[ids[0]], C[ids[1]], sgn)
            ref = ref_anchor[k]
            dist = (pnt[0]-ref[0])**2 + (pnt[1]-ref[1])**2
            if best is None or dist < best[0]:
                best = (dist, sgn)
        return boundary_f(C[ids[0]], C[ids[1]], best[1])
    ids = e['ids']
    return circum_f(C[ids[0]], C[ids[1]], C[ids[2]])

base = dict(a=A0, b=B0, c=C0, d=D0, t=T0, s=S0, z=Z0)
h = mp.mpf('1e-24')

def orbit_sum(oi, **kw):
    prm = dict(base); prm.update(kw)
    return sum(fk(k, **prm) for k in orbits[oi])

def d(oi, name):
    return mp.diff(lambda v: orbit_sum(oi, **{name: v}), base[name])

# --- picture B: independent parameters (r fixed, all others independent)
P('')
P('=' * 78)
P('(A) certificate weights vs the ORBIT GRADIENTS in the independent-parameter picture')
P('    (partials w.r.t. a,b,c,d,t with s,z,r held fixed)')
gnames = ['a', 'b', 'c', 'd', 't']
Gs = [[d(oi, nm) for oi in range(5)] for nm in gnames]   # Gs[param][orbit]
res = []
for i, nm in enumerate(gnames):
    r = sum(wl[k]*Gs[i][k] for k in range(5))
    res.append(r)
    P('    coordinate %s: sum_k w_k dF_k/d%s = %s' % (nm, nm, mp.nstr(r, 10)))
P('    max |residual| = %s' % mp.nstr(max(abs(x) for x in res), 6))

# --- picture A: include the s and z directions as well
P('')
P('(B) same with the s and z directions added (still independent parameters)')
for nm in ('s', 'z'):
    r = sum(wl[k]*d(k, nm) for k in range(5))
    P('    coordinate %s: %s' % (nm, mp.nstr(r, 10)))

P('')
P('=' * 78)
P('(C) what the weights do solve: the 5x5 of the certificate (rows [28,0,1,8,9])')
P('    The certificate selects 5 rows of its 28-row system; if its orbit gradients are')
P('    the ones I computed (picture A), the solved system is:')
cols = {'0': ('a', 'x'), '1': ('b', 'y'), '8': ('c', 'x'), '9': ('d', 'y')}
M = mp.zeros(5, 5)
for i, (nm) in enumerate(['a', 'b', 'c', 'd']):
    for k in range(5):
        M[i, k] = Gs[gnames.index(nm)][k]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    M[4, k] = nn
P('    det = %s' % mp.nstr(mp.det(M), 12))
sol = mp.lu_solve(M, mp.matrix([0, 0, 0, 0, 1]))
P('    solution: %s' % [mp.nstr(x, 12) for x in sol])
P('    certificate: %s' % [mp.nstr(x, 12) for x in wl])
P('    all positive in my solution: %s ; in certificate: %s'
  % (all(x > 0 for x in sol), all(x > 0 for x in wl)))
P('')
P('    => the two weight vectors differ; identify the mapping between the certificate\'s')
P('       contact functions/orbits and the ones I rebuilt before drawing any conclusion.')
P('    my orbit functions at the base point (f_k sums):')
for oi, orb in enumerate(orbits):
    P('       orbit %-18s sum f_k = %s   r^2 = %s' % (str(orb), mp.nstr(orbit_sum(oi), 18), mp.nstr(R0*R0, 18)))

(OUT / 'iface05_kkt_identity.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface05_kkt_identity.txt')
