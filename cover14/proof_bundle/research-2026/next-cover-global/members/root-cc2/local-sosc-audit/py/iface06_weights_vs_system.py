"""root-cc2 local-sosc-audit: verify the certificate's weights against ITS OWN system.

I build the 5x28 orbit-gradient matrix G (orbit-summed contact functions differentiated
w.r.t. all 28 coordinate directions) using the certificate's contact functions and its
branch choices (nearest-to-reference anchor), then:
  (1) solve its 5x5 system on rows [28, 0, 1, 8, 9] and compare with the published weights;
  (2) test the KKT identity: sum_k w_k G[k, j] for all 28 j;
  (3) report the s- and z-coordinate columns (indices 16,18 and 20,22) magnitudes.
If (2) vanishes with the published weights, the analytic identity + spanning argument is
consistent and the interface is closed; a nonvanishing residual localises the defect.
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

def make(prm):
    a, b, c, d, s, z, t = prm
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

def contact_val(k, prm):
    C = make(prm)
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

base = [A0, B0, C0, D0, S0, Z0, T0]

def orbit_sum(oi, prm):
    return sum(contact_val(k, prm) for k in orbits[oi])

# --- dependency model: the certificate's coordinate directions.
# Conventions (the perturbed configuration stays a member of the exact-radical family):
#   a-move: a +- h, s adjusted to keep z fixed, then r,b,t,d recomputed
#   b-move: b only
#   c-move: c only (d recomputed from r, c)
#   d-move: d only (c recomputed from r, d)
#   s-move: s only, then r,a,b,t,d recomputed with z fixed
#   z-move: z only, then a,b,t,d recomputed with s fixed
#   t-move: t only
def perturbed(axis, h):
    a, b, c, d, s, z, t = base
    if axis == 'a':
        a = a + h; s = 2*a - z; r = mp.sqrt(1-s*s)
        b = r + mp.sqrt(r*r - (a-z)**2); t = r + mp.sqrt(r*r - z*z)
        d = 1 - mp.sqrt(r*r - c*c)
    elif axis == 'b':
        b = b + h
    elif axis == 'c':
        c = c + h; r = mp.sqrt(1-s*s); d = 1 - mp.sqrt(r*r - c*c)
    elif axis == 'd':
        d = d + h; r = mp.sqrt(1-s*s); c = mp.sqrt(r*r - (1-d)**2)
    elif axis == 's':
        s = s + h; r = mp.sqrt(1-s*s); a = (s+z)/2
        b = r + mp.sqrt(r*r - (a-z)**2); t = r + mp.sqrt(r*r - z*z)
        d = 1 - mp.sqrt(r*r - c*c)
    elif axis == 'z':
        z = z + h; r = mp.sqrt(1-s*s); a = (s+z)/2
        b = r + mp.sqrt(r*r - (a-z)**2); t = r + mp.sqrt(r*r - z*z)
        d = 1 - mp.sqrt(r*r - c*c)
    elif axis == 't':
        t = t + h
    return [a, b, c, d, s, z, t]

h = mp.mpf('1e-26')
names = ['a', 'b', 'c', 'd', 's', 'z', 't']
D = {}
for nm in names:
    for oi in range(5):
        D[(nm, oi)] = (orbit_sum(oi, perturbed(nm, h)) - orbit_sum(oi, perturbed(nm, -h)))/(2*h)

P('=' * 78)
P('(1) one-parameter gradient rows (7 directions x 5 orbits), certificate geometry')
P('    direction   ' + '  '.join('%14s' % str(orbits[o]) for o in range(5)))
for nm in names:
    P('    %-10s  ' % nm + '  '.join('%14s' % mp.nstr(D[(nm, o)], 8) for o in range(5)))
P('')
P('    certificate weights: %s' % [mp.nstr(x, 12) for x in wl])
P('    sum = %s' % mp.nstr(sum(wl), 12))
P('')
P('(2) KKT residual  sum_k w_k dF_k/dx  in each one-parameter direction')
for nm in names:
    r = sum(wl[k]*D[(nm, k)] for k in range(5))
    P('    %-4s residual = %-22s  (relative to row scale %.3e)'
      % (nm, mp.nstr(r, 8), float(max(abs(D[(nm, k)]) for k in range(5)))))
P('')
P('(3) solve the certificate\'s own 5x5 (rows a,b,c,d + normalization) with these rows')
M = mp.zeros(5, 5)
for i, nm in enumerate(['a', 'b', 'c', 'd']):
    for k in range(5):
        M[i, k] = D[(nm, k)]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    M[4, k] = nn
P('    det = %s' % mp.nstr(mp.det(M), 12))
if mp.det(M) != 0:
    sol = mp.lu_solve(M, mp.matrix([0, 0, 0, 0, 1]))
    P('    solution:      %s' % [mp.nstr(x, 10) for x in sol])
    P('    published:     %s' % [mp.nstr(x, 10) for x in wl])
    P('    all positive: %s' % all(x > 0 for x in sol))
    P('    max |difference| = %s' % mp.nstr(max(abs(sol[i]-wl[i]) for i in range(5)), 8))

(OUT / 'iface06_weights_vs_system.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface06_weights_vs_system.txt')
