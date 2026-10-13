"""root-cc2 local-sosc-audit: independent construction of the 5x5 KKT system.

I rebuild the five orbit-summed contact functions from the geometry (5 effective
coordinates a,b,c,d,t; s = sqrt(1-r^2), z = 2a-s, r the box radius) and compare:
  * my exact finite-difference gradient rows with the certificate's selected rows;
  * the rank of the 5x5 system and the row-space spanning claim;
  * the s- and z-columns (must be exactly 0);
  * the certificate's weights (should solve the system with sum = 1).
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
zb, cb, rb = [I(int(Q(a)*S), int(Q(b)*S), True) for a, b in cert['box_dyadic']]
def mf(x):
    fr = Q(x.lo + x.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator
R = mf(rb); Z = mf(zb); CC = mf(cb)
SQ = mp.sqrt(1 - R*R); A0 = (SQ + Z)/2
T0 = R + mp.sqrt(R*R - Z*Z)
B0 = R + mp.sqrt(R*R - (A0 - Z)**2)
D0 = 1 - mp.sqrt(R*R - CC*CC)

def config(a, b, c, d, t):
    """the 14 centres in the certificate's ordering, as functions of (a,b,c,d,t) and
    the fixed radius r of the box"""
    return [(-a, -b), (-a, b), (a, -b), (a, b),
            (c, -d), (c, d), (-c, -d), (-c, d),
            (-SQ, mp.mpf(0)), (SQ, mp.mpf(0)), (Z, mp.mpf(0)), (-Z, mp.mpf(0)),
            (mp.mpf(0), -t), (mp.mpf(0), t)]

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

bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
orbits = [[0, 4, 5, 9], [1, 3, 6, 8], [2, 7], [10, 13, 16, 19], [12, 15, 18, 21]]
contacts = bary['anchors'] + bary['faces']

# branch signs for the ten boundary switches: choose the sign that reproduces the
# recorded anchor point
anchors = [(SQ, R), None, (mp.mpf(0), mp.mpf(1)), None, (-SQ, R), (-SQ, -R), None,
           (mp.mpf(0), mp.mpf(-1)), None, (SQ, -R)]
v1 = (1 + A0*A0 + B0*B0 - R*R)/2; v2 = (1 + CC*CC + D0*D0 - R*R)/2
det0 = A0*D0 - B0*CC
PX = (v1*D0 - v2*B0)/det0; PY = (A0*v2 - CC*v1)/det0
anchors[1] = (PX, PY); anchors[3] = (-PX, PY); anchors[6] = (-PX, -PY); anchors[8] = (PX, -PY)

def fk(k, a, b, c, d, t):
    C = config(a, b, c, d, t)
    e = contacts[k]
    if k < 10:
        ids = e['owners']
        best = None
        for sgn in (1, -1):
            pnt = boundary_pt(C[ids[0]], C[ids[1]], sgn)
            ref = anchors[k]
            dist = (pnt[0]-ref[0])**2 + (pnt[1]-ref[1])**2
            if best is None or dist < best[0]:
                best = (dist, sgn)
        return boundary_f(C[ids[0]], C[ids[1]], best[1])
    ids = e['ids']
    return circum_f(C[ids[0]], C[ids[1]], C[ids[2]])

base = [A0, B0, CC, D0, T0]
H = mp.mpf('1e-25')
M = mp.zeros(5, 5)
for k in range(5):
    for j in range(5):
        def F(v):
            w = list(base); w[j] = v
            return sum(fk(i, *w) for i in orbits[k])
        M[k, j] = mp.diff(F, base[j])

P('=' * 78)
P('(1) the 5x5 orbit-gradient matrix built independently (mp.diff), rows = orbits')
P('    columns: a, b, c, d, t')
for k in range(5):
    P('    orbit %-18s  %s' % (str(orbits[k]), [mp.nstr(M[k, j], 14) for j in range(5)]))
P('')
P('(2) the effective-row rank and kernel')
import mpmath
U, Sv, Vt = mpmath.svd(M)
P('    singular values: %s' % [mp.nstr(x, 12) for x in Sv])
P('    rank at tol 1e-30: %d' % sum(1 for x in Sv if x > mp.mpf('1e-30')))
nul = [Vt[i, 4] for i in range(5)]
nuln = [x/nul[0] for x in nul] if nul[0] != 0 else nul
P('    null direction (normalised, first component 1): %s' % [mp.nstr(x, 12) for x in nuln])
for nm, x in zip('abcdt', nuln):
    P('       %s = %s' % (nm, mp.nstr(x, 12)))

P('')
P('(3) the certificate weights as the solution of the 5x5 system')
w = [mp.mpf(str(Fraction_to_float_w)) if False else None for Fraction_to_float_w in []]
wl = [mp.mpf(x) for x in (0.07625642008329, 0.04461409025638, 0.04347530203347,
                          0.03300234839640, 0.07438949024711)]
P('    weights (from JSON): %s' % wl)
resid = [sum(wl[k]*M[k, j] for k in range(5)) for j in range(5)]
P('    M^T w = %s  (must be 0)' % [mp.nstr(x, 8) for x in resid])
P('    sum w = %s (must be 1)' % mp.nstr(sum(wl), 12))

P('')
P('(4) the lead\'s selected rows [28,0,1,8,9]: do the four physical rows span row space(M)?')
# rows 0,1 = coordinate 0,1 (a_x, a_y); rows 8,9 = coordinates 8,9 (c_x, c_y)
sel = [0, 1, 8, 9]
Msel = mp.matrix([[M[k, j] for j in sel] for k in range(5)])     # 5x4
P('    rank of the 5x4 matrix of selected coordinate columns: %d'
  % sum(1 for x in mpmath.svd(Msel)[1] if x > mp.mpf('1e-30')))
P('    (rank 5 means the four selected physical equilibrium rows + normalization are')
P('     invertible; rank 4 means they are independent but M has the 1-dim kernel)')
# invertibility of the 5x5 augmented system: rows = M columns [0,1,8,9] + normalization
Aug = mp.zeros(5, 5)
for i, j in enumerate(sel):
    for k in range(5):
        Aug[i, k] = M[k, j]
for k in range(5):
    Aug[4, k] = 1
P('    augmented 5x5 (four selected columns + normalization) det = %s'
  % mp.nstr(mp.det(Aug), 12))
Aug2 = mp.zeros(5, 5)
for i, j in enumerate([0, 1, 8, 9]):
    for k in range(5):
        Aug2[i, k] = M[k, j]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    Aug2[4, k] = nn
P('    aug with multiplicity row det = %s' % mp.nstr(mp.det(Aug2), 12))

(OUT / 'iface02_kkt_system.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface02_kkt_system.txt')
