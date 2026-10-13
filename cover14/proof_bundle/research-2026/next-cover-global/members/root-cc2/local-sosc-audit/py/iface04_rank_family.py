"""root-cc2 local-sosc-audit: the rank interface, computed in the family that the
certificate's gradient rows actually live in.

Family parameters: (a, b, c, d, s, z, t) with the dependent quantities
    r = sqrt(1-s^2),  t = r + sqrt(r^2-z^2),  b = r + sqrt(r^2-(a-z)^2),
    d = 1 - sqrt(r^2-c^2)
recomputed from the perturbed parameters (so the perturbed configuration is the
corresponding member of the exact-radical family).

Reported:
  * the 5x7 orbit-gradient matrix (partials w.r.t. a,b,c,d,s,z,t);
  * which columns vanish (the two claimed exact zeros) and to what accuracy;
  * the 5x5 effective block (a,b,c,d,t): rank, kernel;
  * whether the certificate's selected 5x5 system (rows [28,0,1,8,9]) is invertible
    and reproduces the certificate weights.
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
Z0 = mf(zb); C0 = mf(cb); R0 = mf(rb)
S0 = mp.sqrt(1 - R0*R0); A0 = (S0 + Z0)/2
T0 = R0 + mp.sqrt(R0*R0 - Z0*Z0)
B0 = R0 + mp.sqrt(R0*R0 - (A0 - Z0)**2)
D0 = 1 - mp.sqrt(R0*R0 - C0*C0)
bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
contacts = bary['anchors'] + bary['faces']
orbits = [[0, 4, 5, 9], [1, 3, 6, 8], [2, 7], [10, 13, 16, 19], [12, 15, 18, 21]]

def geom(prm):
    a, b, c, d, s, z, t = prm
    r = mp.sqrt(1 - s*s)
    return (a, b, c, d, s, z, t, r)

def centres(prm):
    a, b, c, d, s, z, t, r = geom(prm)
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

def fk(k, prm):
    C = centres(prm)
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

p0 = [A0, B0, C0, D0, S0, Z0, T0]
np_ = 7
G = mp.zeros(5, np_)
for oi, orb in enumerate(orbits):
    for j in range(np_):
        def F(v):
            w = list(p0); w[j] = v
            return sum(fk(k, w) for k in orb)
        G[oi, j] = mp.diff(F, p0[j])

lab = ['a', 'b', 'c', 'd', 's', 'z', 't']
P('=' * 78)
P('(1) 5x7 orbit-gradient matrix, columns (a,b,c,d,s,z,t)')
for oi, orb in enumerate(orbits):
    P('    orbit %-18s %s' % (str(orb), [mp.nstr(G[oi, j], 12) for j in range(7)]))
P('')
P('    claimed EXACT zeros: s-column (index 4) and z-column (index 5)')
for j, nm in ((4, 's'), (5, 'z')):
    vals = [G[oi, j] for oi in range(5)]
    P('      %s column values: %s' % (nm, [mp.nstr(v, 6) for v in vals]))
    P('      max |%s column| = %s  (fd resolution ~1e-45)' % (nm, mp.nstr(max(abs(v) for v in vals), 6)))

P('')
P('(2) the effective 5x5 block on (a,b,c,d,t) = columns 0,1,2,3,6')
cols = [0, 1, 2, 3, 6]
M5 = mp.matrix([[G[oi, j] for j in cols] for oi in range(5)])
U, Sv, Vt = mp.svd(M5)
P('    singular values: %s' % [mp.nstr(x, 10) for x in Sv])
P('    rank (tol 1e-30): %d' % sum(1 for x in Sv if x > mp.mpf('1e-30')))
nul = [Vt[i, 4] for i in range(5)]
nz = nul[0]
P('    kernel direction (unit, first comp 1): %s' % [mp.nstr(x/nz, 10) for x in nul])
P('    columns of this block: %s' % [lab[j] for j in cols])

P('')
P('(3) certificate selection: rows [28,0,1,8,9] -> 28D coordinate columns 0,1,8,9')
P('    In the family picture those are the a-column (coord 0), b-column (coord 1),')
P('    c-column (coord 8) and d-column (coord 9) if the mapping is the natural one.')
P('    Building the 5x5 from the a,b,c,d columns + normalization (4,4,2,4,4):')
sel = [0, 1, 2, 3]
aug = mp.zeros(5, 5)
for i, j in enumerate(sel):
    for k in range(5):
        aug[i, k] = G[k, j]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    aug[4, k] = nn
det = mp.det(aug)
P('    det = %s' % mp.nstr(det, 14))
if det != 0:
    sol = mp.lu_solve(aug, mp.matrix([0, 0, 0, 0, 1]))
    P('    solution: %s' % [mp.nstr(x, 12) for x in sol])
    P('    certificate weights: %s'
      % [mp.nstr(mp.mpf(x), 12) for x in (0.07625642008329, 0.04461409025638,
                                          0.04347530203347, 0.03300234839640, 0.07438949024711)])
    P('    all positive: %s' % all(x > 0 for x in sol))
# and with the t column included
aug2 = mp.zeros(5, 5)
for i, j in enumerate([0, 1, 2, 6]):
    for k in range(5):
        aug2[i, k] = G[k, j]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    aug2[4, k] = nn
P('    det with (a,b,c,t)+norm = %s' % mp.nstr(mp.det(aug2), 14))

P('')
P('(4) residual check: sum of weights times gradient rows (should vanish on all 7 cols)')
wl = [mp.mpf(x) for x in (0.07625642008329, 0.04461409025638, 0.04347530203347,
                          0.03300234839640, 0.07438949024711)]
res = [sum(wl[k]*G[k, j] for k in range(5)) for j in range(7)]
P('    residual per column (a,b,c,d,s,z,t): %s' % [mp.nstr(x, 8) for x in res])
P('    sum of weights = %s' % mp.nstr(sum(wl), 12))
P('    NOTE the certificate weights are the solution of ITS 5x5; if the residual is not')
P('    zero, the two systems differ and the mapping must be identified explicitly.')

(OUT / 'iface04_rank_family.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface04_rank_family.txt')
