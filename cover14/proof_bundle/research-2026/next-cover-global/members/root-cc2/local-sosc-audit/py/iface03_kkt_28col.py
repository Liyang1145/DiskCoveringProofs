"""root-cc2 local-sosc-audit: build the 28-column orbit-gradient matrix independently.

This is the interface the proof turns on.  Definitions used here:
  * the 14 centres in the certificate's ordering (indices 0..13 = coords 2i,2i+1);
  * radii/site parameters are functions of the SOURCE BOX parameters (s,z,r) via
    a=(s+z)/2, b=r+sqrt(r^2-(a-z)^2), t=r+sqrt(r^2-z^2), d=1-sqrt(r^2-c^2);
  * a *site-move* direction perturbs ONE centre coordinate and updates every dependent
    quantity (this is the direction the certificate's gradient rows use, and the one
    relevant to the 28-coordinate optimization).
  * the orbit-summed function is F_orb = sum_{k in orb} f_k.

Reported: the 28 columns of the five orbit rows, the zero-column set, the rank, the
kernel direction, and the solution of the 5x5 system with the certificate's rows.
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
Z = mf(zb); C0 = mf(cb); R = mf(rb)
SQ0 = mp.sqrt(1 - R*R); A0 = (SQ0 + Z)/2
T0 = R + mp.sqrt(R*R - Z*Z)
B0 = R + mp.sqrt(R*R - (A0 - Z)**2)
D0 = 1 - mp.sqrt(R*R - C0*C0)

bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
contacts = bary['anchors'] + bary['faces']
orbits = [[0, 4, 5, 9], [1, 3, 6, 8], [2, 7], [10, 13, 16, 19], [12, 15, 18, 21]]

def centres_from(a, b, c, d, t, s):
    """the 14 centres with ALL dependencies recomputed from (a,b,c,d,t,s).
    s is the extra parameter: z = 2a - s, r = sqrt(1-s^2)."""
    r = mp.sqrt(1 - s*s)
    z = 2*a - s
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

# reference anchor points for branch selection
v1 = (1 + A0*A0 + B0*B0 - R*R)/2; v2 = (1 + C0*C0 + D0*D0 - R*R)/2
det0 = A0*D0 - B0*C0
PX = (v1*D0 - v2*B0)/det0; PY = (A0*v2 - C0*v1)/det0
ref_anchor = [(SQ0, R), (PX, PY), (mp.mpf(0), mp.mpf(1)), (-PX, PY), (-SQ0, R),
              (-SQ0, -R), (-PX, -PY), (mp.mpf(0), mp.mpf(-1)), (PX, -PY), (SQ0, -R)]

def fk(k, a, b, c, d, t, s):
    C = centres_from(a, b, c, d, t, s)
    e = contacts[k]
    if k < 10:
        ids = e['owners']
        best = None
        for sgn in (1, -1):
            pnt = boundary_pt(C[ids[0]], C[ids[1]], sgn)
            ref = ref_anchor[k]
            dist = (pnt[0]-ref[0])**2 + (pnt[1]-ref[1])**2
            if best is None or dist < best[0]:
                best = (dist, sgn)
        return boundary_f(C[ids[0]], C[ids[1]], best[1])
    ids = e['ids']
    return circum_f(C[ids[0]], C[ids[1]], C[ids[2]])

# parameter vector for the family: (a,b,c,d,t,s)
p0 = [A0, B0, C0, D0, T0, SQ0]
def orbit_sum(orb, pp):
    return sum(fk(k, *pp) for k in orb)

# 28 columns: coordinate j of site i corresponds to perturbing the centre coordinate,
# which is a direction in the family (a,b,c,d,t,s) or in the pure centre position.
# Map: site i coordinate (x/y).
site_deps = {}
for i in range(14):
    site_deps[i] = None

def set_centre(pp, site, axis, val):
    """return the perturbed parameter vector so that centre `site`, axis `axis` = val,
    with all dependencies recomputed from the family relation of that site."""
    a, b, c, d, t, s = pp
    if site in (0, 1, 2, 3):                       # A orbit: +-a, +-b
        if axis == 0:
            a = val
            s = 2*a - Z                            # keep z fixed (z = 2a - s)
            r = mp.sqrt(1 - s*s)
            b = r + mp.sqrt(r*r - (a - Z)**2)
            t = r + mp.sqrt(r*r - Z*Z)
            d = 1 - mp.sqrt(r*r - c*c)
        else:
            b = val
            r = mp.sqrt(1 - s*s)
            t = r + mp.sqrt(r*r - Z*Z)
    elif site in (4, 5, 6, 7):                     # C orbit: +-c, +-d
        if axis == 0:
            c = val
            r = mp.sqrt(1 - s*s)
            d = 1 - mp.sqrt(r*r - c*c)
        else:
            d = val
            r = mp.sqrt(1 - s*s)
            c = mp.sqrt(r*r - (1 - d)**2)
    elif site in (8, 9):                           # X sites: +-s, 0
        if axis == 0:
            s = val
            r = mp.sqrt(1 - s*s)
            a = (s + Z)/2
            b = r + mp.sqrt(r*r - (a - Z)**2)
            t = r + mp.sqrt(r*r - Z*Z)
            d = 1 - mp.sqrt(r*r - c*c)
    elif site in (10, 11):                         # Z sites: +-z, 0
        if axis == 0:
            zloc = val
            r = mp.sqrt(1 - s*s)
            a = (s + zloc)/2
            b = r + mp.sqrt(r*r - (a - zloc)**2)
            t = r + mp.sqrt(r*r - zloc*zloc)
            d = 1 - mp.sqrt(r*r - c*c)
    elif site in (12, 13):                         # T sites: 0, +-t
        if axis == 1:
            t = val
    return [a, b, c, d, t, s]

h = mp.mpf('1e-25')
G = mp.zeros(5, 28)
for oi, orb in enumerate(orbits):
    for site in range(14):
        for axis in range(2):
            j = 2*site + axis
            pp = [x for x in p0]
            base_c = centres_from(*p0)
            val0 = base_c[site][axis]
            fp = set_centre(pp, site, axis, val0 + h)
            fm = set_centre(pp, site, axis, val0 - h)
            G[oi, j] = (orbit_sum(orb, fp) - orbit_sum(orb, fm))/(2*h)

P('=' * 78)
P('(1) 28-column orbit gradient rows (independent finite differences)')
P('    columns with |entry| > 1e-30, per orbit:')
for oi, orb in enumerate(orbits):
    nz = [(j, G[oi, j]) for j in range(28) if abs(G[oi, j]) > mp.mpf('1e-30')]
    P('    orbit %-18s nonzero cols: %s' % (str(orb), [j for j, _ in nz]))
    P('        values: %s' % [mp.nstr(v, 8) for _, v in nz])
P('')
P('(2) which coordinates are the nonzero columns?  (coordinate j = site j//2, axis j%2)')
allnz = sorted({j for oi in range(5) for j in range(28) if abs(G[oi, j]) > mp.mpf('1e-30')})
P('    union of nonzero columns: %s' % allnz)
P('    as (site,axis): %s' % [(j//2, 'xy'[j % 2]) for j in allnz])
P('    s-columns (site 8/9 axis0): %s' % [j for j in (16, 18) if j in allnz])
P('    z-columns (site 10/11 axis0): %s' % [j for j in (20, 22) if j in allnz])

P('')
P('(3) rank and kernel of the 5xT matrix restricted to the nonzero columns')
M = mp.matrix([[G[oi, j] for j in allnz] for oi in range(5)])
U, Sv, Vt = mp.svd(M)
P('    singular values: %s' % [mp.nstr(x, 10) for x in Sv])
P('    rank (tol 1e-30): %d' % sum(1 for x in Sv if x > mp.mpf('1e-30')))
nul = [Vt[i, len(allnz)-1] for i in range(len(allnz))]
nz0 = nul[0] if nul[0] != 0 else 1
P('    kernel direction (normalised): %s' % [mp.nstr(x/nz0, 10) for x in nul])
P('    columns are (site,axis): %s' % [(j//2, 'xy'[j % 2]) for j in allnz])

P('')
P('(4) weights: solve the 5x5 system with the certificate rows [28,0,1,8,9]')
rows = [[G[k, j] for k in range(5)] for j in range(28)] + [[I(len(o)) for o in orbits]]
chosen = [28] + allnz[:4] if len([j for j in allnz]) >= 4 else [28] + allnz
P('    certificate selected rows: [28, 0, 1, 8, 9]; my nonzero columns: %s' % allnz)
P('    building the 5x5 from certificate rows 0,1,8,9 and normalization:')
sel = [0, 1, 8, 9]
aug = mp.zeros(5, 5)
for i, j in enumerate(sel):
    for k in range(5):
        aug[i, k] = G[k, j]
for k, nn in enumerate([4, 4, 2, 4, 4]):
    aug[4, k] = nn
P('    det = %s' % mp.nstr(mp.det(aug), 14))
wl = [mp.mpf(x) for x in (0.07625642008329, 0.04461409025638, 0.04347530203347,
                          0.03300234839640, 0.07438949024711)]
rhs = [mp.mpf(0)]*4 + [mp.mpf(1)]
sol = mp.lu_solve(aug, mp.matrix(rhs))
P('    exact solution of that system: %s' % [mp.nstr(x, 12) for x in sol])
P('    certificate weights:            %s' % [mp.nstr(x, 12) for x in wl])
P('    max |difference|: %s' % mp.nstr(max(abs(sol[i]-wl[i]) for i in range(5)), 6))
P('    all positive: %s' % all(x > 0 for x in sol))

(OUT / 'iface03_kkt_28col.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface03_kkt_28col.txt')
