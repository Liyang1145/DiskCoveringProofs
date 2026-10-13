"""root-cc2 local-sosc-audit: what are the actual contact values at the candidate?

Prints, for each of the 24 contacts (10 boundary switches + 14 circumcircles), the
function value at the candidate and r^2, so the orbit bookkeeping can be checked
directly.  A correct contact function must return exactly r^2 at the candidate for the
contacts that are active.
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

root = json.loads((LEAD / 'root-integer-certificate.json').read_text())
zb, cb, rb = [I(int(Q(a)*S), int(Q(b)*S), True) for a, b in root['box_dyadic']]
def mf(x):
    fr = Q(x.lo + x.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator
Z0 = mf(zb); C0 = mf(cb); R0 = mf(rb)
S0 = mp.sqrt(1 - R0*R0); A0 = (S0 + Z0)/2
T0 = R0 + mp.sqrt(R0*R0 - Z0*Z0)
B0 = R0 + mp.sqrt(R0*R0 - (A0 - Z0)**2)
D0 = 1 - mp.sqrt(R0*R0 - C0*C0)
C = [(-A0, -B0), (-A0, B0), (A0, -B0), (A0, B0),
     (C0, -D0), (C0, D0), (-C0, -D0), (-C0, D0),
     (-S0, mp.mpf(0)), (S0, mp.mpf(0)), (Z0, mp.mpf(0)), (-Z0, mp.mpf(0)),
     (mp.mpf(0), -T0), (mp.mpf(0), T0)]
bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())

def boundary_pts(p, q):
    dv = [q[k]-p[k] for k in range(2)]
    nn = sum(v*v for v in dv)
    k = (sum(v*v for v in q) - sum(v*v for v in p))/2
    base = [v*k/nn for v in dv]
    rad = mp.sqrt((1 - sum(v*v for v in base))/nn)
    return ([base[0] - dv[1]*rad, base[1] + dv[0]*rad],
            [base[0] + dv[1]*rad, base[1] - dv[0]*rad])

def circum_pt(p, q, v):
    u = [q[k]-p[k] for k in range(2)]; w = [v[k]-p[k] for k in range(2)]
    dd = u[0]*w[1] - u[1]*w[0]
    aa = (sum(s2*s2 for s2 in q) - sum(s2*s2 for s2 in p))/2
    bb = (sum(s2*s2 for s2 in v) - sum(s2*s2 for s2 in p))/2
    return [(aa*w[1]-u[1]*bb)/dd, (u[0]*bb-aa*w[0])/dd]

P('r^2 = %s' % mp.nstr(R0*R0, 16))
P('')
P('=' * 78)
P('(1) the ten boundary switches: both circle-circle intersections, their |p|^2 - 1 and')
P('    the squared distance from each to the two owner sites (min must equal r^2)')
for k in range(10):
    e = bary['anchors'][k]
    ids = e['owners']
    p1, p2 = boundary_pts(C[ids[0]], C[ids[1]])
    P('   contact %2d owners %s' % (k, ids))
    for lab, pt in (('p1', p1), ('p2', p2)):
        oncircle = pt[0]**2 + pt[1]**2 - 1
        d0 = (pt[0]-C[ids[0]][0])**2 + (pt[1]-C[ids[0]][1])**2
        d1 = (pt[0]-C[ids[1]][0])**2 + (pt[1]-C[ids[1]][1])**2
        P('      %s = (%s, %s)  |p|^2-1 = %s   d^2 to owners = (%s, %s)   [r^2=%s]'
          % (lab, mp.nstr(pt[0], 10), mp.nstr(pt[1], 10), mp.nstr(oncircle, 4),
             mp.nstr(d0, 12), mp.nstr(d1, 12), mp.nstr(R0*R0, 12)))

P('')
P('=' * 78)
P('(2) the fourteen circumcircles: circumradius^2 at the candidate')
for kk in range(14):
    e = bary['faces'][kk]
    ids = e['ids']
    w = circum_pt(C[ids[0]], C[ids[1]], C[ids[2]])
    R2 = (w[0]-C[ids[0]][0])**2 + (w[1]-C[ids[0]][1])**2
    inside = w[0]**2 + w[1]**2
    P('   face %2d ids %-14s w=(%s, %s)  R^2=%s  |w|^2=%s  R^2-r^2=%s'
      % (kk, str(ids), mp.nstr(w[0], 9), mp.nstr(w[1], 9), mp.nstr(R2, 14),
         mp.nstr(inside, 10), mp.nstr(R2 - R0*R0, 6)))

(OUT / 'contact_values.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'contact_values.txt')
