"""root-cc2 local-sosc-audit: CORRECTED calibration against the lead's published matrix.

The bug in my earlier scripts: I wrote the C orbit as
    (+c,-d), (+c,+d), (-c,-d), (-c,+d)
whereas the certificate's ordering (C[i] = (sx*c, sy*d) for sx in (-1,1) for sy in (-1,1))
is
    (-c,-d), (-c,+d), (+c,-d), (+c,+d)
i.e. I had the two halves of the C orbit swapped.  This document uses the correct order
and then:
  (1) prints all 24 contact values and checks each equals r^2;
  (2) rebuilds the 28x5 equilibrium matrix by the site-motion convention;
  (3) compares it row-by-row with the lead's published lead-kkt-matrix-control.json;
  (4) reports rank(28x5) and the solve of the 5x5 selected system.
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

# ---- CORRECT centre ordering (certificate line 59), one expression only
def centres_at(a, b, c, d, s, z, t):
    return ([(sx*a, sy*b) for sx in (-1, 1) for sy in (-1, 1)] +
            [(sx*c, sy*d) for sx in (-1, 1) for sy in (-1, 1)] +
            [(-s, mp.mpf(0)), (s, mp.mpf(0)), (z, mp.mpf(0)), (-z, mp.mpf(0)),
             (mp.mpf(0), -t), (mp.mpf(0), t)])
CENTRES = centres_at(A0, B0, C0, D0, S0, Z0, T0)
P('site order (0..13):')
for i, p in enumerate(CENTRES):
    P('   %2d (%s, %s)' % (i, mp.nstr(p[0], 12), mp.nstr(p[1], 12)))

v1 = (1 + A0*A0 + B0*B0 - R0*R0)/2; v2 = (1 + C0*C0 + D0*D0 - R0*R0)/2
det0 = A0*D0 - B0*C0
PX = (v1*D0 - v2*B0)/det0; PY = (A0*v2 - C0*v1)/det0
ref_anchor = [(S0, R0), (PX, PY), (mp.mpf(0), mp.mpf(1)), (-PX, PY), (-S0, R0),
              (-S0, -R0), (-PX, -PY), (mp.mpf(0), mp.mpf(-1)), (PX, -PY), (S0, -R0)]

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
        pnt = boundary_pt(CENTRES[ids[0]], CENTRES[ids[1]], sgn)
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

P('')
P('=' * 78)
P('(1) 24-contact calibration at the candidate (each must equal r^2 = %s)' % mp.nstr(R0*R0, 14))
r2 = R0*R0
bad = 0
for k in range(24):
    val = contact_val(k, CENTRES)
    dev = val - r2
    ok = abs(dev) < mp.mpf('1e-25')
    if not ok:
        bad += 1
    P('   %s %2d  ids %-14s  value - r^2 = %-14s %s'
      % ('B' if k < 10 else 'T', k,
         str(contacts[k]['owners'] if k < 10 else contacts[k]['ids']),
         mp.nstr(dev, 6), 'OK' if ok else 'MISMATCH'))
P('   deviations beyond 1e-25: %d' % bad)

def orbit_sum(oi, C):
    return sum(contact_val(k, C) for k in orbits[oi])

P('')
P('=' * 78)
P('(2) 28x5 equilibrium matrix A (site-motion convention, corrected ordering)')
h = mp.mpf('1e-26')
A = mp.zeros(28, 5)
for j in range(28):
    site, axis = j//2, j % 2
    for oi in range(5):
        def val(hh):
            C = [tuple(p) for p in CENTRES]
            q = list(C[site]); q[axis] = q[axis] + hh
            C[site] = tuple(q)
            return orbit_sum(oi, C)
        A[j, oi] = (val(h) - val(-h))/(2*h)
for j in range(28):
    P('    row %2d (site %2d, %s): %s' % (j, j//2, 'xy'[j % 2],
                                          [mp.nstr(A[j, k], 12) for k in range(5)]))

P('')
P('=' * 78)
P('(3) comparison with the lead\'s published matrix')
ctrl = json.loads((LEAD / 'local-kkt-matrix-control.json').read_text())
lead_rows = ctrl['equilibrium_28_by_5']
P('    rows: lead %d vs mine 28' % len(lead_rows))
worst = mp.mpf(0); worstrow = None
for j in range(min(28, len(lead_rows))):
    for k in range(5):
        a = A[j, k]; b = mp.mpf(str(lead_rows[j][k]))
        dd = abs(a - b)
        if dd > worst:
            worst, worstrow = dd, (j, k, a, b)
P('    max |mine - lead| over the 140 entries = %s' % mp.nstr(worst, 6))
P('    worst at row %d col %d: mine=%s lead=%s'
  % (worstrow[0], worstrow[1], mp.nstr(worstrow[2], 12), mp.nstr(worstrow[3], 12)))
P('    selected rows [0,1,8,9] side by side:')
for j in (0, 1, 8, 9):
    P('      row %d: mine %s' % (j, [mp.nstr(A[j, k], 10) for k in range(5)]))
    P('              lead %s' % [mp.nstr(mp.mpf(str(lead_rows[j][k])), 10) for k in range(5)])
P('    selected matrix rows [normalization, 0, 1, 8, 9]:')
P('      lead: %s' % ctrl['matrix_rows_selected'])

P('')
P('=' * 78)
P('(4) rank and the 5x5 solve')
U, Sv, Vt = mp.svd(A)
P('    singular values of my A: %s' % [mp.nstr(x, 8) for x in Sv])
P('    rank (tol 1e-30): %d' % sum(1 for x in Sv if x > mp.mpf('1e-30')))
Al = mp.zeros(28, 5)
for j in range(28):
    for k in range(5):
        Al[j, k] = mp.mpf(str(lead_rows[j][k]))
Ul, Svl, Vtl = mp.svd(Al)
P('    singular values of the lead\'s A: %s' % [mp.nstr(x, 8) for x in Svl])
P('    rank (tol 1e-30): %d' % sum(1 for x in Svl if x > mp.mpf('1e-30')))
wl = [mp.mpf(str(x)) for x in ctrl['weights']]
P('    lead weights: %s ; sum = %s' % ([mp.nstr(x, 10) for x in wl], mp.nstr(sum(wl), 10)))
res = [sum(wl[k]*mp.mpf(str(lead_rows[j][k])) for k in range(5)) for j in range(28)]
P('    max |A^T w| over the 28 lead rows = %s' % mp.nstr(max(abs(x) for x in res), 6))

(OUT / 'fix10_corrected_calibration.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'fix10_corrected_calibration.txt')
