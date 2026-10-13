"""root-cc2 stress-audit (corrected): geometric/kinematic facts for STRESS-OBSTRUCTION.

Corrections to the first attempt:
  * the anchor order in stress_obstruction_certificate.py differs from the order written
    in STRESS-OBSTRUCTION.md section 3; the cap-active gaps must be read off the ACTUAL
    ordering used by the code (found by locating the maximal gaps), not from the prose;
  * the orbit reconstruction must use the same keep-set construction as the script.

Checks: cap and cap-active gaps; velocity sum and feasibility margin; anchors on S^1 and
cyclic; D2 covariance of the symmetry permutations on the literal graph; orbit count.
"""
import json
import sys
from pathlib import Path
import mpmath as mp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent          # .../stress-audit/py
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 60
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

cert = json.loads((LEAD / 'root-integer-certificate.json').read_text())
X = [I(Q(a)*S, Q(b)*S, True) for a, b in cert['box_dyadic']]
z_i, c_i, r_i = X
s_i = (1 - r_i*r_i).sqrt(); a_i = (s_i + z_i)/2
t_i = r_i + (r_i*r_i - z_i*z_i).sqrt()
b_i = r_i + (r_i*r_i - (a_i - z_i)**2).sqrt()
d_i = 1 - (r_i*r_i - c_i*c_i).sqrt()
def mf(ivl):
    fr = Q(ivl.lo + ivl.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator

# ---- the CODE's literal order (stress_obstruction_certificate.py line 13)
C = [(sx*a_i, sy*b_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(sx*c_i, sy*d_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(-s_i, I(0)), (s_i, I(0)), (z_i, I(0)), (-z_i, I(0)), (I(0), -t_i), (I(0), t_i)]
v1 = (1 + a_i*a_i + b_i*b_i - r_i*r_i)/2
v2 = (1 + c_i*c_i + d_i*d_i - r_i*r_i)/2
det = a_i*d_i - b_i*c_i
px_i = (v1*d_i - v2*b_i)/det
py_i = (a_i*v2 - c_i*v1)/det
anc = [(s_i, r_i), (px_i, py_i), (I(0), I(1)), (-px_i, py_i), (-s_i, r_i),
       (-s_i, -r_i), (-px_i, -py_i), (I(0), I(-1)), (px_i, -py_i), (s_i, -r_i)]

rp = mf(r_i)
Lstar = 2*mp.asin(rp)
ang = [mp.atan2(mf(y), mf(x)) for x, y in anc]
gaps = [(ang[(k+1) % 10] - ang[k]) % (2*mp.pi) for k in range(10)]
vth_doc = [mp.mpf(0), mp.mpf(-1)/4, mp.mpf(-2)/3, mp.mpf(-13)/12, mp.mpf(-4)/3,
           mp.mpf(-4)/3, mp.mpf(-13)/12, mp.mpf(-2)/3, mp.mpf(-1)/4, mp.mpf(0)]

P('=' * 78)
P('(1) cap and cap-active gaps (code ordering)')
P('   L* = 2 asin(r) = %s deg ; doc prose cites 38.7355 deg (stale constant)'
  % mp.nstr(mp.degrees(Lstar), 10))
P('   per-gap: index, value, deficit to cap, derivative, active?')
cap_active = []
for k in range(10):
    d = vth_doc[(k+1) % 10] - vth_doc[k]
    atcap = abs(gaps[k] - Lstar) < mp.mpf('1e-12')
    if atcap:
        cap_active.append(k)
    P('      k=%d gap=%10.6f deg deficit=%9.2e vth_k=%8.4f vth_k+1=%8.4f dg=%8.4f %s'
      % (k, mp.degrees(gaps[k]), Lstar - gaps[k], vth_doc[k], vth_doc[(k+1) % 10], d,
         'CAP-ACTIVE' if atcap else ''))
P('   cap-active indices (code order) = %s ; vtheta there = %s'
  % (cap_active, [mp.nstr(vth_doc[k], 4) for k in cap_active]))
P('   max |gap - L*| for non-cap gaps = %s rad'
  % mp.nstr(min(abs(Lstar - gaps[k]) for k in range(10) if k not in cap_active), 4))
P('   sum vtheta = %s  (document coefficient list)' % mp.nstr(sum(vth_doc), 6))
# feasibility window
eps_pos = None
eps_neg = None
for k in range(10):
    if k in cap_active:
        continue
    d = vth_doc[(k+1) % 10] - vth_doc[k]
    # gap_k(eps) = gap_k + eps*d  (to first order; exact to O(eps^2) for sums)
    if d < 0:
        e = (Lstar - gaps[k])/(-d)      # cap reached for eps > 0
        eps_pos = e if eps_pos is None else min(eps_pos, e)
    if d > 0:
        e = (Lstar - gaps[k])/d
        eps_neg = e if eps_neg is None else min(eps_neg, e)
P('   feasible at least for -%s < eps < +%s (first-order gap motion)'
  % (mp.nstr(eps_neg, 5), mp.nstr(eps_pos, 5)))

P('')
P('=' * 78)
P('(2) anchors on S^1, cyclic, gaps sum 2pi')
P('   max | |p|^2-1 | = %s ; all gaps in (0,pi): %s ; sum-2pi = %s'
  % (mp.nstr(max(abs(mf(x)**2 + mf(y)**2 - 1) for x, y in anc), 4),
     all(0 < g < mp.pi for g in gaps), mp.nstr(sum(gaps) - 2*mp.pi, 4)))

P('')
P('=' * 78)
P('(3) the D2 permutations on the literal graph: are they PHYSICALLY the symmetry?')
sym = json.loads((LEAD / 'stress-symmetry-control.json').read_text())
perms = sym['symmetry_permutations_weights']
bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
P('   keys of stress-symmetry-control.json: %s' % sorted(sym.keys()))
P('   number of weight permutations: %d ; each is a bijection: %s'
  % (len(perms), all(sorted(p) == list(range(len(p))) for p in perms)))
P('   first two permutations, truncated:')
for p in perms[:2]:
    P('      %s ...' % str(p[:18]))
# edge index -> point map, rebuilt exactly as the script does
g = bary
keep_faces = [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)]
P('   kept face indices: %s' % keep_faces)
P('   face ids of the 14 tight faces: %s' % [f['ids'] for f in g['faces']])
P('   anchor owners list length: %d' % len(g['anchors']))
P('   anchor-owner pairs: %s' % [(k, a['owners']) for k, a in enumerate(g['anchors'])])

# physical covariance test: for each permutation, look for a D2 transform g such that
# P[sym(i)] = g P[i] for every kept index.  We test on the face-vertex indices 0..13
# using the 14 centre positions.
Cpts = {i: C[i] for i in range(14)}
D2 = {'id': (1, 1), 'Sx': (-1, 1), 'Sy': (1, -1), 'C2': (-1, -1)}
P('   testing whether each weight-permutation agrees with one of the four D2 maps')
P('   applied to the 14 physical centres (indices 0..13):')
for pi, p in enumerate(perms):
    hits = []
    for nm, (ex, ey) in D2.items():
        good = 0; tot = 0
        for i in range(14):
            if p[i] >= 14:
                continue
            tot += 1
            x, y = mf(C[i][0]), mf(C[i][1])
            j = p[i]
            xj, yj = mf(C[j][0]), mf(C[j][1])
            if abs(xj - ex*x) < mp.mpf('1e-25') and abs(yj - ey*y) < mp.mpf('1e-25'):
                good += 1
        hits.append((nm, good, tot))
    P('      perm %d: %s' % (pi, hits))

P('')
P('=' * 78)
P('(4) orbit count and sizes for the kept variable set')
keep = [i for i in range(14) if i not in (1, 4, 7, 10, 12, 13)]
idx = 14
for k, anchor in enumerate(g['anchors']):
    for i in anchor['owners']:
        if idx in keep:
            keep.append(idx)
        idx += 1
P('   keep-set size = %d' % len(keep))
left = set(keep); orbits = []
while left:
    orb = {min(left)}
    while True:
        new = orb | {per[i] for i in orb for per in perms}
        if new == orb:
            break
        orb = new
    orbits.append(sorted(orb)); left -= orb
P('   orbit count = %d (script asserts 6)' % len(orbits))
for o in sorted(orbits, key=len):
    kinds = ['face' if x < 14 else 'edge' for x in o]
    P('      size %d  kinds %s  members %s' % (len(o), sorted(set(kinds)), o))

(OUT / 'geo01_facts.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'geo01_facts.txt')
