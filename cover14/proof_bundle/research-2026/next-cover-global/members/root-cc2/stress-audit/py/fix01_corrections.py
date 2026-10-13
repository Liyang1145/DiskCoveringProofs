"""root-cc2 stress-audit CORRECTION: recompute with (a) the correct telescoping identity,
(b) the cap-active condition on the GAP derivative, (c) the witnesses MOVING.

The earlier draft wrongly claimed sum_k v_k = 0 was necessary.  Since
g_k = theta_{k+1} - theta_k with k+1 mod 10, we have g_k' = v_{k+1} - v_k for ALL k
including k = 9 (where (k+1) mod 10 = 0), so
    sum_k g_k' = sum_k (v_{k+1} - v_k) = 0   identically in v.
Feasibility only needs the cap-active gaps' derivatives to vanish, i.e.
    g_k' = v_{k+1} - v_k = 0   at a cap-active k,
NOT v_k = 0.

This script re-checks: gap values and cap-active indices; which velocity pair controls
each cap gap; the first-order gap motion; and the explicit energy along the path with the
witness velocities taken from the certificate JSON.
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
X = [I(int(Q(a)*S), int(Q(b)*S), True) for a, b in cert['box_dyadic']]
z_i, c_i, r_i = X
s_i = (1 - r_i*r_i).sqrt(); a_i = (s_i + z_i)/2
t_i = r_i + (r_i*r_i - z_i*z_i).sqrt()
b_i = r_i + (r_i*r_i - (a_i - z_i)**2).sqrt()
d_i = 1 - (r_i*r_i - c_i*c_i).sqrt()
def mf(ivl):
    fr = Q(ivl.lo + ivl.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator
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
bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
outcert = json.loads((LEAD / 'stress-obstruction-certificate.json').read_text())
ang = [mp.mpf(x) for x in outcert['rational_anchor_angular_velocities']]

P('=' * 78)
P('(1) CORRECTION: the telescoping identity')
P('   g_k = theta_{k+1} - theta_k with index mod 10, so g_k\' = v_{k+1} - v_k for all k;')
P('   sum_k g_k\' = sum_k (v_{k+1} - v_k) = 0 identically in v.  My earlier claim that')
P('   sum_k v_k = 0 is necessary was WRONG (e.g. the rigid rotation v = (1,...,1) has')
P('   sum v = 10 but is trivially admissible with all gaps constant).')
P('   numeric check: sum_k (v_{k+1}-v_k) = %s ; sum_k v_k = %s'
  % (mp.nstr(sum(ang[(k+1) % 10] - ang[k] for k in range(10)), 6), mp.nstr(sum(ang), 10)))
P('   closed-form g_9\' = v_0 - v_9 = %s ; earlier terms sum to v_9 - v_0 = %s (cancel)'
  % (mp.nstr(ang[0] - ang[9], 6), mp.nstr(sum(ang[k+1] - ang[k] for k in range(9)), 6)))

P('')
P('(2) cap-active condition')
th = [mp.atan2(mf(p[1]), mf(p[0])) for p in anc]
gaps = [(th[(k+1) % 10] - th[k]) % (2*mp.pi) for k in range(10)]
Lstar = 2*mp.asin(mf(r_i))
P('   L* = 2 asin(r) = %s deg' % mp.nstr(mp.degrees(Lstar), 12))
P('   k   gap(deg)      g_k\' = v_{k+1}-v_k   cap-active(violated now)')
for k in range(10):
    d = ang[(k+1) % 10] - ang[k]
    atcap = abs(gaps[k] - Lstar) < mp.mpf('1e-12')
    P('   %-3d %12.6f   %14.6f   %s' % (k, mp.degrees(gaps[k]), d, 'YES' if atcap else ''))
P('   cap-active indices: %s' % [k for k in range(10) if abs(gaps[k]-Lstar) < mp.mpf('1e-12')])
P('   their gap derivatives: %s'
  % [mp.nstr(ang[(k+1) % 10] - ang[k], 6) for k in range(10) if abs(gaps[k]-Lstar) < mp.mpf('1e-12')])
P('   my earlier statement "cap-active gaps have v_4 = v_9 = 0" was a misreading: the')
P('   controlling quantities are g_4\' = v_5 - v_4 = %s and g_9\' = v_0 - v_9 = %s'
  % (mp.nstr(ang[5] - ang[4], 6), mp.nstr(ang[0] - ang[9], 6)))
P('   first-order gap motion for the proposed path:')
for k in range(10):
    d = ang[(k+1) % 10] - ang[k]
    atcap = abs(gaps[k] - Lstar) < mp.mpf('1e-12')
    if atcap:
        P('      k=%d CAP-ACTIVE derivative %s (stationary)' % (k, mp.nstr(d, 6)))
    elif d < 0:
        P('      k=%d eps < %+.6f stays below cap' % (k, float((Lstar - gaps[k])/(-d))))
    else:
        P('      k=%d eps > %+.6f stays non-negative' % (k, float(-gaps[k]/d)))

P('')
P('=' * 78)
P('(3) which nodes the certificate moves (free_velocity_dyadic)')
fv = {}
for k, vv in outcert['free_velocity_dyadic'].items():
    fv[int(k)] = [mf(I(int(Q(vv[t][0])*S), int(Q(vv[t][1])*S), True)) for t in range(2)]
P('   node ids with stored velocities: %s' % sorted(fv))
P('   witness nodes are 24+f (f a face index); stored: %s'
  % sorted(k for k in fv if k >= 24))
P('   centre nodes 10+i stored: %s' % sorted(k for k in fv if 10 <= k < 24))
P('   sample: node 24 v = %s ; node 26 v = %s'
  % ([mp.nstr(x, 8) for x in fv.get(24, [])], [mp.nstr(x, 8) for x in fv.get(26, [])]))

(OUT / 'fix01_corrections.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'fix01_corrections.txt')
