"""r20-rigidity: q2 CONTAINMENT controls for the direct-DBM patch (corrected).

RETRACTION: an earlier version of this file claimed that `cosine_dbm_pilot.py` line 32 uses a
transposed interval. That claim was WRONG. It enclosed `t_6 - t_i`, while the code correctly encloses
`t_i - t_6`, which is exactly what the canonical difference
`theta_i - theta_6 = (i-6)L - D(t_i - t_6)` needs. With the convention "db[p][q] upper-bounds
t_q - t_p":
        db[i][6] >= t_6 - t_i   =>   t_i - t_6 >= -db[i][6]
        db[6][i] >= t_i - t_6   =>   t_i - t_6 <=  db[6][i]
so `tt = [-db[i][6], db[6][i]]` is the right enclosure. No code error exists; the earlier audit was
my error and is withdrawn.

This script builds the containment controls: an explicit rational y, its prefix t, singleton- and
split-consistent DBMs, and checks that the code's `tt` contains the true `t_i - t_6` and that the
interval `q2` from `tt` brackets the true sum of squared canonically shifted perturbations.
"""
import json
from fractions import Fraction as F
from pathlib import Path

R20 = Path(__file__).resolve().parent
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


def closure(db):
    d = [r[:] for r in db]
    for k in range(10):
        for i in range(10):
            for j in range(10):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    return None if any(d[i][i] < 0 for i in range(10)) else d


def split(db, pair):
    i, j = pair
    mid = (-db[j][i] + db[i][j]) / 2
    left = [r[:] for r in db]
    right = [r[:] for r in db]
    left[i][j] = mid
    right[j][i] = -mid
    return mid, closure(left), closure(right)


y = [F(1, 12), F(1, 15), F(1, 10), F(1, 8), F(1, 9), F(1, 7), F(1, 11), F(1, 13), F(0)]
y[-1] = 1 - sum(y[:-1])
assert min(y) >= 0 and sum(y) == 1
t = [F(0)]
for k in range(9):
    t.append(t[-1] + y[k])
assert t[9] == 1
say('[T0] explicit rational y (min %s, sum 1) ; prefix t = %s' % (min(y), [str(x) for x in t]))

db = [[t[q] - t[p] for q in range(10)] for p in range(10)]      # singleton-consistent DBM
ok_sing = True
for k in range(8):
    i = (k - 2) % 9
    ok_sing &= (-db[i][6] <= t[i] - t[6] <= db[6][i])
say('[T1] singleton db[p][q] = t_q - t_p: code interval [-db[i][6], db[6][i]] contains the true'
    ' t_i - t_6 for all 8 loop indices : %s' % ok_sing)

for pair in [(6, 3), (0, 5), (2, 7)]:
    mid, left, right = split(db, pair)
    for name, d in [('left', left), ('right', right)]:
        ok = all((-d[i][6] <= t[i] - t[6] <= d[6][i]) for i in [(k - 2) % 9 for k in range(8)])
        say('[T2] split %s (%s child, mid = %s): code interval still contains the true t_i - t_6 for'
            ' all 8 indices : %s' % (pair, name, mid, ok))

roots = [F(0)] + [F(3, 7) * F(k, 8) for k in range(1, 9)]
L, D = F(19, 50), F(1, 4)
q2_lo = q2_hi = q2_true = F(0)
for k in range(8):
    i = (k - 2) % 9
    hi_ = (i - 6) * L - D * F(-db[i][6]) - (roots[i] - roots[6])   # h decreases in tt
    lo_ = (i - 6) * L - D * F(db[6][i]) - (roots[i] - roots[6])
    q2_lo += min(lo_ * lo_, hi_ * hi_)
    q2_hi += max(lo_ * lo_, hi_ * hi_)
    tv = (i - 6) * L - D * (t[i] - t[6]) - (roots[i] - roots[6])
    q2_true += tv * tv
say('[T3] q2 containment (dummy rational roots): true squared norm = %s ; interval from the code'
    ' tt = [%s, %s] ; true value inside : %s' % (q2_true, q2_lo, q2_hi, bool(q2_lo <= q2_true <= q2_hi)))
OUT = {'retraction': 'earlier "transposed interval" finding withdrawn: line 32 correctly encloses'
                     ' t_i - t_6 (what theta_i - theta_6 needs); no code error',
       'singleton_containment_all_indices': bool(ok_sing),
       'q2_true_dummy_roots': str(q2_true),
       'q2_interval_from_code_tt': [str(q2_lo), str(q2_hi)],
       'q2_contains_true': bool(q2_lo <= q2_true <= q2_hi),
       'scope': 'containment controls for the direct-DBM patch; code correct as written',
       'repro': 'py -3 -B -X utf8 direct_dbm_control.py'}
(R20 / 'direct_dbm_control.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'direct_dbm_control.log').write_text('\n'.join(REP) + '\n')
say('written direct_dbm_control.json / .log')
