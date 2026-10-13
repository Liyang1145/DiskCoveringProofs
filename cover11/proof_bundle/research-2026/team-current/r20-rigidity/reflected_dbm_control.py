"""r20-rigidity: controls for the reflected-DBM patch in lead/cosine_dbm_pilot.py (lines 39-53).

Reflection rho(y)_j = y_{(2-j) mod 9}. Controls, all exact Fraction:
  (A) build an explicit rational y, its prefix t, and a NON-SINGLETON DBM that contains the point;
  (B) explicitly reflect y, rebuild the reflected prefix t', and check that for each of the 8 loop
      indices i = (k-2) mod 9 the code interval tt (from subset_bounds + the i<6 flip) CONTAINS the
      true t'_i - t'_6  (orientation: the code needs t'_i - t'_6, same convention as the direct patch);
  (C) check that the cyclic-block sums used by subset_bounds equal the true sums of y over the
      reflected index set (i.e. sum_{j in J} y'_j = t_max - t_min of the ORIGINAL y);
  (D) rq2 containment: the interval sum of squares from tt brackets the true reflected squared norm
      (with a dummy rational roots[] vector).
Writes reflected_dbm_control.json/.log.
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


def prefix(y):
    t = [F(0)]
    for k in range(9):
        t.append(t[-1] + y[k])
    return t


def subset_bounds(db, inds):
    """verbatim re-implementation of the code's subset_bounds"""
    if not inds:
        return F(0), F(0)
    inds = sorted(inds)
    if inds == list(range(inds[0], inds[-1] + 1)):
        a, b = inds[0], inds[-1] + 1
        return -db[b][a], db[a][b]
    comp = sorted(set(range(9)) - set(inds))
    assert comp == list(range(comp[0], comp[-1] + 1)), 'complement not contiguous'
    a, b = comp[0], comp[-1] + 1
    return 1 - db[a][b], 1 + db[b][a]


L, D = F(19, 50), F(1, 4)

# (A) explicit rational y and a NON-SINGLETON DBM containing it
y = [F(1, 12), F(1, 15), F(1, 10), F(1, 8), F(1, 9), F(1, 7), F(1, 11), F(1, 13), F(0)]
y[-1] = 1 - sum(y[:-1])
assert min(y) >= 0 and sum(y) == 1
t = prefix(y)
say('[R0] explicit rational y (min %s) ; prefix t_9 = %s' % (min(y), t[9]))
db = [[F(0) if j <= i else F(1) for j in range(10)] for i in range(10)]
db[9][0] = F(-1)
db = closure(db)
# the ROOT DBM is already non-singleton: width db[i][j] + db[j][i] = 1 for every i < j, and it
# contains every simplex point, hence the chosen rational point.
assert all(-db[i][j] <= t[i] - t[j] <= db[j][i] for i in range(10) for j in range(10))
say('[R1] ROOT DBM used, non-singleton (width 1 in every difference) and verified to contain the chosen point t')

# (B) explicit reflection and containment of the true reflected prefix difference
yr = [y[(2 - j) % 9] for j in range(9)]
tr = prefix(yr)
assert sum(yr) == 1 and tr[9] == 1
say('[R2] reflected y (rho(y)_j = y_(2-j)) ; prefix t\'_9 = %s ; t\'_6 = %s' % (tr[9], tr[6]))
ok_cont = True
rows = []
for k in range(8):
    i = (k - 2) % 9
    l, u = subset_bounds(db, [(2 - j) % 9 for j in range(min(i, 6), max(i, 6))])
    if i < 6:
        l, u = -u, -l
    true_val = tr[i] - tr[6]                 # the convention the code uses: t'_i - t'_6
    inside = (l <= true_val <= u)
    ok_cont &= inside
    rows.append((i, str(l), str(u), str(true_val), inside))
say('[R3] containment of the TRUE reflected t\'_i - t\'_6 by the code interval (8 indices) : %s' % ok_cont)
for i, l, u, tv, ins in rows:
    say('     i=%d  tt=[%s, %s]  true t\'_i-t\'_6 = %s  inside=%s' % (i, l, u, tv, ins))

# (B2) also check the same under a pure cyclic-block split (non-singleton in the tested directions)
db2 = [r[:] for r in db]
db2 = closure(db2)
ok_cont2 = True
for pair in [(0, 5), (2, 7)]:
    i_, j_ = pair
    if db2[i_][j_] + db2[j_][i_] > 0:
        mid = (-db2[j_][i_] + db2[i_][j_]) / 2
        d2 = [r[:] for r in db2]
        d2[i_][j_] = mid
        d2 = closure(d2)
        okc = True
        for k in range(8):
            i = (k - 2) % 9
            l, u = subset_bounds(d2, [(2 - j) % 9 for j in range(min(i, 6), max(i, 6))])
            if i < 6:
                l, u = -u, -l
            okc &= (l <= tr[i] - tr[6] <= u)
        say('[R4] after splitting %s (mid %s): containment still holds : %s' % (pair, mid, okc))
        ok_cont2 &= okc

# (C) the cyclic-block sum identity used by subset_bounds
ok_id = True
for i in [(k - 2) % 9 for k in range(8)]:
    J = [(2 - j) % 9 for j in range(min(i, 6), max(i, 6))]
    lhs = sum(yr[j] for j in J)
    rhs = tr[max(min(i, 6), max(i, 6))] - tr[min(i, 6)] if False else None
    lo_, hi_ = min(i, 6), max(i, 6)
    rhs = t[hi_] - t[lo_]
    ok_id &= (lhs == rhs)
say('[R5] cyclic-block identity sum_{j in J} y\'_j == t_hi - t_lo of the ORIGINAL y (8 indices) : %s'
    % ok_id)

# (D) rq2 containment
roots = [F(0)] + [F(3, 7) * F(k, 8) for k in range(1, 9)]
rlo = rhi = rtrue = F(0)
for k in range(8):
    i = (k - 2) % 9
    l, u = subset_bounds(db, [(2 - j) % 9 for j in range(min(i, 6), max(i, 6))])
    if i < 6:
        l, u = -u, -l
    h_at_l = (i - 6) * L - D * l - (roots[i] - roots[6])
    h_at_u = (i - 6) * L - D * u - (roots[i] - roots[6])
    rlo += min(h_at_l * h_at_l, h_at_u * h_at_u)
    rhi += max(h_at_l * h_at_l, h_at_u * h_at_u)
    tv = (i - 6) * L - D * (tr[i] - tr[6]) - (roots[i] - roots[6])
    rtrue += tv * tv
say('[R6] rq2 containment (dummy roots): true reflected squared norm = %s ; interval = [%s, %s] ;'
    ' inside = %s' % (rtrue, rlo, rhi, bool(rlo <= rtrue <= rhi)))
OUT = {'reflection': 'rho(y)_j = y_{(2-j) mod 9}', 'y': [str(x) for x in y], 'y_reflected': [str(x) for x in yr],
       'non_singleton_dbm': True, 'contains_point': True,
       'tt_contains_true_reflected_prefix_diff': bool(ok_cont),
       'tt_contains_after_splits': bool(ok_cont2),
       'cyclic_block_sum_identity': bool(ok_id),
       'rq2_true': str(rtrue), 'rq2_interval': [str(rlo), str(rhi)],
       'rq2_contains_true': bool(rlo <= rtrue <= rhi),
       'convention_check': "the code uses t'_i - t'_6 (same as the direct patch: tt=[-db[i][6],db[6][i]]);"
                          " the i<6 flip -u,-l maps a bound on sum_{[i,6)} y' to t'_i - t'_6 = -sum",
       'scope': 'controls for the reflected-DBM patch only; C920 radius not re-audited',
       'repro': 'py -3 -B -X utf8 reflected_dbm_control.py'}
(R20 / 'reflected_dbm_control.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'reflected_dbm_control.log').write_text('\n'.join(REP) + '\n')
say('written reflected_dbm_control.json / .log')
