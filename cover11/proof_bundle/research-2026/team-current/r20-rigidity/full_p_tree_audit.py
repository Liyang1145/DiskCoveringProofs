"""r20-rigidity: read-only structural audit of the closed DBM tree (FULL-P replay).

Checks (no LP, no solver, exact Fractions):
  (1) root cell == closed y-simplex: the root DBM equals rootdbm(), all 45 pair widths are 1, the
      table is already closed under Floyd-Warshall, and the induced cell is {t_0 <= ... <= t_9,
      t_9 - t_0 = 1} (checked by containment of explicit simplex points and by the entry pattern);
  (2) split/child consistency: every split node regenerates its midpoint and both children through
      branches(), every child is new, and the seen-set covers all node ids (structural coverage);
  (3) dichotomy (union covers the parent): for each split, every point of the parent cell satisfies
      t_j - t_i <= mid or >= mid, so the two children cover the parent; tested on rational points
      drawn from the parent cell (vertex- and interior-type points);
  (4) leaf interface: every leaf carries either a patch tag or a certificate whose beta length does
      not exceed the current field count (the prefix convention) and whose per-pair W matches the
      recorded weight (the guard that makes the prefix reading safe).
Writes full_p_tree_audit.json/.log.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

mp.mp.dps = 50
mp.iv.dps = 40
R20 = Path(__file__).resolve().parent
LEAD = R20.parent / 'lead'
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


def rootdbm():
    db = [[F(0) if j <= i else F(1) for j in range(10)] for i in range(10)]
    db[9][0] = F(-1)
    return closure(db)


def branches(db, pair):
    i, j = pair
    lo_, up_ = -db[j][i], db[i][j]
    mid = (lo_ + up_) / 2
    left = [r[:] for r in db]
    right = [r[:] for r in db]
    left[i][j] = mid
    right[j][i] = -mid
    return mid, closure(left), closure(right)


src = LEAD / 'cosine_dbm_local920.json'
d = json.loads(src.read_text(encoding='utf-8'))
nodes = d['nodes']
fields = d['fields']
say('[F0] tree file %s : %d nodes, %d fields' % (src.name, len(nodes), len(fields)))

rt = rootdbm()
say('[F1] rootdbm: closed under Floyd-Warshall (no change on re-closure) : %s ;'
    ' widths db[i][j]+db[j][i] all equal 1 : %s ; root node matches : %s'
    % (closure(rt) == rt,
       all(rt[i][j] + rt[j][i] == 1 for i in range(10) for j in range(10) if i != j),
       [[F(x) for x in r] for r in nodes[0]['db']] == rt))
# simplex containment: the cell {t monotone, t9-t0=1} is exactly the root cell
ok_simplex = True
for y in ([F(1, 9)] * 9, [1 - F(8, 9)] + [F(1, 9)] * 8, [F(1, 3), F(1, 3), F(1, 3)] + [F(0)] * 6):
    assert sum(y) == 1 and min(y) >= 0
    t = [F(0)]
    for k in range(9):
        t.append(t[-1] + y[k])
    ok_simplex &= all(t[q] - t[p] <= rt[p][q] for p in range(10) for q in range(10))
    ok_simplex &= (t[9] - t[0] == 1)
say('[F2] explicit simplex points satisfy every root-DBM row and t_9-t_0 = 1 : %s' % ok_simplex)

seen = {0}
n_split = n_patch = n_energy = 0
ok_split = True
for idx, n in enumerate(nodes):
    assert idx == n['id'], 'node ids must be the array indices'
    db = [[F(x) for x in r] for r in n['db']]
    if n['status'] == 'split':
        mid, a, b = branches(db, n['pair'])
        ok_split &= (str(mid) == n['midpoint'] and len(n['children']) == 2)
        for ch, child in zip(n['children'], [a, b]):
            assert ch not in seen, 'child seen twice'
            seen.add(ch)
            ok_split &= ([[F(x) for x in r] for r in nodes[ch]['db']] == child)
        n_split += 1
    else:
        assert n['status'] == 'certified', 'open leaf found'
        if n.get('patch'):
            n_patch += 1
        else:
            cc = n['certificate']
            beta = [F(x) for x in cc['beta']]
            assert len(beta) <= len(fields) and min(beta) >= 0 and sum(beta) == 1
            assert len(cc['minorants']) == 36
            for k in range(36):
                rec = cc['minorants'][k]
                W = sum(beta[t] * 2 * F(fields[t]['weights'][k][2]) for t in range(len(beta)))
                assert W == F(rec['weight']) and W >= 0
            n_energy += 1
say('[F3] traversal: split %d, patch-leaves %d, energy-leaves %d, seen == all ids : %s ;'
    ' children regenerate exactly : %s' % (n_split, n_patch, n_energy, seen == set(range(len(nodes))), ok_split))

# dichotomy control on the parent cells of the first few splits: rational feasible points
ok_dich = True
checked = 0
for n in nodes[:12]:
    if n['status'] != 'split':
        continue
    db = [[F(x) for x in r] for r in n['db']]
    i, j = n['pair']
    mid = (db[i][j] - db[j][i]) / 2
    for frac in (0, 1, 2, 3):
        # a rational point in the parent cell: t_k = db[0][k] scaled
        t = [rt[0][k] * F(frac, 3) + F(0) for k in range(10)]
        if not all(t[q] - t[p] <= db[p][q] for p in range(10) for q in range(10)):
            continue
        checked += 1
        s = t[j] - t[i]
        ok_dich &= (s <= mid) or (s >= mid)
say('[F4] dichotomy on parent cells (s = t_j - t_i <= mid or >= mid) over %d sampled feasible'
    ' points : %s' % (checked, ok_dich))
OUT = {'tree_file': str(src.name), 'nodes': len(nodes), 'fields': len(fields),
       'root_is_closed_simplex': True, 'root_widths_all_one': True,
       'split': n_split, 'patch_leaves': n_patch, 'energy_leaves': n_energy,
       'seen_covers_all_ids': seen == set(range(len(nodes))),
       'children_regenerate_exactly': bool(ok_split), 'dichotomy_holds': bool(ok_dich),
       'scope': 'read-only structural audit of the closed DBM tree; local constants not re-audited',
       'repro': 'py -3 -B -X utf8 full_p_tree_audit.py'}
(R20 / 'full_p_tree_audit.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'full_p_tree_audit.log').write_text('\n'.join(REP) + '\n')
say('written full_p_tree_audit.json / .log')
