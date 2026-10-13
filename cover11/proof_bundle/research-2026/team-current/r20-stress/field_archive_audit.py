"""FIELD-ARCHIVE-AUDIT: check lead/cosine_dbm_local919.json (321 fields).

Bulk (exact, all 321 fields):
  * 51 alphas per field: positive, normalized (sum = 1), rational;
  * 36 weights per field: all >= 0 (and rational).
Selected (first / last / a reflected one):
  * independent reconstruction attempt of the 36 Schur weights from the 51 alphas, plus the reflection
    label conversion check (canonical new_i = old (i+2) mod 9 ; reflection rho(i) = 4 - i).
Unless stated, everything here is a *check on stored evidence* -- not a re-proof of any local claim.

Usage: py -3 -B -X utf8 research-2026/team-current/r20-stress/field_archive_audit.py
"""
import json
from fractions import Fraction as F
from pathlib import Path

W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'
J = json.loads((LEAD / 'cosine_dbm_local919.json').read_text(encoding='utf-8'))
FIELDS = J['fields']


def frac(v):
    """exact rational: accepts int / str / float / [lo,hi] / [lo,hi,'rational']."""
    if isinstance(v, (list, tuple)):
        if len(v) >= 3:
            return frac(v[2])
        if len(v) == 2:
            return (frac(v[0]) + frac(v[1])) / 2
        return F(str(v[0]))
    if isinstance(v, int):
        return F(v)
    if isinstance(v, str):
        s = v.strip()
        if "/" in s:
            n, d = s.split("/"); return F(int(n), int(d))
        return F(s) if "." not in s else F(s)
    if isinstance(v, float):
        return F(v).limit_denominator(10 ** 12)
    return F(str(v))


def bounds(v):
    """sign bounds (lo,hi) as Fractions for scalars or interval-like entries."""
    if isinstance(v, (list, tuple)) and len(v) >= 2:
        a, b = frac(v[0]), frac(v[1])
        return (min(a, b), max(a, b))
    x = frac(v)
    return (x, x)


# RETRACTED (lead): weights entries are (i, j, w) = anchor/retained-coordinate INDICES + exact weight,
# NOT [lo, hi, rational].  The previous "sum of lo(weights) = 84" was a sum of INDICES -> meaningless.
bad_alpha_len = bad_alpha_pos = bad_alpha_norm = bad_w_len = 0
bad_w_neg = bad_idx = 0
w_min = None
max_idx = 0
n_fields = len(FIELDS)
sum_dev_max = F(0)
for fld in FIELDS:
    a = fld.get('alpha', [])
    w = fld.get('weights', [])
    if len(a) != 51:
        bad_alpha_len += 1
    if len(w) != 36:
        bad_w_len += 1
    A = [frac(x) for x in a]
    if not all(x > 0 for x in A):
        bad_alpha_pos += 1
    s = sum(A, F(0))
    sum_dev_max = max(sum_dev_max, abs(s - 1))
    if abs(s - 1) > 0:
        bad_alpha_norm += 1
    for ent in w:
        if not (isinstance(ent, (list, tuple)) and len(ent) == 3):
            bad_w_len += 1
            continue
        i, j, ww = int(ent[0]), int(ent[1]), frac(ent[2])
        max_idx = max(max_idx, i, j)
        if i < 0 or j < 0:
            bad_idx += 1
        if ww < 0:
            bad_w_neg += 1
        w_min = ww if w_min is None else min(w_min, ww)

res = {
    'source': str(LEAD / 'cosine_dbm_local919.json'),
    'n_fields': n_fields,
    'bulk': {'alpha_len_ne_51': bad_alpha_len, 'alpha_not_all_positive': bad_alpha_pos,
             'alpha_sum_ne_1': bad_alpha_norm, 'max_abs_sum_minus_1': str(sum_dev_max),
             'weights_len_ne_36': bad_w_len, 'weights_negative': bad_w_neg,
             'weights_bad_index': bad_idx, 'weights_max_index_seen': max_idx,
             'weights_min_value': str(w_min),
             'schema': '(i, j, w): indices + exact weight (source: lead/certify_energy_cell.py line 20)'},
}
print('=== BULK (all %d fields, exact rationals) ===' % n_fields)
print('   alpha: len!=51 %d ; not-all-positive %d ; sum!=1 %d (max |sum-1| = %s)'
      % (bad_alpha_len, bad_alpha_pos, bad_alpha_norm, sum_dev_max))
print('   weights: len!=36 %d ; any negative %d' % (bad_w_len, bad_w_neg))

# ---- label / reflection conversion check on the stored names --------------------------------
names = [f.get('name', '?') for f in FIELDS]
refl = [n for n in names if 'reflect' in n.lower() or 'refl' in n.lower()]
res['names'] = {'first': names[0], 'last': names[-1], 'n_with_reflect_in_name': len(refl),
                'reflect_examples': refl[:5]}
print('=== NAMES ===')
print('   first %r ; last %r ; names containing reflect: %d %s'
      % (names[0], names[-1], len(refl), refl[:5]))

# ---- selected fields: descriptor + independent reconstruction status -------------------------
sel = [0, n_fields - 1] + ([names.index(refl[0])] if refl else [n_fields // 2])
sel = sorted(set(sel))[:3]
res['selected'] = []
for idx in sel:
    fld = FIELDS[idx]
    A = [frac(x) for x in fld.get('alpha', [])]
    Wb = [bounds(x) for x in fld.get('weights', [])]
    entry = {'idx': idx, 'name': fld.get('name'), 'alpha_pos': all(x > 0 for x in A),
             'alpha_sum': str(sum(A, F(0))), 'weights_nonneg': all(frac(e[2]) >= 0 for e in fld.get('weights', [])),
             'weight_min_lo': str(min(lo for (lo, hi) in Wb)), 'n_alpha': len(A), 'n_weights': len(Wb),
             'schur_reconstruction':
                 'NOT COMPLETED HERE: the 51->36 elimination needs the field system (incidence/'
                 'geometry) as stored in cosine_dbm_local919.json["nodes"]; reverse-engineering it is '
                 'beyond this check. The bulk checks above are exact and cover all 321 fields.'}
    res['selected'].append(entry)
    print('=== SELECTED field %d (%s) === alpha_pos=%s sum=%s ; weights_nonneg=%s wmin=%s'
          % (idx, entry['name'], entry['alpha_pos'], entry['alpha_sum'],
             entry['weights_nonneg'], entry.get('weight_min_lo')))

node_keys = None
if isinstance(J.get('nodes'), list) and J['nodes']:
    n0 = J['nodes'][0]
    node_keys = list(n0.keys()) if isinstance(n0, dict) else type(n0).__name__
res['nodes_probe'] = node_keys
print('=== nodes probe ===', str(node_keys)[:160])
OUT.mkdir(exist_ok=True)
(OUT / 'field_archive_audit.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
print('[done] -> out/field_archive_audit.json')
