"""near_attack2.py  (r20-alternative; sole write, no child; NUMERIC only)

Lead follow-up: execute the REMAINING three starts (2/6 were used before) from
  lead/cosine_cut_diagnostic.json  ->  rows[].y_numeric / rows[].after_numeric,
sorted by after_numeric and taking the LOWEST THREE (the cuts file holds only DBM entries, the
points live in the diagnostic file).

Naming: R_upper = C529 rational value, an explicit NUMERIC PROXY; R* (C891) is NOT used here.
Reporting: actual differences and feasibility residuals only -- no "-1e-7 below R* means no
counterexample" shortcut.
"""
import json
from pathlib import Path
import numpy as np

import joint_oracle_attack_new4 as J

OUT = Path(__file__).resolve().parent
DIAG = OUT.parent / 'lead' / 'cosine_cut_diagnostic.json'
R_UPPER = float(J.R_STAR)          # C529 rational; NUMERIC PROXY ONLY (not R* = C891)


def to_y(vals):
    v = [float(x) for x in np.asarray(vals).reshape(-1)[:9]]
    if len(v) < 9:
        return None
    s = sum(v)
    if abs(s - 2 * np.pi) < 1e-6:
        return [(J.L_CAP - x) / J.D_CAP for x in v]
    if abs(s - 1.0) < 1e-6:
        return v
    return None


def load_rows():
    d = json.loads(DIAG.read_text(encoding='utf-8'))
    rows = d.get('rows', d if isinstance(d, list) else [])
    out = []
    for r in rows:
        if not isinstance(r, dict):
            continue
        y = None
        for k in ('y_numeric', 'after_numeric', 'y', 'y9', 'point'):
            if k in r:
                y = to_y(r[k])
                if y is not None:
                    break
        key = r.get('after_numeric', r.get('y_numeric'))
        out.append({'y9': y, 'sort_key': (float(np.asarray(key).reshape(-1)[0])
                                         if key is not None and np.asarray(key).size else None),
                    'keys': sorted(r.keys())[:14]})
    out.sort(key=lambda r: (r['sort_key'] if r['sort_key'] is not None else 1e9))
    return d, out


if __name__ == '__main__':
    chk = J.jac_cs_check()
    print('jac CS gate:', chk['PASS_lt_1e-6'], 'max err %.3e' % chk['max_jac_error'])
    if not chk['PASS_lt_1e-6']:
        raise SystemExit('jacobian gate failed')
    d, rows = load_rows()
    print('diag top-level keys:', list(d.keys())[:10] if isinstance(d, dict) else 'list',
          '| rows:', len(rows), '| first row keys:', rows[0]['keys'] if rows else None)
    usable = [r for r in rows if r['y9'] is not None][:3]
    print('usable rows (lowest by after_numeric):', len(usable))
    rep = {'R_upper_C529_numeric_proxy': R_UPPER,
           'note': ('R_upper is the C529 rational used as an explicit NUMERIC PROXY; the strict '
                    'R* refers to C891 and is not used here.  Actual differences and feasibility '
                    'residuals are reported; no threshold shortcut.'),
           'source': str(DIAG), 'jacobian_cs_check': chk, 'rows_total': len(rows),
           'rows_usable': len(usable), 'first_row_keys': rows[0]['keys'] if rows else None,
           'runs': []}
    for i, r in enumerate(usable):
        s = J.solve(np.asarray(r['y9'][:8], dtype=float))
        s.update({'start': 'diag_row_low%d' % i, 'sort_key': r['sort_key'],
                  'delta_r_vs_R_upper': s['r'] - R_UPPER})
        rep['runs'].append(s)
        print('diag_row_low%d sort_key=%s r=%.12f delta=%.3e min51=%.3e wmaxOK=%s success=%s'
              % (i, r['sort_key'], s['r'], s['delta_r_vs_R_upper'],
                 s['min_edge_residual_all51'], s['widths_max_leq_L'], s['success']))
    rep['deltas'] = [s['delta_r_vs_R_upper'] for s in rep['runs']]
    rep['min51'] = [s['min_edge_residual_all51'] for s in rep['runs']]
    (OUT / 'near_attack_diag.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
    print('deltas:', rep['deltas'], '-> near_attack_diag.json')
