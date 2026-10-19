#!/usr/bin/env python3
"""Write energy/RESULTS.json and energy/classification.csv (one row per remaining terminal)."""
import os, json, csv
H = os.path.dirname(os.path.abspath(__file__))
ids = json.load(open(os.path.join(H, 'ids.json')))
rows = []; cnt = {}
for n in ids['remaining']:
    c = json.load(open(os.path.join(H, 'certs', '%d.json' % n)))
    row = dict(node=n, single_cell=c['status'], single_margin=c.get('margin'), single_lp_gap=c.get('lp_gap'))
    rf = os.path.join(H, 'refine', '%d.json' % n)
    if os.path.exists(rf):
        r = json.load(open(rf)); row['kelley_vup_gap'] = r.get('vup_gap'); row['format_impossible_float'] = r.get('format_impossible_float')
    sf = os.path.join(H, 'split', '%d.json' % n)
    if os.path.exists(sf):
        s = json.load(open(sf)); row['split'] = s['status']; row['split_leaves'] = s.get('leaves')
    if c['status'] == 'pass': cls = 'single_cell_prevalidated'
    elif row.get('split') == 'pass': cls = 'refinement_prevalidated'
    elif 'split' in row: cls = 'open_split_failed'
    else: cls = 'open_not_attempted'
    row['class'] = cls; cnt[cls] = cnt.get(cls, 0) + 1; rows.append(row)
keys = ['node', 'class', 'single_cell', 'single_margin', 'single_lp_gap', 'kelley_vup_gap', 'format_impossible_float', 'split', 'split_leaves']
with open(os.path.join(H, 'classification.csv.tmp'), 'w', newline='') as f:
    w = csv.DictWriter(f, keys); w.writeheader(); [w.writerow({k: r.get(k) for k in keys}) for r in rows]
os.replace(os.path.join(H, 'classification.csv.tmp'), os.path.join(H, 'classification.csv'))
ctl = json.load(open(os.path.join(H, 'control-results.json')))
rt = json.load(open(os.path.join(H, 'roundtrip-results.json')))
leaves = sum(r.get('split_leaves') or 0 for r in rows if r['class'] == 'refinement_prevalidated')
ref = [r for r in rows if 'kelley_vup_gap' in r]
res = dict(remaining=len(rows), classes=cnt, refinement_leaves=leaves,
           positive_control=dict(passed=ctl['positive_pass'], total=ctl['positive_total'], note='all 274 paid packets in Paid16 format (G01..G12 252 + Batch22 22); other 36 paid use different certificate types, not replayed'),
           negative_controls=[(r['name'], r['rejected']) for r in ctl['negative']],
           lean_text_roundtrip=rt,
           kelley_diag=dict(nodes=len(ref), format_impossible_float=sum(1 for r in ref if r.get('format_impossible_float'))),
           min_single_margin=min(r['single_margin'] for r in rows if r['single_margin'] is not None))
open(os.path.join(H, 'RESULTS.json.tmp'), 'w').write(json.dumps(res, indent=1)); os.replace(os.path.join(H, 'RESULTS.json.tmp'), os.path.join(H, 'RESULTS.json'))
print(json.dumps(res, indent=1))
