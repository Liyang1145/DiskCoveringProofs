#!/usr/bin/env python3
"""Merge results-* artifacts into summary.json; print a markdown summary to stdout.
usage: summarize.py <dir-with-artifacts> <summary.json>"""
import sys, glob, json, os
d, out = sys.argv[1], sys.argv[2]
mods = {}; groups = []; audit = []
for f in sorted(glob.glob(f'{d}/**/*.jsonl', recursive=True)):
    b = os.path.basename(f)
    for l in open(f):
        try: r = json.loads(l)
        except Exception: continue
        if b.endswith('-groups.jsonl'): groups.append(r)
        elif b.endswith('-audit.jsonl'): audit.append(r)
        else: mods[(r['group'], r['module'])] = r   # later chunks override earlier
per = {}
for (g, m), r in mods.items():
    p = per.setdefault(g, dict(built=0, replayed=0, failed=0, sorry=0, failed_modules=[]))
    p[r['status']] = p.get(r['status'], 0) + 1
    p['sorry'] += r.get('sorry', False)
    if r['status'] == 'failed': p['failed_modules'].append(m)
lastaudit = {}
for a in audit: lastaudit[a['const']] = a
S = dict(groups=groups, per_group=per, audit=list(lastaudit.values()))
json.dump(S, open(out, 'w'), indent=1)
print('## dcp-n11-build summary\n')
print('| group | built | replayed | failed | sorry |\n|---|---|---|---|---|')
for g, p in sorted(per.items()):
    print(f"| {g} | {p.get('built',0)} | {p.get('replayed',0)} | {p['failed']} | {p['sorry']} |")
print('\n### lake invocations\n')
for g in groups: print(f"- {g['track']} c{g['chunk']} {g['group']}: rc={g['lake_rc']} {g['seconds']}s")
print('\n### axiom audit\n')
for a in lastaudit.values():
    print(f"- {'OK ' if a['ok'] else 'BAD'} `{a['const']}`: {a['axioms']}")
