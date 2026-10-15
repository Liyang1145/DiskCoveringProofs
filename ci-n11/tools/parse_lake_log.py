#!/usr/bin/env python3
"""Parse a `lake build` log into per-module rows (JSONL).
usage: parse_lake_log.py <lake.log> <group> <out.jsonl> [<targets.txt>]
Row: {group, module, status: built|failed|replayed, seconds, sorry, errors, warnings}"""
import re, sys, json
log, group, out = sys.argv[1], sys.argv[2], sys.argv[3]
targets = open(sys.argv[4]).read().split() if len(sys.argv) > 4 else []
hdr = re.compile(r'^(✔|⚠|✖|ℹ)\s*\[(\d+)/(\d+)\]\s+(Built|Building|Replayed|Ran|Running|Fetched|Compiled|Checked|Fetching)\s+(\S+)(?:.*?\((\d+(?:\.\d+)?)(ms|s|m)\))?')
rows = {}; cur = None
for raw in open(log, errors='replace'):
    line = raw.rstrip('\n')
    m = hdr.match(line)
    if m:
        sym, _, _, verb, name, t, unit = m.groups()
        name = name.split(':')[0]
        secs = None
        if t:
            secs = float(t) / 1000 if unit == 'ms' else float(t) * (60 if unit == 'm' else 1)
        st = 'failed' if sym == '✖' else ('replayed' if verb == 'Replayed' else 'built')
        r = rows.setdefault(name, dict(group=group, module=name, status=st, seconds=secs, sorry=False, errors=0, warnings=0))
        r['status'] = st; r['seconds'] = secs if secs is not None else r['seconds']
        cur = r; continue
    if cur is not None:
        if "declaration uses 'sorry'" in line: cur['sorry'] = True
        if line.startswith('error:') or ': error:' in line: cur['errors'] += 1
        if line.startswith('warning:') or ': warning:' in line: cur['warnings'] += 1
with open(out, 'a') as f:
    for r in rows.values():
        f.write(json.dumps(r) + '\n')
n = len(rows); fl = sum(r['status'] == 'failed' for r in rows.values())
print(f'{group}: {n} job lines, {fl} failed, {sum(r["sorry"] for r in rows.values())} with sorry warning')
