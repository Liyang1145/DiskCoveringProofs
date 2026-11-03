#!/usr/bin/env python3
"""BFS shortest import path from the lane-A chain roots to the three
non-C450 modules that carry a real `set_option maxHeartbeats 0` (flagged by
c450-hardrules-stripped.json).  Read-only static analysis, NOT a kernel verdict.
"""
import json, os, re, sys
from collections import deque

LEAN = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'lean')
LEAN = os.path.normpath(LEAN)
IMP = re.compile(r'^\s*import\s+(N11Formalization[\w.]*)', re.M)

ROOTS = ['N11Formalization.C450ChainCompletion',
         'N11Formalization.C450ChainCompletionMain']
TARGETS = ['N11Formalization.DrowBallBox_compIvBoxBox',
           'N11Formalization.GridBridge',
           'N11Formalization.Ladder49_jt_kkt_z']

def path_of(mod):
    return os.path.join(LEAN, mod.replace('.', '/') + '.lean')

def imports_of(mod):
    p = path_of(mod)
    if not os.path.exists(p):
        return None
    with open(p, encoding='utf-8', errors='replace') as f:
        return IMP.findall(f.read())

prev = {}
seen = set()
q = deque()
for r in ROOTS:
    prev[r] = None
    seen.add(r)
    q.append(r)
missing = []
while q:
    m = q.popleft()
    deps = imports_of(m)
    if deps is None:
        missing.append(m)
        continue
    for d in deps:
        if d not in seen:
            seen.add(d)
            prev[d] = m
            q.append(d)

def chain(t):
    out = []
    cur = t
    while cur is not None:
        out.append(cur)
        cur = prev.get(cur)
    return list(reversed(out))

report = {
    'roots': ROOTS,
    'closure_size': len(seen),
    'missing_module_files': sorted(set(missing)),
    'targets': {},
}
for t in TARGETS:
    if t in prev:
        report['targets'][t] = {'reachable': True, 'shortest_import_path': chain(t)}
    else:
        report['targets'][t] = {'reachable': False, 'shortest_import_path': None}

out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   'c450-import-paths.json')
with open(out, 'w', encoding='utf-8') as f:
    json.dump(report, f, indent=1, sort_keys=True)
print(json.dumps({k: report[k] for k in ('closure_size','missing_module_files','targets')}, indent=1))
