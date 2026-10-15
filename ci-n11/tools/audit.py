#!/usr/bin/env python3
"""Axiom audit for compiled modules.
usage (from lean/): python3 ../tools/audit.py <audit-list.txt> <out.jsonl> <tag>
List lines: "MODULE" (audit every top-level theorem declared in MODULE) or "MODULE CONST".
Only modules whose .olean exists in .lake/build are audited. Writes one row per constant:
{tag, module, const, axioms, ok}. ok = axioms subset of {propext, Classical.choice, Quot.sound}.
Exit 0 always; prints a summary line AUDIT <tag> ok=<n> bad=<n> unresolved=<n>."""
import os, re, sys, json, subprocess
lst, out, tag = sys.argv[1], sys.argv[2], sys.argv[3]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
items = []
for l in open(lst):
    p = l.split()
    if not p: continue
    mod = p[0]
    olean = '.lake/build/lib/lean/' + mod.replace('.', '/') + '.olean'
    if not os.path.exists(olean):
        print('skip (not compiled):', mod); continue
    if len(p) > 1:
        items.append((mod, p[1])); continue
    src = mod.replace('.', '/') + '.lean'
    ns = []
    for s in open(src, errors='replace'):
        m = re.match(r'^namespace\s+(\S+)', s)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', s)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r'^theorem\s+([^\s(:{\[]+)', s)
        if m:
            items.append((mod, '.'.join(ns + [m.group(1)])))
if not items:
    print(f'AUDIT {tag} ok=0 bad=0 unresolved=0 (nothing compiled)'); sys.exit(0)
mods = sorted({m for m, _ in items})
path = f'/tmp/Audit_{tag}.lean'
with open(path, 'w') as f:
    for m in mods: f.write(f'import {m}\n')
    for _, c in items: f.write(f'#print axioms {c}\n')
r = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
txt = r.stdout + r.stderr
open(f'/tmp/audit_{tag}.out', 'w').write(txt)
res = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt):
    res[m.group(1)] = [a.strip() for a in m.group(2).split(',') if a.strip()]
for m in re.finditer(r"'([^']+)' does not depend on any axioms", txt):
    res[m.group(1)] = []
ok = bad = unres = 0
with open(out, 'a') as f:
    for mod, c in items:
        ax = res.get(c)
        if ax is None:
            row = dict(tag=tag, module=mod, const=c, axioms=None, ok=False, note='unresolved'); unres += 1
        else:
            good = set(ax) <= ALLOWED
            row = dict(tag=tag, module=mod, const=c, axioms=ax, ok=good); ok += good; bad += (not good)
        f.write(json.dumps(row) + '\n')
print(f'AUDIT {tag} ok={ok} bad={bad} unresolved={unres} lean_rc={r.returncode}')
if r.returncode != 0: print(txt[-4000:])
