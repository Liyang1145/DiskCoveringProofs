#!/usr/bin/env python3
"""Lane A: static top-level declaration-name collision audit for the two
restored HARK-MISSING modules (`C450ChainCompletion`, `C450ChainCompletionMain`).

When the stage-1 root uncomments both imports it imports the whole project at
once; any fully-qualified declaration name that is declared BOTH in one of the
two new modules AND in some other module reachable from the root would make the
root fail with `already declared`.  This tool builds a namespace-aware map of
top-level declarations across `n11-work/lean/N11Formalization/**` and reports
such collisions (and any duplicate *within* the two new modules).

Scope: STATIC source-text audit; NOT a kernel verdict and NOT a build.
"""
import hashlib, json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'lean', 'N11Formalization'))
NEW = ['C450ChainCompletion', 'C450ChainCompletionMain']

DECL = re.compile(
    r'^(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque|'
    r'noncomputable\s+def)\s+([A-Za-z_\u00c0-\uffff][\w\u00c0-\uffff\']*)')
NS = re.compile(r'^namespace\s+(.+?)\s*$')
END = re.compile(r'^end(?:\s+(\S+))?\s*$')


def decls_of(path):
    """Return list of fully-qualified top-level declaration names in `path`.

    Streams the file line by line so that the multi-MB generated tables
    (e.g. `Ladder49_jt_kkt_z.lean`, ~70 MB) are covered too -- the earlier
    `MAX_BYTES` skip left exactly those files out of the collision scan.
    """
    stack = []
    out = []
    try:
        fh = open(path, encoding='utf-8', errors='replace')
    except OSError:
        return out
    with fh:
        for raw in fh:
            line = raw.split('--', 1)[0]
            m = NS.match(line)
            if m and not line.lstrip().startswith('--'):
                for part in m.group(1).split():
                    stack.append(part)
                continue
            e = END.match(line)
            if e and stack:
                stack.pop()
                continue
            d = DECL.match(line.lstrip())
            if d:
                out.append('.'.join(stack + [d.group(1)]))
    return out


checks = []


def ck(ok, label):
    checks.append({'ok': bool(ok), 'label': label})


owner = {}
new_decls = {}
for name in NEW:
    p = os.path.join(LEAN, name + '.lean')
    ds = decls_of(p)
    new_decls[name] = ds
    ck(os.path.exists(p), 'module file %s.lean present' % name)
    for fq in ds:
        owner.setdefault(fq, []).append(name)

# collisions between the two new modules
within = {k: v for k, v in owner.items() if len(v) > 1}
ck(not within, 'no declaration name shared between the two new modules')

# collisions of the new modules' declarations against every other module
others = {}
scanned = {}
for fn in sorted(os.listdir(LEAN)):
    if not fn.endswith('.lean'):
        continue
    mod = fn[:-5]
    if mod in NEW:
        continue
    ds = decls_of(os.path.join(LEAN, fn))
    scanned[mod] = len(ds)
    for fq in ds:
        others.setdefault(fq, []).append(mod)

# every .lean module in the tree must have been read, incl. the multi-MB
# generated tables that an earlier size cap skipped
lean_mods = [f[:-5] for f in os.listdir(LEAN) if f.endswith('.lean')]
n_other = len([m for m in lean_mods if m not in NEW])
ck(len(scanned) == n_other,
   'every other .lean module scanned (incl. >3 MB generated tables)')
BIG = 3_000_000
large = sorted(((f[:-5], scanned[f[:-5]]) for f in os.listdir(LEAN)
                if f.endswith('.lean') and f[:-5] not in NEW
                and os.path.getsize(os.path.join(LEAN, f)) > BIG),
               key=lambda t: -os.path.getsize(os.path.join(LEAN, t[0] + '.lean')))
ck(all(m in scanned for m, _ in large),
   'all >3 MB modules covered by the scan')

new_fq = set(owner)
collide = {fq: others[fq] for fq in sorted(new_fq & set(others))}
ck(not collide,
   'no new-module declaration name already declared elsewhere in the tree')

verdict = ('PASS_C450_DECL_NO_COLLISION' if all(c['ok'] for c in checks)
           else 'FAIL_C450_DECL_COLLISION')
report = {
    'scope': 'STATIC source-text audit; NOT a kernel verdict and NOT a build',
    'verdict': verdict,
    'n_checks': len(checks),
    'n_failures': sum(1 for c in checks if not c['ok']),
    'new_modules': NEW,
    'new_decl_counts': {k: len(v) for k, v in new_decls.items()},
    'shared_between_new': within,
    'collisions_with_tree': collide,
    'n_modules_scanned': len(scanned),
    'large_modules_scanned': [
        {'module': m, 'bytes': os.path.getsize(os.path.join(LEAN, m + '.lean')),
         'n_decls': n} for m, n in large],
    'module_sha256': {n: hashlib.sha256(
        open(os.path.join(LEAN, n + '.lean'), 'rb').read()).hexdigest()
        for n in NEW},
    'checks': checks,
}
out = os.path.join(HERE, 'c450-decl-collisions.json')
json.dump(report, open(out, 'w', encoding='utf-8'), indent=1, sort_keys=True)
print('verdict:', verdict)
print('new decl counts:', report['new_decl_counts'])
print('collisions with tree:', collide)
print('failures:', [c['label'] for c in checks if not c['ok']])
print('report:', out)
