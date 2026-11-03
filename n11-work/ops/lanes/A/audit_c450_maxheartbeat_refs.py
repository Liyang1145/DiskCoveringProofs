#!/usr/bin/env python3
"""Lane A: is the `set_option maxHeartbeats 0` trio *referenced* by the chain?

Session 191 part 3 flagged three non-C450 modules in the C450 import closure
that carry a real `set_option maxHeartbeats 0` (hard-rule-#1 territory):

    N11Formalization.GridBridge
    N11Formalization.DrowBallBox_compIvBoxBox   (namespace ...DrowBallBox)
    N11Formalization.Ladder49_jt_kkt_z          (namespace ...Ladder49)

`audit_c450_import_paths.py` already showed all three are import-REACHABLE from
the chain roots.  Import-reachability alone does not make them load-bearing:
their `maxHeartbeats 0` affects only their own elaboration, and the chain only
depends on them if some module in the closure *names* one of their declarations.

This tool is the source-level approximation of the referenced-declaration
closure the previous session asked for.  It BFS-closes the import graph from the
two chain roots, comment/string-strips every closure module, and searches for a
namespace-qualified reference (`GridBridge.`, `DrowBallBox.`, `Ladder49.`) or an
`open ...GridBridge` / `...DrowBallBox` / `...Ladder49`.  Any closure module
other than the three definers that matches is a module whose proof *may* be
load-bearing on a flagged module.

Scope: STATIC source scan, NOT a kernel verdict and NOT a build.  It cannot see
references that arrive purely through `open`ed unqualified names re-exported by
an intermediate module; it is a lower bound on load-bearing-ness.
"""
import hashlib, json, os, re

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
LEAN = os.path.join(REPO, 'n11-work', 'lean')
MODDIR = os.path.join(LEAN, 'N11Formalization')
ROOT = os.path.join(LEAN, 'N11Formalization.lean')
IMP = re.compile(r'^import\s+(N11Formalization\.\S+)\s*$', re.M)

ROOTS = ['N11Formalization.C450ChainCompletion',
         'N11Formalization.C450ChainCompletionMain']

# module -> the namespace whose declarations a reference would be qualified by
FLAGGED = {
    'N11Formalization.GridBridge': 'GridBridge',
    'N11Formalization.DrowBallBox_compIvBoxBox': 'DrowBallBox',
    'N11Formalization.Ladder49_jt_kkt_z': 'Ladder49',
}
QUAL = {ns: re.compile(r'\b' + ns + r'\.[A-Za-z_]') for ns in set(FLAGGED.values())}
OPEN = {ns: re.compile(r'\bopen\b[^\n]*\b' + ns + r'\b') for ns in set(FLAGGED.values())}


def refs(body, ns):
    """(qualified_use, namespace_opened) ignoring `import` lines."""
    txt = '\n'.join(l for l in body.splitlines() if not l.lstrip().startswith('import '))
    return bool(QUAL[ns].search(txt)), bool(OPEN[ns].search(txt))


def sha(p):
    with open(p, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def strip(text):
    """Remove Lean line comments, nested block comments and string/char literals."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                i += 1
            continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        elif text.startswith('/-', i):
            depth = 1; i += 2
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
        elif c == "'" and i + 2 < n and (text[i+1] != '\\') and text[i+2] == "'":
            i += 3
        else:
            out.append(c); i += 1
    return ''.join(out)


def modfile(mod):
    return os.path.join(MODDIR, mod.split('.', 1)[1] + '.lean')


def closure(roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        p = modfile(m)
        if not os.path.exists(p):
            continue
        for nxt in IMP.findall(open(p, encoding='utf-8', errors='replace').read()):
            if nxt not in seen:
                stack.append(nxt)
    return seen


seen = closure(ROOTS)
flagged_ns = set(FLAGGED.values())
qual_use = {}
opened = {}
missing = sorted(m for m in seen if not os.path.exists(modfile(m)))

for m in sorted(seen):
    p = modfile(m)
    if not os.path.exists(p):
        continue
    body = strip(open(p, encoding='utf-8', errors='replace').read())
    for ns in flagged_ns:
        q, o = refs(body, ns)
        if q:
            qual_use.setdefault(ns, []).append(m)
        if o:
            opened.setdefault(ns, []).append(m)

load_bearing = {ns: sorted(m for m in qual_use.get(ns, []) if m not in FLAGGED)
                for ns in flagged_ns}

report = {
    'scope': ('comment/string-stripped namespace-reference scan of the C450 chain '
              'import closure; STATIC lower bound, NOT a kernel verdict'),
    'root_sha256': sha(ROOT),
    'roots': ROOTS,
    'closure_size': len(seen),
    'missing_module_files': missing,
    'flagged_modules': sorted(FLAGGED),
    'qualified_use_total': {ns: sorted(ms) for ns, ms in qual_use.items()},
    'namespace_opened': {ns: sorted(ms) for ns, ms in opened.items()},
    'qualified_use_outside_definer': load_bearing,
}
out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   'c450-maxheartbeat-refs.json')
with open(out, 'w', encoding='utf-8') as f:
    json.dump(report, f, indent=1, sort_keys=True)
print('closure_size', report['closure_size'], '| missing modules', len(missing))
for ns in sorted(flagged_ns):
    q = report['qualified_use_total'].get(ns, [])
    o = report['namespace_opened'].get(ns, [])
    print(f'{ns}: {len(q)} modules with a qualified use, {len(o)} modules `open` it')
    for m in report['qualified_use_outside_definer'][ns]:
        print('    qualified-use:', m)
print('report', out)
