#!/usr/bin/env python3
"""Lane A: comment/string-aware hard-rule scan of the C450 chain closure.

The session-190 raw scan (audit_c450_closure_hardrules.py) regexes every
`\bsorry\b`/`\badmit\b` in the file text, so it flags modules whose *comments*
merely mention the words (e.g. Chinese header lines "无 sorry").  That produced
a ~120-module false-positive list.  This version first strips Lean line
comments, (nested) block comments and string/char literals, then scans, so the
reported list is the real one.

STATIC ONLY -- NOT a kernel verdict and NOT a build.  It does not resolve which
declarations are *referenced* by the chain proofs, only which modules in the
import closure contain real hard-rule tokens.
"""
import hashlib, json, os, re

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
LEAN = os.path.join(REPO, 'n11-work', 'lean')
MODDIR = os.path.join(LEAN, 'N11Formalization')
ROOT = os.path.join(LEAN, 'N11Formalization.lean')
IMP = re.compile(r'^import\s+(N11Formalization\.\S+)\s*$', re.M)
VIOL = re.compile(r'\b(?:sorry|admit|axiom|native_decide|ofReduceBool|implemented_by)\b'
                  r'|maxHeartbeats\s+0\b')


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


roots = ['N11Formalization.C450ChainCompletion', 'N11Formalization.C450ChainCompletionMain']
seen = closure(roots)
real, c450_real = {}, {}
for m in sorted(seen):
    p = modfile(m)
    if not os.path.exists(p):
        continue
    hits = sorted(set(m.group(0) for m in VIOL.finditer(strip(open(p, encoding='utf-8', errors='replace').read()))))
    if hits:
        real[m] = hits
        if 'C450' in m:
            c450_real[m] = hits

report = {
    'scope': 'comment/string-stripped hard-rule scan of C450 chain import closure; NOT a kernel verdict',
    'root_sha256': sha(ROOT),
    'closure_size': len(seen),
    'closure_module_sha256': {m: sha(modfile(m)) for m in sorted(seen) if os.path.exists(modfile(m))},
    'real_violations': real,
    'real_violations_in_c450_modules': c450_real,
}
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'c450-hardrules-stripped.json')
with open(out, 'w', encoding='utf-8') as f:
    json.dump(report, f, indent=1, sort_keys=True)
print('closure_size', report['closure_size'])
print('real violations total:', len(real), '| in C450 modules:', len(c450_real))
print('sample:', sorted(real)[:8])
print('report', out)
