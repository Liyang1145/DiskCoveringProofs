#!/usr/bin/env python3
"""Lane A: static gates for the CI-pending q0(5,8) Lean modules.

Catches cheap CI-red modes before a kernel run: forbidden hard-rule tokens
(comment/string-aware), missing direct imports, and namespace balance.
STATIC ONLY -- NOT a kernel verdict and NOT a build.
"""
import hashlib, json, os, re

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
MODDIR = os.path.join(REPO, 'n11-work', 'lean', 'N11Formalization')
MODULES = ['N11Formalization.Q0Degree5SourceData',
           'N11Formalization.Q0Degree5ClosureExtension']
IMP = re.compile(r'^import\s+(\S+)\s*$', re.M)
VIOL = re.compile(r'\b(?:sorry|admit|axiom|native_decide|ofReduceBool|implemented_by)\b'
                  r'|maxHeartbeats\s+0\b')


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def strip(text):
    out, i, n, depth = [], 0, len(text), 0
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
            j = text.find('\n', i); i = n if j < 0 else j
        elif text.startswith('/-', i):
            depth = 1; i += 2
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
        else:
            out.append(c); i += 1
    return ''.join(out)


def path_of(mod):
    if mod.startswith('N11Formalization.'):
        return os.path.join(MODDIR, mod.split('.', 1)[1] + '.lean')
    return None  # Mathlib / other dependency, not checked here


report = {'scope': 'static gate for CI-pending q0(5,8) modules; NOT a kernel verdict',
          'modules': {}, 'failures': []}
for mod in MODULES:
    p = path_of(mod)
    raw = open(p, encoding='utf-8').read()
    code = strip(raw)
    viol = VIOL.findall(code)
    missing = [m for m in IMP.findall(raw)
               if path_of(m) is not None and not os.path.exists(path_of(m))]
    opens = len(re.findall(r'^namespace\s+\S+', code, re.M))
    ends = len(re.findall(r'^end\s+\S+', code, re.M))
    report['modules'][mod] = {'sha256': sha(p), 'forbidden_tokens': viol,
                              'missing_local_imports': missing,
                              'namespace_open': opens, 'namespace_end': ends}
    if viol or missing or opens != ends:
        report['failures'].append(mod)

out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'q0-degree5-static.json')
with open(out, 'w', encoding='utf-8') as f:
    json.dump(report, f, indent=1, sort_keys=True)
print('modules', len(report['modules']), 'failures', report['failures'])
for m, d in report['modules'].items():
    print(' ', m, 'viol', d['forbidden_tokens'], 'missing', d['missing_local_imports'],
          'ns', d['namespace_open'], '/', d['namespace_end'])
print('report', out)
