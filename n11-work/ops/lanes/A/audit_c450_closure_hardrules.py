#!/usr/bin/env python3
"""STATIC audit of the lane-A C450 chain closure (session 190+).

Checks, without building:
  * root carries exactly the two HARK-MISSING import lines;
  * both requested modules exist;
  * the full import closure of C450ChainCompletion + C450ChainCompletionMain
    has no hard-rule violations (sorry/admit/axiom/native_decide/
    ofReduceBool/implemented_by/maxHeartbeats 0);
  * all 36 C450 segment modules are inside that closure.
Scope: STATIC only -- NOT a kernel verdict.
"""
import hashlib, json, os, re

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
LEAN = os.path.join(REPO, 'n11-work', 'lean')
MODDIR = os.path.join(LEAN, 'N11Formalization')
ROOT = os.path.join(LEAN, 'N11Formalization.lean')
VIOL = re.compile(r'\b(sorry|admit)\b|\bnative_decide\b|\bofReduceBool\b|\bimplemented_by\b|\baxiom\b|maxHeartbeats\s+0\b')
IMP = re.compile(r'^import\s+(N11Formalization\.\S+)\s*$', re.M)

def sha(p):
    with open(p, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()

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
        for nxt in IMP.findall(open(p, encoding='utf-8').read()):
            if nxt not in seen:
                stack.append(nxt)
    return seen

report = {'scope': 'STATIC import-closure + hard-rule scan; NOT a kernel verdict'}
root = open(ROOT, encoding='utf-8').read()
report['root_sha256'] = sha(ROOT)
missing = re.findall(r'(?m)^-- HARK-MISSING.*?: import (N11Formalization\.\S+)\s*$', root)
report['root_hark_missing_imports'] = missing
report['root_hark_missing_count'] = len(missing)

roots = ['N11Formalization.C450ChainCompletion', 'N11Formalization.C450ChainCompletionMain']
report['roots_present'] = {r: os.path.exists(modfile(r)) for r in roots}
seen = closure(roots)
report['closure_size'] = len(seen)
viols, hashes = {}, {}
for m in sorted(seen):
    p = modfile(m)
    if not os.path.exists(p):
        continue
    txt = open(p, encoding='utf-8').read()
    hashes[m] = sha(p)
    hits = sorted(set(VIOL.findall(txt)))
    if hits:
        viols[m] = hits
report['hard_rule_violations'] = viols
named = ['First','Second','Third','Fourth','Fifth','Sixth','Seventh','Eighth','Ninth','Tenth']
segs = ['N11Formalization.C450%sSegment' % n for n in named]
segs += ['N11Formalization.C450Source%dSegment' % i for i in range(11, 37)]
missing_segs = [s for s in segs if s not in seen]
report['segment_count_expected'] = len(segs)
report['segments_missing_from_closure'] = missing_segs
report['closure_module_sha256'] = hashes
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'c450-closure-hardrules.json')
with open(out, 'w', encoding='utf-8') as f:
    json.dump(report, f, indent=1, sort_keys=True)
ok = (report['root_hark_missing_count'] == 2 and not viols and not missing_segs
      and all(report['roots_present'].values()))
print('VERDICT', 'PASS_STATIC' if ok else 'FAIL_STATIC')
print('hark_missing', report['root_hark_missing_count'], 'closure_size', report['closure_size'])
print('violations', viols)
print('segments_missing', missing_segs)
print('report', out)
