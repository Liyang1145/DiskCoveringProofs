#!/usr/bin/env python3
"""Lane A: end-to-end wiring audit of the restored C450 telescope chain.

`C450ChainCompletion.h450` is built by a stack of applications
    C450SourceNNSegment.source(NN-1)_remaining_of_remaining (...)
starting from the vacuous `C450Source36Segment` endpoint and descending to
`C450Source11Segment`.  This tool parses the six chain modules that carry the
applications (Endpoint, Tail, Mid1, Mid2, Mid3, Completion) and checks, at the
SOURCE level, that
  (1) every segment module `C450SourceNN*Segment.lean` for NN in 11..36 exists,
  (2) every referenced transfer lemma `sourceBB_remaining_of_remaining` is
defined in the module that owns it,
  (3) the applications form a single unbroken 36 -> 11 chain with no gap or
cycle,
  (4) the 36 -> 11 descent uses exactly the 25 consecutive links.

Scope: STATIC source-text audit; NOT a kernel verdict and NOT a build.
"""
import hashlib, json, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'lean', 'N11Formalization'))
CHAIN = ['C450ChainCompletionEndpoint', 'C450ChainCompletionTail',
         'C450ChainCompletionMid1', 'C450ChainCompletionMid2',
         'C450ChainCompletionMid3', 'C450ChainCompletion']
APPLY = re.compile(
    r'C450Source(\d+)Segment\.source(\d+)_remaining_of_remaining')
DEFN = re.compile(
    r'theorem\s+source(\d+)_remaining_of_remaining')
checks = []
def ck(ok, label):
    checks.append({'ok': bool(ok), 'label': label})

# (1) segment modules present
seg_present = {}
for nn in range(11, 37):
    fn = 'C450Source%dSegment.lean' % nn
    seg_present[nn] = os.path.exists(os.path.join(LEAN, fn))
ck(all(seg_present.values()),
   'all 26 source segment modules 11..36 present on disk')

# (2)/(3)/(4) parse chain applications
# each entry: (target_seg_from_theorem, source_seg_of_lemma)
edges = []   # (lemma_owner_seg, provides_seg)
for mod in CHAIN:
    path = os.path.join(LEAN, mod + '.lean')
    text = open(path, encoding='utf-8', errors='replace').read()
    for owner, provides in APPLY.findall(text):
        edges.append((int(owner), int(provides)))

# verify each lemma is defined in its owner module
for owner, provides in edges:
    path = os.path.join(LEAN, 'C450Source%dSegment.lean' % owner)
    txt = open(path, encoding='utf-8', errors='replace').read() \
        if os.path.exists(path) else ''
    defined = ('source%d_remaining_of_remaining' % provides) in txt
    ck(defined, 'lemma source%d_remaining_of_remaining defined in '
                'C450Source%dSegment.lean' % (provides, owner))
    ck(provides == owner - 1,
       'lemma in segment %d transfers to its predecessor %d'
       % (owner, provides))

# continuity: build map provides->owner, walk 11..36
prov_to_owner = {p: o for (o, p) in edges}
chain_ok = True
missing = []
for p in range(11, 36):
    if p not in prov_to_owner:
        chain_ok = False
        missing.append(p)
ck(chain_ok, 'every step 11..35 has an of_remaining transfer')
ck(not missing, 'no gap in the 25-link descent 36->11')
ck(len(set(prov_to_owner.values())) == len(edges),
   'no duplicated transfer lemma (no ambiguous/cyclic link)')

# the descent must be exactly 36->35->...->11
covered = sorted(prov_to_owner)
ck(covered == list(range(11, 36)),
   'transfer lemma targets are exactly {11,...,35}')

verdict = 'PASS_C450_CHAIN_WIRING' if all(c['ok'] for c in checks) \
    else 'FAIL_C450_CHAIN_WIRING'
report = {
    'scope': 'STATIC source-text audit; NOT a kernel verdict and NOT a build',
    'verdict': verdict,
    'n_checks': len(checks),
    'n_failures': sum(1 for c in checks if not c['ok']),
    'chain_modules': CHAIN,
    'segment_modules_present': sum(seg_present.values()),
    'transfer_edges': len(edges),
    'transfer_lemma_targets': covered,
    'missing_targets': missing,
    'module_sha256': {m: hashlib.sha256(
        open(os.path.join(LEAN, m + '.lean'), 'rb').read()).hexdigest()
        for m in CHAIN},
    'checks': checks,
}
out = os.path.join(HERE, 'c450-chain-wiring.json')
json.dump(report, open(out, 'w', encoding='utf-8'), indent=1, sort_keys=True)
print('verdict:', verdict)
print('segment modules present:', report['segment_modules_present'], '/ 26')
print('transfer edges:', len(edges), 'targets:', covered)
print('failures:', [c['label'] for c in checks if not c['ok']])
print('report:', out)
