#!/usr/bin/env python3
"""Lane A: does the lane-A root import *add* any maxHeartbeats-0 exposure?

Session-191 audits flagged three `set_option maxHeartbeats 0` modules inside the
C450 chain closure (GridBridge, DrowBallBox_compIvBoxBox, Ladder49_jt_kkt_z) and
showed GridBridge is qualified-referenced by 8 modules outside its definer.

This tool answers the only question that matters for the HARD RULE: is that
exposure *introduced* by uncommenting the two HARK-MISSING chain imports, or is
it already present in the stage-1 root?  If the root already imports the trio
directly, then the chain import adds no new maxHeartbeats-0 surface and the LEAD
is pre-existing / non-blocking for the lane-A root edit.

Scope: STATIC import scan of the frozen root file, NOT a kernel verdict.
"""
import hashlib, json, os, re
REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..'))
ROOT = os.path.join(REPO, 'n11-work', 'lean', 'N11Formalization.lean')
IMP = re.compile(r'^import\s+(N11Formalization\.\S+)\s*$', re.M)
TRIO = ['N11Formalization.GridBridge',
        'N11Formalization.DrowBallBox_compIvBoxBox',
        'N11Formalization.Ladder49_jt_kkt_z']
text = open(ROOT, encoding='utf-8', errors='replace').read()
imports = set(IMP.findall(text))
report = {
 'scope': 'STATIC direct-import scan of frozen stage-1 root; NOT a kernel verdict',
 'root_sha256': hashlib.sha256(open(ROOT, 'rb').read()).hexdigest(),
 'flagged_trio': TRIO,
 'root_imports_flagged_directly': {m: (m in imports) for m in TRIO},
 'root_import_count': len(imports),
}
report['lane_a_root_edit_adds_new_maxheartbeat_exposure'] = \
    any(m not in imports for m in TRIO)
out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   'c450-root-maxheartbeat-exposure.json')
json.dump(report, open(out, 'w', encoding='utf-8'), indent=1, sort_keys=True)
for m in TRIO:
    print('root imports', m, '->', m in imports)
print('chain root edit adds new maxHeartbeats-0 exposure:',
      report['lane_a_root_edit_adds_new_maxheartbeat_exposure'])
print('report', out)
