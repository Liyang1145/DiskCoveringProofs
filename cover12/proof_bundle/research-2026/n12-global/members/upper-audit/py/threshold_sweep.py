"""threshold_sweep.py  (member upper-audit, 2026-09-26)

Calls the ORIGINAL py/cert_batch.candidate_coverage (read-only import) on the recorded
configurations at three thresholds:
    claim,  claim - 1e-9,  claim - 1e-6
and prints (n_cand, n_checked, n_uncovered).  Purpose: document that the filtered
counter is the one quoted in out/STATUS.md section 4 ("claim - 1e-9 => 19/29/25" for
n=13/14/17) and that it has discriminating power, whereas the historical JSON field
(no domain filter) is a different counter.

Run:  py -3 -B py/threshold_sweep.py > logs/threshold_sweep.txt 2>&1
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..'))
N1314 = os.path.join(ROOT, 'research-2026', 'session2', 'n1314')
sys.path.insert(0, os.path.join(N1314, 'py'))

import cert_cand
import cert_batch

TAGS = [('n12_othern', 'cert_n12_othern.json'), ('n13_v1', 'cert_n13_v1.json'),
        ('n14_v1', 'cert_n14_v1.json'), ('n15_v1', 'cert_n15_v1.json'),
        ('n16_v1', 'cert_n16_v1.json'), ('n17_v1', 'cert_n17_v1.json'),
        ('n18_v1', 'cert_n18_v1.json')]

print('cert_batch.candidate_coverage semantics (current source): boxes NOT disjoint from D are the only ones checked;')
print('n_checked counts those; n_uncovered counts the ones among THEM with min_i dist_box_lo > r.')
print()
print('%-11s %-26s %8s %9s %11s' % ('tag', 'threshold', 'n_cand', 'n_checked', 'n_uncovered'))
for tag, cfg in TAGS:
    C = cert_cand.load_frac_centers(os.path.join(N1314, 'cfg', cfg), 'centers_dec17', 17)
    claim = F(json.load(open(os.path.join(N1314, 'out', 'cert_%s.json' % tag), encoding='utf-8'))['claim'])
    for label, r in (('claim', claim), ('claim-1e-9', claim - F(1, 10 ** 9)),
                     ('claim-1e-6', claim - F(1, 10 ** 6))):
        cov = cert_batch.candidate_coverage(C, r)
        print('%-11s %-26s %8d %9d %11d' % (tag, label, cov['n_cand'], cov['n_checked'], cov['n_uncovered']))
    print()
