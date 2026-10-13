"""run_fixed_sweep.py  (member upper-audit/twohub-kernel-audit, 2026-09-26)

Bounded re-run of the CURRENT (fixed) py/certify_ring2.py sweep at the recorded
threshold (thr_scale = 1.0) with a larger box budget than the recorded run used.
Writes nothing except this member's log (run() has no file side effects; main() is
never called).  Purpose: does the fixed kernel close the fixed-configuration
certificate, and with what worst-leaf ratio?

Run: py -3 -B py/run_fixed_sweep.py <max_boxes> <max_depth>
"""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
TWO_HUB = os.path.join(ROOT, 'research-2026', 'n12-global', 'members', 'two-hub')
sys.path.insert(0, os.path.join(TWO_HUB, 'py'))

import certify_ring2 as cr

mb = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
md = int(sys.argv[2]) if len(sys.argv) > 2 else 14
W, meta = cr.load_weights()
c = cr.Cert(W, dps=25)
t0 = time.time()
res = c.run(max_boxes=mb, max_depth=md, verbose=True)
print('=== summary (fixed kernel, thr_scale=1.0, max_boxes=%d, max_depth=%d) ===' % (mb, md))
for k in ('nbox', 'leaves', 'unsolved', 'maxdepth', 'worst_leaf_ub', 'worst_any_ub',
          'thr_scale', 'secs'):
    print('   %-14s %s' % (k, res[k]))
print('   worst_leaf_box %s' % (res['worst_leaf_box'],))
print('   margin_ratio   %s' % res['margin_ratio'])
print('   fail_examples  %s' % (res['fail_examples'],))
print('wall %.1f s' % (time.time() - t0))
