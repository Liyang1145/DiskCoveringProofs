"""margins.py  (member upper-audit, 2026-09-26)

Two exact margins, to quantify how tight the two sides of the n=12 diagnosis are:

  (m1) the 36 D-external offenders: exact |p|^2 - 1 (how far outside the unit disk the
       near-degenerate circumcentres are).  Disjointness is exact, but a large margin
       means the reading is robust against any upstream coordinate perturbation.
  (m2) the 328 D-meeting candidate boxes: min over boxes of ( claim^2 - min_i max_corner d2 ).
       This is the exact slack of the load-bearing inequality; compare with the claim's
       1e-30 decimal truncation and with the 1e-17 coordinate granularity.

Run: py -3 -B py/margins.py > logs/margins.txt 2>&1
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..'))
N1314 = os.path.join(ROOT, 'research-2026', 'session2', 'n1314')
sys.path.insert(0, os.path.join(N1314, 'py'))
import cert_cand
from certlib import dist_box_lo, box_outside_disk, fstr


def maxcorner_d2(box, c):
    (x0, x1), (y0, y1) = box
    return max((x - c[0]) ** 2 + (y - c[1]) ** 2 for x in (x0, x1) for y in (y0, y1))


C = cert_cand.load_frac_centers(os.path.join(N1314, 'cfg', 'cert_n12_othern.json'), 'centers_dec17', 17)
claim = F(json.load(open(os.path.join(N1314, 'out', 'cert_n12_othern.json'), encoding='utf-8'))['claim'])
print('claim = %s' % fstr(claim, 30, 'up'))

# (m1) D-external offenders
m1 = []
for name, box in cert_cand.candidates(C):
    d = min(dist_box_lo(box, C[i]) for i in range(len(C)))
    if d > claim and box_outside_disk(box):
        (x0, x1), (y0, y1) = box
        if x0 != x1 or y0 != y1:
            print('  (non-degenerate box among offenders: %s)' % name)
        p2 = ((x0 + x1) / 2) ** 2 + ((y0 + y1) / 2) ** 2
        m1.append((p2 - 1, name))
m1.sort()
print()
print('(m1) %d D-external offenders; exact |p|^2 - 1 :' % len(m1))
print('     smallest : %s   (%s)' % (m1[0][0], m1[0][1]))
print('     as decimal: %s' % fstr(m1[0][0], 30, 'down'))
print('     largest  : %s' % m1[-1][0])
print('     count with |p|^2-1 < 1e-3 : %d' % sum(1 for v, _ in m1 if v < F(1, 1000)))
print('     count with |p|^2-1 < 1e-6 : %d' % sum(1 for v, _ in m1 if v < F(1, 10 ** 6)))

# (m2) exact slack of the coverage inequality on D-meeting boxes
best = None
for name, box in cert_cand.candidates(C):
    if box_outside_disk(box):
        continue
    s = claim * claim - min(maxcorner_d2(box, C[i]) for i in range(len(C)))
    if best is None or s < best[0]:
        best = (s, name)
print()
print('(m2) 328 D-meeting boxes; min slack claim^2 - min_i max_corner d2 :')
print('     value  : %s   (box %s)' % (best[0], best[1]))
print('     decimal: %s' % fstr(best[0], 40, 'down'))
print('     >= 0 ? %s   (0 failures = the exact inequality holds for every D-meeting box)' % (best[0] >= 0))
print()
print('context: 1 ulp of a 17-decimal coordinate = 1e-17 ; claim decimal truncation = 1e-30')
