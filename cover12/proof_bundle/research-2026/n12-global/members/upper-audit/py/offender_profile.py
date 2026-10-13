"""offender_profile.py  (member upper-audit, 2026-09-26)

Profile of the 36 recorded "uncovered" candidates of n12_othern:
  * candidate kind histogram (far* / bis* / circ*)
  * how many of them are disjoint from D (exact filter)
  * how many D-external candidates exist by kind
  * value range (min/max of the exact rational min_i dist_box_lo)
Run: py -3 -B py/offender_profile.py > logs/offender_profile.txt 2>&1
"""
import json, os, sys
from fractions import Fraction as F
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..'))
N1314 = os.path.join(ROOT, 'research-2026', 'session2', 'n1314')
sys.path.insert(0, os.path.join(N1314, 'py'))
import cert_cand
from certlib import dist_box_lo, fstr, box_outside_disk


def kind(name):
    return 'far' if name.startswith('far') else ('bis' if name.startswith('bis') else 'circ')


C = cert_cand.load_frac_centers(os.path.join(N1314, 'cfg', 'cert_n12_othern.json'), 'centers_dec17', 17)
claim = F(json.load(open(os.path.join(N1314, 'out', 'cert_n12_othern.json'), encoding='utf-8'))['claim'])
cand = cert_cand.candidates(C)

off_kind = Counter(); out_kind = Counter()
vals = []
for name, box in cand:
    d = min(dist_box_lo(box, C[i]) for i in range(len(C)))
    outside = box_outside_disk(box)
    if outside:
        out_kind[kind(name)] += 1
    if d > claim:
        off_kind[kind(name)] += 1
        vals.append((kind(name), name, d, outside))
print('candidates total                       :', len(cand))
print('kind histogram (all)                   :', dict(Counter(kind(n) for n, _ in cand)))
print('candidates disjoint from D, by kind    :', dict(out_kind))
print('recorded offenders (d > claim), by kind:', dict(off_kind))
print('offenders that are disjoint from D     :', sum(1 for _, _, _, o in vals if o), '/', len(vals))
print('offender value range (exact rationals) :',
      fstr(min(v[2] for v in vals), 25, 'down'), ' .. ', fstr(max(v[2] for v in vals), 25, 'down'))
print('  (claim = %s)' % fstr(claim, 30, 'up'))
print()
print('all 36 offenders, in candidate order:')
for k, name, d, o in vals:
    print('   %-12s %-45s %s' % (k, name, fstr(d, 20, 'down')))
