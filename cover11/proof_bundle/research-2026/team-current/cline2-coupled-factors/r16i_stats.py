import json
from pathlib import Path
P = Path(r'research-2026/team-current/cline2-coupled-factors')
d = json.loads((P/'out/r16h_endpoints.json').read_text())
both = [r for r in d if r['tag_hi'] == 'face1-cap&face2-cap']
print('cases where BOTH caps are tight at the maximum:', len(both))
for r in both[:8]:
    print(f"   r={r['r']} b1={r['b1']:.5f} b2={r['b2']:.5f} dhi={r['dhi']:.6f} "
          f"(b1-b2={r['b1']-r['b2']:+.5f})")
if both:
    print('   |b1-b2| min %.2e max %.2e' % (min(abs(r['b1']-r['b2']) for r in both),
                                             max(abs(r['b1']-r['b2']) for r in both)))
    print('   dhi min %.6f max %.6f' % (min(r['dhi'] for r in both), max(r['dhi'] for r in both)))
only_f1 = [r for r in d if r['tag_hi'] == 'face1-cap']
print()
print('cases with only face1-cap tight at the max:', len(only_f1))
if only_f1:
    print('   |b1-b2| min %.3f max %.3f' % (min(abs(r['b1']-r['b2']) for r in only_f1),
                                             max(abs(r['b1']-r['b2']) for r in only_f1)))
atdom = [r for r in d if abs(r['dhi']-r['b1']) < 1e-9]
print()
print('maxima at the delta-domain end (dhi == b1):', len(atdom), 'of', len(d))
lo_dom = [r for r in d if abs(r['dlo']+r['b2']) < 1e-9]
print('lower ends at delta = -b2 (domain end):', len(lo_dom), 'of', len(d))
