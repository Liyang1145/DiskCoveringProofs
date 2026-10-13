"""Provenance of the frozen numeric_total and the control's corner2 reference."""
import json, math
from pathlib import Path

L = Path(__file__).resolve().parents[1] / 'lead'
a = json.loads((L / 'middle_inward_exchange_best.json').read_text())
b = json.loads((L / 'middle_inward_exchange_refined_best.json').read_text())
f = json.loads((L / 'middle_inward_frozen.json').read_text())
c = json.loads((L / 'middle_inward_proposal_continuum_control.json').read_text())

print('exchange_best   total', a['numeric_total'])
print('refined_best    total', b['numeric_total'])
print('frozen          total', f['numeric_total'])
print('control corner2     ', c['corner2'])
print('control ring_optimized keys:', list(c['ring_optimized'].keys()) if isinstance(c.get('ring_optimized'), dict) else type(c.get('ring_optimized')))
print()
print('frozen z == refined z ?', all(abs(x - y) < 1e-9 for x, y in zip(f['z'], b['z'])))
print()
z = f['z']
i = 2
base = ((2 * math.asin(0.38) - math.sin(2 * math.asin(0.38))) / 2 - z[i] * math.pi
        - (z[32 + 2 * i] + z[33 + 2 * i]) + (z[71] + (z[113] + z[114]) / 2) * 2 * math.asin(0.38))
print('corner(1.0) using linear block z[98],z[99] =', base - (z[98] + z[99]))
print('control corner2                            =', c['corner2'])
for blk in [(94, 95), (73, 74), (75, 76), (52, 53)]:
    print(f'   if linear slacks were z[{blk[0]}],z[{blk[1]}] -> corner(1) = '
          f'{base - (z[blk[0]] + z[blk[1]]):+.9f}')
print()
print('ring_optimized (control) values:')
ro = c['ring_optimized']
if isinstance(ro, dict):
    for k, v in ro.items():
        print('   ', k, v)
elif isinstance(ro, list):
    for k, v in enumerate(ro):
        print('   ', k, v)
print()
print('face_switch_maxima:', c['face_switch_maxima'])
