"""Pin the exact term that differs between my evaluation and the lead's control, then stop."""
import json, math
from pathlib import Path

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
ctrl = json.loads((LEAD / 'ring1_direct_control.json').read_text())
a, u, v = ctrl['point']
target = ctrl['value']
R, R2, i = 0.38, 0.38 ** 2, 1

q = u * u + v * v - 2 * u * v * math.cos(a)
w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
fixed = (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 - z[i] * a
         - z[32 + 2 * i] * u * u - z[33 + 2 * i] * v * v
         + (z[113] - z[114]) * beta - z[114] * a + z[114] * math.pi
         + (z[113] + z[114]) * w / 2)
print(f'fixed part (all terms except dl*u and el*v) = {fixed:+.12f}')
print(f'target total = {target:+.12f}')
need = target - fixed
print(f'=> required  -dl*u - el*v  = {need:+.12f}')
print(f'    with u={u!r}, v={v!r}:  dl*u + el*v = {-need:+.12f}')
print()
print('candidate blocks for the linear slacks (i=1):')
for nm, dli, eli in [('z94+2i / z95+2i', 96, 97), ('z96 / z97 explicit', 96, 97),
                     ('z73+2i / z74+2i', 75, 76), ('z74 / z75 explicit', 75, 76)]:
    dval = -z[dli] * u - z[eli] * v
    print(f'   {nm:22s} dl=z[{dli}]={z[dli]:+.9f} el=z[{eli}]={z[eli]:+.9f} '
          f'-> -dl u - el v = {dval:+.9f}')
print()
print('spread of z[73:101] (adjacent pairs for i=1):')
for k in range(73, 101):
    print(f'   z[{k}] = {z[k]:+.9f}')
