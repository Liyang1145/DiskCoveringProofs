"""Final check: reproduce the lead's ring1_direct_control value at the debug point.
dl=z[96], el=z[97] (i=1), all other indices per the kernel's 94-base map.
"""
import json, math
from pathlib import Path

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
ctrl = json.loads((LEAD / 'ring1_direct_control.json').read_text())
a, u, v = ctrl['point']
print('control:', ctrl)
print(f'point (a,u,v) = ({a!r}, {u!r}, {v!r})')
print('dl_index', ctrl['dl_index'], 'el_index', ctrl['el_index'])

R = 0.38
R2 = R * R
i = 1
mu = z[i]
d = z[32 + 2 * i]
e = z[33 + 2 * i]
C = z[71] + (z[72] if i >= 3 else 0)
dl = z[ctrl['dl_index']]
el = z[ctrl['el_index']]
hl = z[112 + i]
hr = z[113 + i]
print(f'mu=z[{i}]={mu:+.9f} d=z[{32+2*i}]={d:+.9f} e=z[{33+2*i}]={e:+.9f} C={C:+.9f}')
print(f'dl=z[{ctrl["dl_index"]}]={dl:+.9f} el=z[{ctrl["el_index"]}]={el:+.9f} '
      f'hl=z[{112+i}]={hl:+.9f} hr=z[{113+i}]={hr:+.9f}')

q = u * u + v * v - 2 * u * v * math.cos(a)
w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
terms = {
    'R2uv sin a/2': R2 * u * v * math.sin(a) / 2,
    '(w - sin w)/2': (w - math.sin(w)) / 2,
    'Cw': C * w,
    '-mu a': -mu * a,
    '-d u^2': -d * u * u,
    '-e v^2': -e * v * v,
    '-dl u': -dl * u,
    '-el v': -el * v,
    '(hl-hr) b': (hl - hr) * beta,
    '-hr a': -hr * a,
    'hr pi': hr * math.pi,
    '(hl+hr) w/2': (hl + hr) * w / 2,
}
val = sum(terms.values())
for k, t in terms.items():
    print(f'   {k:16s} {t:+.9f}')
print()
print(f'q={q:.9f}  w={w:.9f}  beta={beta:.9f}')
print(f'my value    = {val:.15f}')
print(f'control     = {ctrl["value"]:.15f}')
print(f'difference  = {val - ctrl["value"]:+.3e}')
