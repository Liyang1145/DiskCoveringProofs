"""Reproduce the lead's control value 1.4459409612312664 by varying the term choices that could
plausibly differ (dl/el block, hl/hr block, beta sign, C source, d/e block). Report which
combination reproduces it, if any."""
import json, math
from pathlib import Path

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
ctrl = json.loads((LEAD / 'ring1_direct_control.json').read_text())
a, u, v = ctrl['point']
target = ctrl['value']
R, R2 = 0.38, 0.38 ** 2
i = 1

q = u * u + v * v - 2 * u * v * math.cos(a)
w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
base = R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2
beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
print(f'q={q:.9f} w={w:.9f} beta={beta:.9f} base={base:+.9f}')
print(f'target = {target:.15f}\n')

cands = []
for dl_name, dl, el in [('z94+2i', z[94 + 2 * i], z[95 + 2 * i]),
                        ('z96/97', z[96], z[97]),
                        ('z73+2i', z[73 + 2 * i], z[74 + 2 * i]),
                        ('none', 0.0, 0.0)]:
    for h_name, hl, hr in [('z112+i', z[112 + i], z[113 + i]),
                           ('z113/114', z[113], z[114]),
                           ('none', 0.0, 0.0)]:
        for sgn_name, sgn in [('+beta', 1.0), ('-beta', -1.0)]:
            for ce_name, C in [('z71', z[71] + (z[72] if i >= 3 else 0)), ('z72', z[72])]:
                for dv_name, dd, ee in [('z32/33', z[32 + 2 * i], z[33 + 2 * i]),
                                        ('alt', z[33 + 2 * i], z[34 + 2 * i])]:
                    val = (base + C * w - z[i] * a - dd * u * u - ee * v * v
                           - dl * u - el * v + (hl - hr) * sgn * beta
                           - hr * a + hr * math.pi + (hl + hr) * w / 2)
                    cands.append((abs(val - target), val, dl_name, h_name, sgn_name,
                                  ce_name, dv_name))
cands.sort()
print('closest combinations:')
for diff, val, dn, hn, sn, cn, dvn in cands[:8]:
    print(f'  |diff|={diff:.3e}  value={val:+.12f}  dl/el={dn:7s} hl/hr={hn:7s} '
          f'{sn} C={cn} d/e={dvn}')
