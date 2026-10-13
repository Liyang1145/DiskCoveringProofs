"""Verify the ring1 value at/around the lead's control point with the control's own indices
(dl=z[96], el=z[97], i=1). Includes a local sweep to confirm it is a genuine maximum region and
not a formula artifact, and prints every term."""
import json, math
from pathlib import Path

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
ctrl = json.loads((LEAD / 'ring1_direct_control.json').read_text())
a0, u0, v0 = ctrl['point']
R, R2 = 0.38, 0.38 ** 2
i = 1
mu, d, e = z[i], z[32 + 2 * i], z[33 + 2 * i]
C = z[71] + (z[72] if i >= 3 else 0)
dl, el = z[96], z[97]
hl, hr = z[113], z[114]


def F(a, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None
    w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    return (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * a - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * a + hr * math.pi + (hl + hr) * w / 2)


print('term-by-term at the control point (dl=z96, el=z97):')
q = u0 * u0 + v0 * v0 - 2 * u0 * v0 * math.cos(a0)
w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
beta = math.atan2(v0 * math.sin(a0), u0 - v0 * math.cos(a0))
parts = [
    ('R2uv sin a/2', R2 * u0 * v0 * math.sin(a0) / 2),
    ('(w-sin w)/2', (w - math.sin(w)) / 2),
    ('C w', C * w),
    ('-mu a', -mu * a0),
    ('-d u^2', -d * u0 * u0),
    ('-e v^2', -e * v0 * v0),
    ('-dl u', -dl * u0),
    ('-el v', -el * v0),
    ('(hl-hr) beta', (hl - hr) * beta),
    ('-hr a', -hr * a0),
    ('hr pi', hr * math.pi),
    ('(hl+hr) w/2', (hl + hr) * w / 2),
]
for k, t in parts:
    print(f'   {k:14s} {t:+.9f}')
mine = sum(t for _, t in parts)
print(f'   {"TOTAL":14s} {mine:+.12f}   control = {ctrl["value"]:+.12f}   '
      f'diff = {mine - ctrl["value"]:+.6f}')

print('\nlocal sweep (grid 41^3 around the control point, step 5e-3 in a, 2e-3 in u,v):')
best = (-1e18, None)
for ia in range(-20, 21):
    a = a0 + ia * 5e-3
    for iu in range(-20, 21):
        u = u0 + iu * 2e-3
        for iv in range(-20, 21):
            v = v0 + iv * 2e-3
            if not (0 < a <= math.pi and 0 < u <= 1 and 0 < v <= 1):
                continue
            val = F(a, u, v)
            if val is not None and val > best[0]:
                best = (val, (a, u, v))
print(f'  local max = {best[0]:+.12f} at (a,u,v) = {tuple(round(x, 6) for x in best[1])}')
print(f'  control value = {ctrl["value"]:+.12f}')
if best[0] > ctrl['value']:
    print(f'  => a point within 0.1 of the control point attains {best[0]:.6f}, which is '
          f'{best[0] - ctrl["value"]:+.6f} ABOVE the control value.')
