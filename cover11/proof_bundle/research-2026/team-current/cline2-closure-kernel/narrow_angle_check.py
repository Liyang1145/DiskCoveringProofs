"""Verify the lead's narrow-angle finding: maxima of ring1/ring3 near alpha ~ 0.05.

Frozen duals; kernel index map (mu=z[i], d=z[32+2i], e=z[33+2i], dl=z[94+2i], el=z[95+2i],
hl=z[112+i], hr=z[113+i], C=z[71]+(z[72] if i>=3)).

Question: is there a point with alpha ~ 0.05 and q >= qmin where the ring residual exceeds the
interval bound stored in middle_inward_bound_21.json / _23.json?
"""
import json, math
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
pi = math.pi
R = 0.38
R2 = R * R
qmin = 4 * math.sin(pi - 8 * math.asin(R)) ** 2 / R2
tmin2 = (75.0 / 76.0) ** 2
print(f'qmin = {qmin:.9f}')


def params(i):
    return (z[i], z[32 + 2 * i], z[33 + 2 * i], z[71] + (z[72] if i >= 3 else 0),
            z[94 + 2 * i], z[95 + 2 * i], z[112 + i], z[113 + i])


def F(i, a, u, v):
    mu, d, e, C, dl, el, hl, hr = params(i)
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None
    w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    return (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * a - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * a + hr * pi + (hl + hr) * w / 2)


def filt(a, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q < qmin:
        return None
    h = R * math.sqrt(q) / 2
    k = math.sqrt(max(0.0, 1 - h * h))
    return u * v * (k * math.sin(a) - h * math.cos(a)) - max(tmin2, u * u, v * v) * h


stored = {}
for fi, nm in [(21, 'ring1'), (23, 'ring3')]:
    p = LEAD / f'middle_inward_bound_{fi:02d}.json'
    if p.exists():
        stored[nm] = json.loads(p.read_text())['upper']
print('stored interval bounds:', stored)

print('\nscan: alpha in (0, 0.20], u,v in [0.05,1], q>=qmin, filter-slack >= 0')
for nm, i in [('ring1', 1), ('ring3', 3)]:
    best = (-1e18, None)
    best_nofilter = (-1e18, None)
    for ka in range(1, 401):
        a = 0.20 * ka / 400
        for ku in range(1, 101):
            u = ku / 100
            for kv in range(1, 101):
                v = kv / 100
                val = F(i, a, u, v)
                if val is None:
                    continue
                q = u * u + v * v - 2 * u * v * math.cos(a)
                if q < qmin:
                    continue
                if val > best_nofilter[0]:
                    best_nofilter = (val, (a, u, v))
                s = filt(a, u, v)
                if s is not None and s >= 0 and val > best[0]:
                    best = (val, (a, u, v))
    print(f'\n  {nm}: stored upper = {stored.get(nm)}')
    print(f'    max (filter-satisfying): {best[0]:+.9f} at (a,u,v)='
          f'{tuple(round(x,6) for x in best[1])}')
    print(f'    max (q>=qmin only)     : {best_nofilter[0]:+.9f} at (a,u,v)='
          f'{tuple(round(x,6) for x in best_nofilter[1])}')
    if nm in stored:
        print(f'    stored - max(filter)   : {stored[nm] - best[0]:+.6f}'
              f'   {"OK" if stored[nm] >= best[0] else "*** BELOW ATTAINED ***"}')

print('\nrefine the argmax for each ring:')
for nm, i in [('ring1', 1), ('ring3', 3)]:
    a0, u0, v0 = None, None, None
    best = (-1e18, None)
    for ka in range(1, 401):
        a = 0.20 * ka / 400
        for ku in range(1, 101):
            u = ku / 100
            for kv in range(1, 101):
                v = kv / 100
                val = F(i, a, u, v)
                if val is None:
                    continue
                q = u * u + v * v - 2 * u * v * math.cos(a)
                if q < qmin:
                    continue
                s = filt(a, u, v)
                if s is not None and s >= 0 and val > best[0]:
                    best = (val, (a, u, v))
    a0, u0, v0 = best[1]
    for step in (1e-3, 1e-4, 1e-5):
        for ia in range(-20, 21):
            a = a0 + ia * step
            for iu in range(-20, 21):
                u = u0 + iu * step
                for iv in range(-20, 21):
                    v = v0 + iv * step
                    if not (0 < a <= pi and 0 < u <= 1 and 0 < v <= 1):
                        continue
                    val = F(i, a, u, v)
                    if val is None:
                        continue
                    q = u * u + v * v - 2 * u * v * math.cos(a)
                    if q < qmin:
                        continue
                    s = filt(a, u, v)
                    if s is not None and s >= 0 and val > best[0]:
                        best = (val, (a, u, v))
        a0, u0, v0 = best[1]
    print(f'  {nm}: refined max {best[0]:+.9f} at (a,u,v)='
          f'{tuple(round(x,7) for x in best[1])}  filter-slack={filt(*best[1]):+.3e}')
