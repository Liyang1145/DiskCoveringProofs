"""Quantify: is the line-22 corner value a sound upper bound for ring2's factor on the domain
that the filter actually leaves admissible?

Filter (lines 15-17) discards a box iff  uv(k sin a - h cos a) < max(75/76^2,u^2,v^2) h
everywhere in it. So the surviving domain is a superset of the admissible set:
    D = {(a,u,v): a in (0,pi], u,v in (0,1], uv(k sin a - h cos a) >= max((75/76)^2,u^2,v^2) h}.
We compute sup of the ring2 residual over D and compare with the corner value -1.552226.
"""
import json, math
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
pi = math.pi
R = 0.38
R2 = R * R
i = 2
mu, d, e = z[i], z[32 + 2 * i], z[33 + 2 * i]
C = z[71] + (z[72] if i >= 3 else 0)
dl, el = z[94 + 2 * i], z[95 + 2 * i]
hl, hr = z[112 + i], z[113 + i]
tmin2 = (75.0 / 76.0) ** 2
qmin = 4 * math.sin(pi - 8 * math.asin(R)) ** 2 / R2


def admissible(a, u, v, use_filter=True):
    if not (0 < a <= pi and 0 < u <= 1 and 0 < v <= 1):
        return False
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q < qmin:
        return False
    h = R * math.sqrt(q) / 2
    k = math.sqrt(max(0.0, 1 - h * h))
    if use_filter:
        lhs = u * v * (k * math.sin(a) - h * math.cos(a))
        rhs = max(tmin2, u * u, v * v) * h
        if lhs < rhs:
            return False
    return True


def F(a, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None
    w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    return (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * a - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * a + hr * pi + (hl + hr) * w / 2)


corner_max = max((2 * math.asin(min(1.0, R * t)) - math.sin(2 * math.asin(min(1.0, R * t)))) / 2
                 - z[i] * pi
                 - (z[32 + 2 * i] + z[33 + 2 * i]) * t * t
                 - (z[94 + 2 * i] + z[95 + 2 * i]) * t
                 + (z[71] + (z[113] + z[114]) / 2) * 2 * math.asin(min(1.0, R * t))
                 for t in [75 / 76 + (1 - 75 / 76) * k / 2000 for k in range(2001)])
print(f'corner formula max on t in [75/76,1] = {corner_max:+.9f}')

print('\nsup of ring2 residual over the filter-surviving domain D:')
mx, arg = -1e18, None
N = 120
for ka in range(0, N + 1):
    a = pi * ka / N
    for ku in range(0, N + 1):
        u = ku / N
        for kv in range(0, N + 1):
            v = kv / N
            if not admissible(a, u, v):
                continue
            val = F(a, u, v)
            if val is not None and val > mx:
                mx, arg = val, (a, u, v)
print(f'  coarse N={N}: sup = {mx:+.9f} at (a,u,v) = {tuple(round(x, 5) for x in arg)}')
print(f'  corner bound                    = {corner_max:+.9f}')
print(f'  deficit (sup - corner)          = {mx - corner_max:+.6f}')
print(f'  => corner is a sound upper bound for the whole domain? {corner_max >= mx - 1e-9}')

print('\nrefinement around the argmax:')
a0, u0, v0 = arg
best = (-1e18, None)
for ia in range(-60, 61):
    a = a0 + ia * 1e-3
    for iu in range(-60, 61):
        u = u0 + iu * 2e-3
        for iv in range(-60, 61):
            v = v0 + iv * 2e-3
            if not admissible(a, u, v):
                continue
            val = F(a, u, v)
            if val is not None and val > best[0]:
                best = (val, (a, u, v))
print(f'  refined sup = {best[0]:+.9f} at (a,u,v) = {tuple(round(x, 5) for x in best[1])}')
print(f'  deficit     = {best[0] - corner_max:+.6f}')
