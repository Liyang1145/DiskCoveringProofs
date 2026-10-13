"""Tight numeric sup of ring2's residual over the admissible domain (C844 constraint satisfied),
versus the bound certify_middle_inward.py stores for factor 22."""
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


def lhs_rhs(a, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q < qmin:
        return None
    h = R * math.sqrt(q) / 2
    k = math.sqrt(max(0.0, 1 - h * h))
    lhs = u * v * (k * math.sin(a) - h * math.cos(a))
    rhs = max(tmin2, u * u, v * v) * h
    return lhs, rhs


def F(a, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None
    w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    return (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * a - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * a + hr * pi + (hl + hr) * w / 2)


best = (-1e18, None)
N = 200
for ka in range(1, N + 1):
    a = pi * ka / N
    for ku in range(1, N + 1):
        u = ku / N
        for kv in range(1, N + 1):
            v = kv / N
            lr = lhs_rhs(a, u, v)
            if lr is None or lr[0] < lr[1]:
                continue
            val = F(a, u, v)
            if val is not None and val > best[0]:
                best = (val, (a, u, v))
print(f'coarse sup over admissible domain = {best[0]:+.9f} at {tuple(round(x,4) for x in best[1])}')

a0, u0, v0 = best[1]
for step, span in [(1e-2, 40), (1e-3, 40), (1e-4, 40)]:
    improved = best
    for ia in range(-span, span + 1):
        a = a0 + ia * step
        for iu in range(-span, span + 1):
            u = u0 + iu * step
            for iv in range(-span, span + 1):
                v = v0 + iv * step
                lr = lhs_rhs(a, u, v)
                if lr is None or lr[0] < lr[1]:
                    continue
                val = F(a, u, v)
                if val is not None and val > improved[0]:
                    improved = (val, (a, u, v))
    best = improved
    a0, u0, v0 = best[1]
    print(f'  refined (step {step:g}): {best[0]:+.9f} at {tuple(round(x,6) for x in best[1])}')

stored = json.loads((LEAD / 'middle_inward_bound_22.json').read_text())['upper']
print()
print(f'admissible sup of ring2 residual   = {best[0]:+.9f}')
print(f'stored bound for factor 22 (corner)= {stored:+.9f}')
print(f'stored - sup                       = {stored - best[0]:+.6f}')
print(f'=> stored bound is {"SOUND" if stored >= best[0] - 1e-9 else "NOT a valid upper bound"}')
