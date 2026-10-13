"""L1 closed: the polar chart with v = H cos delta, t = H sin delta.

Substitution: norm distance from (s,0) to (H cos d, H sin d) with H = s cos d + sig sqrt((1-r)^2 - s^2 sin^2 d).
Verifies
  (a) H^2 - 2 s H cos d + s^2 = (1-r)^2  exactly, and hence
  (b) |(H cos d, H sin d) - (s,0)| = 1-r, with discriminant (1-r)^2 - s^2 sin^2 d
      and maxima H_max = s cos d + sqrt(...), H_min = s cos d - sqrt(...).
"""
import math, sys

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

print('(a) H^2 - 2 s H cos d + s^2 vs (1-r)^2')
print(f'{"r":>7} {"d":>7} {"H(j=2)":>14} {"lhs":>22} {"(1-r)^2":>14} {"diff":>10}')
worst = 0.0
for r in (0.375, 0.377, 0.379, 0.38):
    s = math.sqrt(1 - r * r)
    for d in (-0.5, -0.25, 0.0, 0.2, 0.4, 0.6):
        rad = (1 - r) ** 2 - s * s * math.sin(d) ** 2
        if rad < 0:
            print(f'{r:>7.4f} {d:>7.3f}   radicand<0 (discard)')
            continue
        H = s * math.cos(d) + math.sqrt(rad)
        lhs = H * H - 2 * s * H * math.cos(d) + s * s
        rhs = (1 - r) ** 2
        worst = max(worst, abs(lhs - rhs))
        print(f'{r:>7.4f} {d:>7.3f} {H:>14.9f} {lhs:>22.15f} {rhs:>14.9f} {lhs - rhs:>10.2e}')
print(f'worst |lhs - (1-r)^2| = {worst:.3e}')

print('\n(b) norm distance |(H cos d, H sin d) - (s,0)| - (1-r)')
worst2 = 0.0
for r in (0.375, 0.38):
    s = math.sqrt(1 - r * r)
    for sign in (+1, -1):
        for d in (-0.55, -0.3, 0.0, 0.3, 0.55):
            rad = (1 - r) ** 2 - s * s * math.sin(d) ** 2
            if rad < 0:
                continue
            H = s * math.cos(d) + sign * math.sqrt(rad)
            v, t = H * math.cos(d), H * math.sin(d)
            dist = math.hypot(v - s, t)
            worst2 = max(worst2, abs(dist - (1 - r)))
print(f'worst |distance - (1-r)| over both roots = {worst2:.3e}')

print('\n(c) chord consistency: t must equal H sin d, NOT s sin d')
r, d = 0.375, 0.3
s = math.sqrt(1 - r * r)
rad = (1 - r) ** 2 - s * s * math.sin(d) ** 2
H = s * math.cos(d) + math.sqrt(rad)
print(f'  r={r} d={d}: H={H:.9f}  H sin d={H*math.sin(d):.9f} vs s sin d={s*math.sin(d):.9f}'
      f'  (H sin d - s sin d = {(H-s)*math.sin(d):.9f})')
