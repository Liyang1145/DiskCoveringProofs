"""Is the line-22 corner formula a valid bound for ring22, and is the total still a dual?

Builds ring22's residual coefficient-by-coefficient from the FROZEN z (same index convention
the kernel uses: mu=z[i], d=z[32+2i], e=z[33+2i], dl=z[94+2i], el=z[95+2i], hl=z[112+i],
hr=z[113+i], C=z[71]), then checks:
  (i)  corner(t) vs ring22_residual(pi,t,t)         [slice consistency]
  (ii) corner-dual feasibility: is  R_corner(alpha,u,v) >= 0 on the box?
       (this is what turns the corner number into a usable dual bound)
  (iii) max of the corner-dual residual over the box (what the 1-D B&B actually reports)
"""
import json, math
from pathlib import Path
from mpmath import iv

LEAD = Path(__file__).resolve().parents[1] / 'lead'
HERE = Path(__file__).resolve().parent
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
R = 0.38
R2 = R * R
pi = math.pi
i = 2
mu, d, e = z[i], z[32 + 2 * i], z[33 + 2 * i]
C = z[71] + (z[72] if i >= 3 else 0)
dl, el = z[94 + 2 * i], z[95 + 2 * i]
hl, hr = z[112 + i], z[113 + i]
print('ring22 kernel-style coefficients (frozen z):')
print(f'  mu={mu:+.9f} d={d:+.9f} e={e:+.9f} C={C:+.9f} dl={dl:+.9f} el={el:+.9f} '
      f'hl={hl:+.9f} hr={hr:+.9f}')


def w_of_q(q):
    return 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))


def ring22(alpha, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(alpha)
    if q <= 0:
        return None
    w = w_of_q(q)
    beta = math.atan2(v * math.sin(alpha), u - v * math.cos(alpha))
    return (R2 * u * v * math.sin(alpha) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * alpha - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * alpha + hr * pi + (hl + hr) * w / 2)


def corner_t(t):
    """the line-22 formula restricted to the slice (alpha=pi, u=v=t)"""
    w = 2 * math.asin(min(1.0, R * t))
    return ((w - math.sin(w)) / 2 - z[i] * pi
            - (z[32 + 2 * i] + z[33 + 2 * i]) * t * t
            - (z[94 + 2 * i] + z[95 + 2 * i]) * t
            + (z[71] + (z[113] + z[114]) / 2) * w)


print('\n(i) slice consistency: corner(t) vs ring22(pi,t,t)')
worst = 0.0
for k in range(0, 41):
    t = 0.375 + 0.625 * k / 40
    r2 = ring22(pi, t, t)
    c = corner_t(t)
    if r2 is None:
        print(f'  t={t:.6f}: ring22 None; corner={c:+.9f}')
        continue
    dif = c - r2
    worst = min(worst, dif)
    if k % 5 == 0 or abs(dif) > 1e-3:
        print(f'  t={t:.6f}: ring22={r2:+.9f}  corner={c:+.9f}  corner-ring22={dif:+.3e}')
print(f'  worst (corner - ring22) on the slice = {worst:+.3e}')

print('\n(ii) corner-dual feasibility: min over the box of R_corner(alpha,u,v)')
# R_corner = same functional as ring22 but with the corner multipliers; since the functional is
# built from the SAME coefficients (checked above), feasibility equals min of ring22 >= 0 on the
# admissible set with the internal alpha=pi/u=v restriction replaced by the full box.
mn = (1e9, None)
for ka in range(1, 241):
    a = pi * ka / 240
    for ku in range(1, 101):
        u = ku / 100
        for kv in range(1, 101):
            v = kv / 100
            q = u * u + v * v - 2 * u * v * math.cos(a)
            if q <= 0:
                continue
            val = ring22(a, u, v)
            if val < mn[0]:
                mn = (val, (a, u, v))
print(f'  min ring22 functional over the box = {mn[0]:+.9f} at '
      f'(a,u,v)={tuple(round(x,5) for x in mn[1])}')
print(f'  => corner-dual feasible (min>=0)? {mn[0] >= 0}')

print('\n(iii) max of the same functional over the box (what the 1-D B&B should bound)')
mx = (-1e9, None)
for ka in range(0, 121):
    a = pi * ka / 120
    for ku in range(0, 41):
        u = ku / 40
        for kv in range(0, 41):
            v = kv / 40
            if u * u + v * v - 2 * u * v * math.cos(a) <= 0:
                continue
            val = ring22(a, u, v)
            if val is not None and val > mx[0]:
                mx = (val, (a, u, v))
print(f'  max = {mx[0]:+.9f} at (a,u,v)={tuple(round(x,5) for x in mx[1])}')
print(f'  corner 1-D max on t in [0.375,1] = '
      f'{max(corner_t(0.375 + 0.625*k/200) for k in range(201)):+.9f}')
