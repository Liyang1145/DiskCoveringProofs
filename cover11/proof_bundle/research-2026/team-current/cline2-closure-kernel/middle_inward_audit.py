"""Two focused checks on lead/certify_middle_inward.py.

Check 1: is the line-22 'corner' formula an upper bound for ring2's actual (3-D) factor?
         corner(t) is the value of the ring2 functional on the 1-D slice (alpha=pi, u=v=t).
         Substituting a slice-only bound for a 3-D factor bound is sound iff
             sup_{3-D box} F_ring2  <=  max_t corner(t).
Check 2: does the assembly constant + sum(per-factor bounds) reproduce the frozen numeric_total?
"""
import json, math
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
HERE = Path(__file__).resolve().parent
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
pi = math.pi
R = 0.38
R2 = R * R
i = 2
mu, d, e = z[i], z[32 + 2 * i], z[33 + 2 * i]
C = z[71] + (z[72] if i >= 3 else 0)
dl, el = z[94 + 2 * i], z[95 + 2 * i]
hl, hr = z[112 + i], z[113 + i]
print(f'ring2 duals: mu={mu:+.9f} d={d:+.9f} e={e:+.9f} C={C:+.9f} '
      f'dl={dl:+.9f} el={el:+.9f} hl={hl:+.9f} hr={hr:+.9f}')
qmin = 4 * math.sin(pi - 8 * math.asin(R)) ** 2 / R2


def F(alpha, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(alpha)
    if q <= qmin:
        return None
    w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
    beta = math.atan2(v * math.sin(alpha), u - v * math.cos(alpha))
    return (R2 * u * v * math.sin(alpha) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * alpha - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * alpha + hr * pi + (hl + hr) * w / 2)


def corner(t):
    w = 2 * math.asin(min(1.0, R * t))
    return ((w - math.sin(w)) / 2 - z[i] * pi
            - (z[32 + 2 * i] + z[33 + 2 * i]) * t * t
            - (z[94 + 2 * i] + z[95 + 2 * i]) * t
            + (z[71] + (z[113] + z[114]) / 2) * w)


# --- Check 1 -----------------------------------------------------------------------------
print('\nCheck 1: sup of the ring2 functional over the 3-D box vs max_t corner(t)')
mx, arg = -1e18, None
N = 160
for ka in range(0, N + 1):
    a = pi * ka / N
    for ku in range(0, N + 1):
        u = ku / N
        for kv in range(0, N + 1):
            v = kv / N
            val = F(a, u, v)
            if val is not None and val > mx:
                mx, arg = val, (a, u, v)
cmax = max(corner(0.375 + (1.0 - 0.375) * k / 400) for k in range(401))
print(f'  sup_3D  F_ring2            = {mx:+.9f} at (a,u,v)={tuple(round(x,4) for x in arg)}')
print(f'  max_t   corner(t)          = {cmax:+.9f}')
print(f'  corner >= sup_3D ? {cmax >= mx - 1e-9}   deficit (sup_3D - corner) = {mx - cmax:+.6f}')

# --- Check 2 -----------------------------------------------------------------------------
print('\nCheck 2: assembly')
const = (pi * (sum(z[:9]) + 2 * sum(z[9:11]) + sum(z[50:71]) - 2 * z[71] - 2 * z[72])
         + 2 * z[72] * math.asin(2 * R) - pi * sum(z[112:]))
print(f'  constant part            = {const:.9f}')
print(f'  frozen numeric_total     = 3.14123003341214')
need = 3.14123003341214 - const
print(f'  implied sum of bounds    = {need:.9f}')
tot = 0.0
for fi in range(29):
    f = LEAD / f'middle_inward_bound_{fi:02d}.json'
    if f.exists():
        tot += json.loads(f.read_text())['upper']
print(f'  actual sum of written bounds (indices 0..28 present) = {tot:.9f}')
print(f'  constant + written sum   = {const + tot:.9f}')
print(f'  difference from frozen   = {const + tot - 3.14123003341214:+.6f}')
