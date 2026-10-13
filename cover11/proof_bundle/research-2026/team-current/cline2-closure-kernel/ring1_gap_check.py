"""Confirm the ring1 gap: value of the ring1 residual at the scan argmax, computed with the
kernel's own ring-1 coefficients (both candidate linear-slack maps), plus filter status."""
import json, math
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
pi = math.pi
R = 0.38
R2 = R * R
qmin = 4 * math.sin(pi - 8 * math.asin(R)) ** 2 / R2
tmin2 = (75.0 / 76.0) ** 2
i = 1


def coefs(dl_block):
    """dl_block='z94' -> kernel literal dl=z[94+2i]; 'z73' -> the alternative block"""
    mu = z[i]
    d = z[32 + 2 * i]
    e = z[33 + 2 * i]
    C = z[71] + (z[72] if i >= 3 else 0)
    if dl_block == 'z94':
        dl, el = z[94 + 2 * i], z[95 + 2 * i]
    else:
        dl, el = z[73 + 2 * i], z[74 + 2 * i]
    hl, hr = z[112 + i], z[113 + i]
    return mu, d, e, C, dl, el, hl, hr


def F(a, u, v, blk):
    mu, d, e, C, dl, el, hl, hr = coefs(blk)
    q = u * u + v * v - 2 * u * v * math.cos(a)
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
    return (q, u * v * (k * math.sin(a) - h * math.cos(a)) - max(tmin2, u * u, v * v) * h)


stored = json.loads((LEAD / 'middle_inward_bound_21.json').read_text())
print('stored ring1: upper =', stored['upper'], ' lower_probe =', stored['lower_probe'])
print()
for blk in ('z94', 'z73'):
    mu, d, e, C, dl, el, hl, hr = coefs(blk)
    print(f"map dl-block={blk}: mu={mu:+.6f} d={d:+.6f} e={e:+.6f} C={C:+.6f} "
          f"dl={dl:+.6f} el={el:+.6f} hl={hl:+.6f} hr={hr:+.6f}")
print()
for (a, u, v) in [(0.21476, 0.6078, 1.0), (0.198, 0.63, 1.0), (0.0494, 0.5, 0.52)]:
    f = filt(a, u, v)
    print(f'point (a,u,v)=({a},{u},{v}): q={f[0]:.6f} q>=qmin={f[0] >= qmin} '
          f'filter-slack={f[1]:+.3e} -> {"passes" if f[1] >= 0 else "blocked"}')
    for blk in ('z94', 'z73'):
        val = F(a, u, v, blk)
        print(f'    ring1 residual [{blk}] = {val:+.9f}   stored upper = {stored["upper"]:+.9f}   '
              f'val-stored = {val - stored["upper"]:+.6f}')
    print()
