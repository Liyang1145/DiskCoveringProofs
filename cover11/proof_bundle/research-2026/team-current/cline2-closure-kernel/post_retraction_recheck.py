"""Post-retraction recheck: the corner arithmetic is now reproduced exactly (my report's
indices/domain were wrong). Question that remains: does the corner value bound the residual the
CODE's filter actually admits?

Code facts:
 * ring factors are built with the kernel index map (hl=z[112+i], hr=z[113+i]); for i=2 that is
   z[114], z[115]  -- but line 21/22 of certify_middle_inward.py uses a specific i=2 form.
 * the corner is installed on domain [(75/76), 1] (line 23): a ONE-dimensional box.
 * the filter (lines 15-17) only deletes boxes violating the C844 necessary condition;

Here: evaluate ring2's residual (kernel index map, AND the lead's hl=z113/hr=z114 variant) at
points satisfying the code's own filter, inside the box [0,pi]x[0,1]x[0,1].
"""
import json, math
from pathlib import Path

LEAD = Path(__file__).resolve().parents[1] / 'lead'
z = [float(v) for v in json.loads((LEAD / 'middle_inward_frozen.json').read_text())['z']]
pi = math.pi
R = 0.38
R2 = R * R
i = 2
qmin = 4 * math.sin(pi - 8 * math.asin(R)) ** 2 / R2
tmin2 = (75.0 / 76.0) ** 2
STORED = json.loads((LEAD / 'middle_inward_bound_22.json').read_text())['upper']
print(f'stored factor-22 bound = {STORED:+.9f}')
print(f'qmin = {qmin:.9f},  (75/76)^2 = {tmin2:.9f}\n')


def data(alpha, u, v, hl_idx=114, hr_idx=115):
    mu, d, e = z[i], z[32 + 2 * i], z[33 + 2 * i]
    C = z[71] + (z[72] if i >= 3 else 0)
    dl, el = z[94 + 2 * i], z[95 + 2 * i]
    hl, hr = z[hl_idx], z[hr_idx]
    q = u * u + v * v - 2 * u * v * math.cos(alpha)
    w = 2 * math.asin(min(1.0, R * math.sqrt(max(q, 0)) / 2))
    beta = math.atan2(v * math.sin(alpha), u - v * math.cos(alpha))
    val = (R2 * u * v * math.sin(alpha) / 2 + (w - math.sin(w)) / 2 + C * w
           - mu * alpha - d * u * u - e * v * v - dl * u - el * v
           + (hl - hr) * beta - hr * alpha + hr * pi + (hl + hr) * w / 2)
    h = R * math.sqrt(max(q, 0)) / 2
    k = math.sqrt(max(0.0, 1 - h * h))
    lhs = u * v * (k * math.sin(alpha) - h * math.cos(alpha))
    rhs = max(tmin2, u * u, v * v) * h
    return dict(q=q, w=w, val=val, lhs=lhs, rhs=rhs, slack=lhs - rhs)


for (a, u, v) in [(0.595211, 0.1927, 0.2175), (0.6, 0.2, 0.2), (0.6, 0.19, 0.22),
                  (0.62, 0.193, 0.216)]:
    for hli, hri, tag in [(114, 115, 'kernel map hl=z114,hr=z115'),
                          (113, 114, 'lead variant hl=z113,hr=z114')]:
        d = data(a, u, v, hli, hri)
        feasible = (d['q'] >= qmin) and (d['slack'] >= 0)
        flag = 'PASSES filter' if feasible else 'filter-blocked'
        over = d['val'] - STORED
        print(f'(a,u,v)=({a},{u},{v}) [{tag}]')
        print(f'   q={d["q"]:.6f} (>=qmin {d["q"]>=qmin})  lhs-rhs={d["slack"]:+.6e} -> {flag}')
        print(f'   ring2 residual={d["val"]:+.9f}   stored bound={STORED:+.9f}   '
              f'residual-bound={over:+.6f}  {"EXCEEDS STORED" if over>0 else "ok"}')
    print()
