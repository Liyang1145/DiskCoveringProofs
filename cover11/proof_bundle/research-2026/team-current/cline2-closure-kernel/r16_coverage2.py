"""R16: derive the Cartesian hub disk geometry from the code that builds it, then re-test
whether the polar (delta, both-roots) set covers the same arc.

Source of truth: interval_hub_boundary.setup uses
    disks = [(r sin2b1, -r cos2b1, r), (r sin2b2, r cos2b2, r), (s, 0, 1-r)]
    circle(theta,j): c = (cx,cy) + rho (cos th, sin th); reject if c inside any other disk
    wedge: t + v tan b2 >= 0, v tan b1 - t >= 0
The Cartesian control sweeps j=2 with theta in [-pi,pi].
"""
import math, sys

sys.stdout.reconfigure(encoding='utf-8', errors='replace')


def cart_legal(r, b1, b2, th):
    s = math.sqrt(1 - r * r)
    disks = [(r * math.sin(2 * b1), -r * math.cos(2 * b1), r),
             (r * math.sin(2 * b2), r * math.cos(2 * b2), r),
             (s, 0.0, 1 - r)]
    cx, cy, rho = disks[2]
    v = cx + rho * math.cos(th)
    t = cy + rho * math.sin(th)
    if v <= 0:
        return None
    for i, (dx, dy, rr) in enumerate(disks):
        if i == 2:
            continue
        if (v - dx) ** 2 + (t - dy) ** 2 > rr * rr + 1e-12:
            return None
    if t + v * math.tan(b2) < -1e-12:
        return None
    if v * math.tan(b1) - t < -1e-12:
        return None
    return (v, t)


print('legal Cartesian points (j=2 sweep) and their polar representation')
print(f'{"r":>7} {"b1":>7} {"b2":>7} {"#leg":>6} {"|t|<=s?":>8} {"delta range":>22} '
      f'{"covered":>8}')
for (r, b1, b2) in [(0.375, 1.0, 1.0), (0.38, 1.1863995522992576, 1.1863995522992576),
                    (0.375, 1.1864, 1.1864), (0.379, 1.0, 1.1864),
                    (0.375, 1.05, 1.18), (0.38, 1.0, 1.0)]:
    s = math.sqrt(1 - r * r)
    nleg = 0
    bad_y = bad_de = bad_root = cov = 0
    dmin, dmax = 9.9, -9.9
    sample_bad = []
    for k in range(8000):
        th = -math.pi + 2 * math.pi * k / 8000
        p = cart_legal(r, b1, b2, th)
        if p is None:
            continue
        nleg += 1
        v, t = p
        if abs(t) > s + 1e-12:
            bad_y += 1
            if len(sample_bad) < 2:
                sample_bad.append(('|t|>s', round(v, 4), round(t, 4)))
            continue
        de = math.asin(max(-1.0, min(1.0, t / s)))
        dmin = min(dmin, de); dmax = max(dmax, de)
        if not (-b2 - 1e-9 <= de <= b1 + 1e-9):
            bad_de += 1
            if len(sample_bad) < 2:
                sample_bad.append(('de-out', round(v, 4), round(t, 4), round(de, 5)))
            continue
        hit = False
        for sg in (+1, -1):
            rad = (1 - r) ** 2 - s * s * math.sin(de) ** 2
            if rad < 0:
                continue
            X = s * math.cos(de) + sg * math.sqrt(rad)
            Y = s * math.sin(de)
            if abs(X - v) < 1e-9 and abs(Y - t) < 1e-9:
                hit = True
                break
        if hit:
            cov += 1
        else:
            bad_root += 1
            if len(sample_bad) < 2:
                sample_bad.append(('root', round(v, 4), round(t, 4), round(de, 5)))
    rng = f'[{dmin:+.4f},{dmax:+.4f}]' if nleg else 'n/a'
    print(f'{r:>7.4f} {b1:>7.4f} {b2:>7.4f} {nleg:>6d} '
          f'{("y-bad=" + str(bad_y)) if bad_y else "ok":>8} {rng:>22} {cov:>8d}'
          f'   de-out={bad_de} root-bad={bad_root}')
    for e in sample_bad:
        print('        ', e)
