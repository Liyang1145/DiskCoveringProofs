"""R16: does the polar (delta, both roots) parametrisation cover the same norm-circle arc(s) as
the Cartesian theta sweep, on the legal set (all three disks + wedge + |c|=(1-r))?

Cartesian: c = (s,0) + (1-r)(cos th, sin th),  y = (1-r) sin th
Polar:     y = s sin(de),  x = s cos(de) + sigma*sqrt((1-r)^2 - s^2 sin^2 de),  de in [-b2,b1]
Test: for each legal Cartesian theta, de := asin(y/s) must exist and lie in [-b2,b1], and some
polar root must reproduce the point.
"""
import math, sys

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
r_lo, r_hi = 0.375, 0.38


def legal(c, r, b1, b2):
    x, y = c
    if x <= 0:
        return False
    rr = 1 - r
    # on the norm circle (up to fp)
    if abs(math.hypot(x - math.sqrt(1 - r * r), y) - rr) > 1e-9:
        return False
    disks = [(r * math.sin(2 * b1), -r * math.cos(2 * b1), r),
             (r * math.sin(2 * b2), r * math.cos(2 * b2), r)]
    for (cx, cy, rho) in disks:
        if (x - cx) ** 2 + (y - cy) ** 2 > rho * rho + 1e-12:
            return False
    # wedge: t + v tan b2 >= 0 and v tan b1 - t >= 0
    if y + x * math.tan(b2) < -1e-12:
        return False
    if x * math.tan(b1) - y < -1e-12:
        return False
    return True


print(f'{"r":>7} {"b1":>7} {"b2":>7} {"#legal":>7} {"#cov":>6} {"#uncov":>7}  delta-range needed')
tot_bad = 0
for r in (0.375, 0.376, 0.378, 0.38):
    s = math.sqrt(1 - r * r)
    for (b1, b2) in [(1.0, 1.0), (1.1864, 1.1864), (1.05, 1.15), (1.15, 1.05)]:
        nleg = ncov = nunc = 0
        dmin, dmax = 9.9, -9.9
        examples = []
        for k in range(4000):
            th = -math.pi + 2 * math.pi * k / 4000
            x = s + (1 - r) * math.cos(th)
            y = (1 - r) * math.sin(th)
            if not legal((x, y), r, b1, b2):
                continue
            nleg += 1
            if abs(y) > s + 1e-12:
                nunc += 1
                if len(examples) < 2:
                    examples.append(('|y|>s', round(x, 4), round(y, 4)))
                continue
            de = math.asin(max(-1.0, min(1.0, y / s)))
            dmin = min(dmin, de); dmax = max(dmax, de)
            if -b2 - 1e-9 <= de <= b1 + 1e-9:
                ok = False
                for sg in (+1, -1):
                    rad = (1 - r) ** 2 - s * s * math.sin(de) ** 2
                    if rad < 0:
                        continue
                    X = s * math.cos(de) + sg * math.sqrt(rad)
                    Y = s * math.sin(de)
                    if abs(X - x) < 1e-9 and abs(Y - y) < 1e-9:
                        ok = True
                        break
                if ok:
                    ncov += 1
                else:
                    nunc += 1
                    if len(examples) < 2:
                        examples.append(('root-mismatch', round(x, 4), round(y, 4), de))
            else:
                nunc += 1
                if len(examples) < 2:
                    examples.append(('de-out-of-range', round(x, 4), round(y, 4), de))
        tot_bad += nunc
        rng = f'[{dmin:+.4f},{dmax:+.4f}]' if nleg else 'n/a'
        print(f'{r:>7.4f} {b1:>7.4f} {b2:>7.4f} {nleg:>7d} {ncov:>6d} {nunc:>7d}  {rng}')
        for e in examples:
            print('        e.g.', e)
print()
print('total uncovered legal points:', tot_bad)
