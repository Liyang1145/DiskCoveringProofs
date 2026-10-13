"""R16 central check: is the polar (delta, both-roots) cover equivalent to the Cartesian
(theta in [-pi,pi]) sweep of the same saturated norm circle?

Cartesian (certify_norm_cartesian_control.py / interval_hub_norm_cartesian.py):
    c = (s,0) + (1-r)(cos th, sin th),  v = c_v, t = c_t, atan2(t - s, v)
Polar (interval_hub_saturated.py branches j=2,3):
    H = s cos de ± sqrt((1-r)^2 - s^2 sin^2 de),  t = s sin de,   de in [-b2, b1]

Claim to test: for every legal (r,b1,b2) and every theta, there is de in [-b2,b1] and a root
sign giving the same point.
"""
import math

R0 = 0.38


def cart_point(s, r, th):
    return (s + (1 - r) * math.cos(th), (1 - r) * math.sin(th))


def polar_point(s, r, de, sign):
    rad = (1 - r) ** 2 - s * s * math.sin(de) ** 2
    if rad < 0:
        return None
    return (s * math.cos(de) + sign * math.sqrt(rad), s * math.sin(de))


def delta_of(s, r, p):
    """the delta implied by the polar parametrisation for a point p=(v,t) on the circle"""
    v, t = p
    return math.atan2(t, v) if False else math.asin(max(-1.0, min(1.0, t / s)))


print('r     b1     b2     | theta sweep: max |delta| required, and coverage by [-b2,b1]')
print('-' * 88)
bad = []
for r in (0.375, 0.376, 0.377, 0.378, 0.379, 0.3799):
    s = math.sqrt(1 - r * r)
    for (b1, b2) in [(1.0, 1.0), (1.05, 1.0), (1.0, 1.1), (1.1864, 1.1864),
                     (1.18, 1.05), (1.05, 1.18)]:
        need_lo, need_hi = 0.0, 0.0
        missing = 0
        N = 2000
        for k in range(N + 1):
            th = -math.pi + 2 * math.pi * k / N
            v, t = cart_point(s, r, th)
            # legal filters used by the cartesian kernel:
            if v <= 0:
                continue
            # wedge constraints: t + v tan(b2) >= 0 and v tan(b1) - t >= 0
            if t + v * math.tan(b2) < -1e-12:
                continue
            if v * math.tan(b1) - t < -1e-12:
                continue
            # polar delta for this point
            if abs(t) > s:
                missing += 1
                continue
            de = math.asin(t / s)
            okde = (-b2 - 1e-12) <= de <= (b1 + 1e-12)
            found = False
            if okde:
                for sg in (+1, -1):
                    p = polar_point(s, r, de, sg)
                    if p and abs(p[0] - v) < 1e-9 and abs(p[1] - t) < 1e-9:
                        found = True
                        break
            if not found:
                missing += 1
            # also require the polar root to be inside the two face disks (as the kernel asserts)
        print(f'{r:<6.4f}{b1:<7.4f}{b2:<7.4f} missing={missing}')
        if missing:
            bad.append((r, b1, b2, missing))
print()
print('configurations with any uncovered legal cartesian point:', bad if bad else 'none')

print('\n=== direct test at the certificate corner values ===')
for (r, b1, b2) in [(0.375, 1.0, 1.0), (0.38, 1.1863995522992576, 1.1863995522992576),
                    (0.375, 1.1863995522992576, 1.0)]:
    s = math.sqrt(1 - r * r)
    miss = []
    for k in range(4001):
        th = -math.pi + 2 * math.pi * k / 4000
        v, t = cart_point(s, r, th)
        if v <= 0:
            continue
        if t + v * math.tan(b2) < -1e-12 or v * math.tan(b1) - t < -1e-12:
            continue
        if abs(t) > s:
            miss.append(('|t|>s', th, v, t)); continue
        de = math.asin(t / s)
        if not (-b2 - 1e-12 <= de <= b1 + 1e-12):
            miss.append(('delta-out-of-range', th, v, t, de))
            continue
        hit = any(polar_point(s, r, de, sg) and
                  abs(polar_point(s, r, de, sg)[0] - v) < 1e-9 for sg in (+1, -1))
        if not hit:
            miss.append(('root-mismatch', th, v, t, de))
    print(f'  r={r}, b1={b1:.6f}, b2={b2:.6f}: uncovered legal points = {len(miss)}')
    for m in miss[:3]:
        print('     e.g.', m)
