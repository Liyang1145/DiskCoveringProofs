"""R22 clean: derive the exact feasible A-interval from G and compare with the lead's proposal.

Use the code's own form (face_totalangle_jet.legal):
    G = 1 - s(sin2b + sin2A) - r cos(2(b+A)) <= 0
which I verified is identical to the lead's G = 1 - s sin2b - (s - r sin2b) sin2A - r cos2b cos2A
(max difference 3.9e-16 over 2000 points).

Identity:  G = 1 - s sin2b - ( s sin2A + r cos2b cos2A - r sin2b sin2A )
             = 1 - s sin2b - [ u sin2A + v cos2A ]        with u = s - r sin2b, v = r cos2b
             = 1 - s sin2b - d sin(2A + gamma),           d = hypot(u,v), gamma = atan2(v,u)
The lead writes it with cos; both are the same object with the right phase convention, which is
what we pin down here.
"""
import math, sys, random
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

L = 0.60946080763725372899


def G(r, b, A):
    s = math.sqrt(1 - r * r)
    return 1 - s * (math.sin(2 * b) + math.sin(2 * A)) - r * math.cos(2 * (b + A))


rng = random.Random(5)
print('=== the exact identity: G = 1 - s sin2b - d sin(2A + gamma) ===')
worst = 0.0
for _ in range(3000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    A = rng.random() * 2 * b
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b); v = r * math.cos(2 * b)
    d = math.hypot(u, v); g = math.atan2(v, u)
    worst = max(worst, abs(G(r, b, A) - (1 - s * math.sin(2 * b) - d * math.sin(2 * A + g))))
print(f'  max discrepancy = {worst:.3e}   (identity confirmed)')

print()
print('=== feasible set: G <= 0  <=>  d sin(2A+gamma) >= 1 - s sin2b = c ===')
print('    (a) c > 0 and d > c ; (b) sin(2A+gamma) >= c/d = sin(theta), theta = asin(c/d)')
mnc = 9
for _ in range(2000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    s = math.sqrt(1 - r * r)
    c = 1 - s * math.sin(2 * b)
    mnc = min(mnc, c)
print(f'    min c = {mnc:.9f} > 0 : {mnc > 0}')
print('    => feasible  <=>  2A+gamma in [theta, pi-theta] (mod 2pi)')
print('       => A in [ (theta-gamma)/2 , (pi-theta-gamma)/2 ]  (mod pi)')
print('    the mod-pi image gives a second band shifted by pi/2; inside (0,T) with T < 2 < pi')
print('    only the first band can appear, provided (pi-theta-gamma)/2 < T.')

print()
print('=== set equality test: exact feasible {A in (0,T): G<=0}  vs  [max(0,a-), min(T,a+)] ===')
bad = 0
tested = 0
for _ in range(1500):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    b2 = L + rng.random() * (1 - L)
    T = b + b2
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b); v = r * math.cos(2 * b)
    c = 1 - s * math.sin(2 * b)
    d = math.hypot(u, v); g = math.atan2(v, u)
    th = math.atan2(c, math.sqrt(d * d - c * c))
    a_m = (th - g) / 2
    a_p = (math.pi - th - g) / 2
    lo = max(0.0, a_m); hi = min(T, a_p)
    if lo > hi:
        lo = hi = (lo + hi) / 2      # empty interval convention
    N = 3000
    feas = [T * k / N for k in range(1, N) if G(r, b, T * k / N) <= 0]
    tested += 1
    if feas:
        f_lo, f_hi = min(feas), max(feas)
        if abs(f_lo - lo) > T / N + 1e-12 or abs(f_hi - hi) > T / N + 1e-12:
            bad += 1
            if bad <= 3:
                print(f'  MISMATCH r={r:.7f} b={b:.7f} T={T:.7f}: exact=[{f_lo:.9f},{f_hi:.9f}]'
                      f' proposed=[{lo:.9f},{hi:.9f}]  a-={a_m:.9f} a+={a_p:.9f}')
    else:
        if hi - lo > 1e-9:
            bad += 1
            if bad <= 3:
                print(f'  EMPTY exact but proposed nonempty: r={r:.7f} b={b:.7f} T={T:.7f} '
                      f'proposed=[{lo:.9f},{hi:.9f}]')
print(f'  tested {tested}; mismatches = {bad}')

print()
print('=== is a+ < T automatic? ===')
worst_over = -9
for _ in range(3000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    b2 = L + rng.random() * (1 - L)
    T = b + b2
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b); v = r * math.cos(2 * b)
    c = 1 - s * math.sin(2 * b)
    d = math.hypot(u, v); g = math.atan2(v, u)
    th = math.atan2(c, math.sqrt(d * d - c * c))
    a_p = (math.pi - th - g) / 2
    worst_over = max(worst_over, a_p - T)
print(f'  max (a+ - T) over 3000 random legal (r,b,T) = {worst_over:+.6f}')
print('  a+ < T is NOT automatic; the interval is nonempty only when T > a+.')
print('  the certificate must therefore require T > a+ (else no A is norm-feasible).')
