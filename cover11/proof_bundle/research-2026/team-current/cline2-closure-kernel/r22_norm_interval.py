"""R22: independent audit of the norm-feasible A-interval formula.

Claim (lead): for r in [.379,.37999], b in [L, 1] with L = .60946080763725372899, T in [2L, 2],
the set of A with 0 < A < T and  G <= 0  is exactly
   [ a- , a+ ]  intersect (0,T),      a- = (theta-gamma)/2 ,  a+ = (pi-theta-gamma)/2
where u = s - r sin2b, v = r cos2b, c = 1 - s sin2b, d = hypot(u,v), gamma = atan2(v,u),
theta = atan2(c, sqrt(d^2-c^2)), s = sqrt(1-r^2), and
G = 1 - s sin2b - (s - r sin2b) sin2A - r cos2b cos2A <= 0.

Checks: (a) G equals the exact norm residual 1 - |X|^2 - r^2 + 2r|X|cos delta (up to the
factor r/2 and orientation) at sample points; (b) the feasible A-set equals the proposed interval;
(c) the sign claims d^2 - c^2 = s sin2b (2(1-r) - s sin2b) > 0, u > 0; (d) the atan2 branches;
(e) the cap/wedge claims.
"""
import math, sys, random
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

L = 0.60946080763725372899


def Gfun(r, b, A):
    s = math.sqrt(1 - r * r)
    return 1 - s * math.sin(2 * b) - (s - r * math.sin(2 * b)) * math.sin(2 * A) \
        - r * math.cos(2 * b) * math.cos(2 * A)


def normresid(r, b, A):
    """exact residual: X = (s,0) + (1-r)(cos th, sin th) with the face constraint |X-Q1|=2r? 
    Instead use the direct hub-norm form: G should equal (r/2)(1 - |hub|^2 ... ) - verify by
    the algebra: G = 1 - s sin2b - ... and the hub point from the face-1 arc."""
    # hub point on the face-1 arc parametrised by A:
    v = r * (math.sin(2 * b) + math.sin(2 * A))
    t = r * (math.cos(2 * A) - math.cos(2 * b))
    # in the C858 frame the norm disk is |c| <= 1-r with c = (v, t) + (s, 0)?  Use the exact
    # relation derived in the audit: 1 - |c|^2 where c is the hub centre in the centred frame.
    # Exact identity:  r*(s*sin2b + s*sin2A + r*cos2(b+A)) = 1 - |c|^2  (to be tested)
    s = math.sqrt(1 - r * r)
    return r * (s * math.sin(2 * b) + s * math.sin(2 * A) + r * math.cos(2 * (b + A))) - (1 - r * r)


def proposed(r, b, T):
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b)
    v = r * math.cos(2 * b)
    c = 1 - s * math.sin(2 * b)
    d = math.hypot(u, v)
    gamma = math.atan2(v, u)
    theta = math.atan2(c, math.sqrt(max(0.0, d * d - c * c)))
    a_m = (theta - gamma) / 2
    a_p = (math.pi - theta - gamma) / 2
    return a_m, a_p, u, v, c, d, gamma, theta


print('=== (a) G == the exact norm residual (up to a constant factor) ===')
rng = random.Random(7)
worst = 0.0
for _ in range(400):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    A = rng.random() * 2 * b
    g = Gfun(r, b, A)
    nr = normresid(r, b, A)
    # relation to determine empirically: is g - (1 - |c|^2)/something proportional?
    worst = max(worst, abs(g))
worst_diff = 0.0
for _ in range(400):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    A = rng.random() * 2 * b
    g = Gfun(r, b, A)
    s = math.sqrt(1 - r * r)
    # candidate: g  ==  1 - |c|^2  where |c|^2 = 1 - r*s*(sin2b+sin2A) - r^2 cos2(b+A)
    c2 = 1 - r * s * (math.sin(2 * b) + math.sin(2 * A)) - r * r * math.cos(2 * (b + A))
    worst_diff = max(worst_diff, abs(g - (1 - c2)))
print(f'  max |G - (1 - |c|^2)| over 400 random legal points = {worst_diff:.3e}')
print('  (if ~0 then G is exactly the norm residual, i.e. G <= 0  <=>  |c|^2 <= 1)')

print()
print('=== (b) feasible A-set vs the proposed interval ===')
rng = random.Random(11)
bad = 0
tested = 0
for _ in range(300):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    T = 2 * L + rng.random() * (2 - 2 * L)
    if not (2 * L <= T <= 2):
        continue
    if b + (T - b) != T:
        continue
    # T must be b1+b2 with b1=b and b2=T-b in [L,1]
    b2 = T - b
    if not (L <= b2 <= 1):
        continue
    a_m, a_p, u, v, c, d, gamma, theta = proposed(r, b, T)
    lo = max(0.0, a_m)
    hi = min(T, a_p)
    # exact feasible set by dense sampling of A in (0,T)
    feas = []
    N = 4000
    for k in range(1, N):
        A = T * k / N
        if Gfun(r, b, A) <= 0:
            feas.append(A)
    tested += 1
    if feas:
        f_lo, f_hi = min(feas), max(feas)
        # compare with the proposed interval
        if abs(f_lo - lo) > T / N + 1e-12 or abs(f_hi - hi) > T / N + 1e-12:
            bad += 1
            if bad <= 3:
                print(f'  MISMATCH r={r:.6f} b={b:.6f} T={T:.6f}: '
                      f'exact=[{f_lo:.9f},{f_hi:.9f}] proposed=[{lo:.9f},{hi:.9f}]')
    else:
        if lo < hi:
            bad += 1
            print(f'  EMPTY exact but proposed nonempty: r={r:.6f} b={b:.6f} T={T:.6f} '
                  f'proposed=[{lo:.9f},{hi:.9f}]')
print(f'  tested {tested} random legal (r,b,T); mismatches = {bad}')

print()
print('=== (c) sign claims ===')
w1 = w2 = 1e9
for _ in range(2000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b)
    v = r * math.cos(2 * b)
    c = 1 - s * math.sin(2 * b)
    d2 = u * u + v * v
    claimed = s * math.sin(2 * b) * (2 * (1 - r) - s * math.sin(2 * b))
    w1 = min(w1, d2 - c * c)
    w2 = min(w2, u)
    if abs((d2 - c * c) - claimed) > 1e-12:
        print(f'  d^2-c^2 identity mismatch at r={r} b={b}: {d2-c*c:.12f} vs {claimed:.12f}')
print(f'  min (d^2 - c^2) = {w1:.9e}  (>0 required)')
print(f'  min u            = {w2:.9e}  (>0 required)')
print('  => d^2 - c^2 = s sin2b (2(1-r) - s sin2b) > 0 and u > 0 on the whole domain: '
      f'{w1 > 0 and w2 > 0}')

print()
print('=== (d) branches and ranges ===')
mn_g, mx_g, mn_t, mx_t = 9, -9, 9, -9
for _ in range(4000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    a_m, a_p, u, v, c, d, gamma, theta = proposed(r, b, 2 * b)
    mn_g, mx_g = min(mn_g, gamma), max(mx_g, gamma)
    mn_t, mx_t = min(mn_t, theta), max(mx_t, theta)
print(f'  gamma in [{mn_g:+.6f},{mx_g:+.6f}] rad  (atan2(v,u), v can be negative: branch open)')
print(f'  theta in [{mn_t:+.6f},{mx_t:+.6f}] rad  (atan2(c, +sqrt): branch [0,pi/2], c>0)')
print(f'  theta in (0,pi/2): {mn_t > 0 and mx_t < math.pi/2}')
print(f'  a- >= 0 always?  {min((proposed(0.3795,b,2*b)[0]) for b in [L,0.7,0.8,0.9,1.0]):+.6f}')
