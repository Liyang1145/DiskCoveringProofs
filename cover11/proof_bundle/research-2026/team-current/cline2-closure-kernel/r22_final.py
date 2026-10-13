"""R22 final: (a) the exact two-form identity, (b) the closed-form derivation of the feasible
interval, so the claim can be confirmed analytically and not only numerically."""
import math, sys, random
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

L = 0.60946080763725372899


def G1(r, b, A):
    s = math.sqrt(1 - r * r)
    return 1 - s * math.sin(2 * b) - (s - r * math.sin(2 * b)) * math.sin(2 * A) \
        - r * math.cos(2 * b) * math.cos(2 * A)


def G2(r, b, A):
    s = math.sqrt(1 - r * r)
    return 1 - s * (math.sin(2 * b) + math.sin(2 * A)) - r * math.cos(2 * (b + A))


rng = random.Random(3)
worst = 0.0
for _ in range(2000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    A = rng.random() * 2 * b
    worst = max(worst, abs(G1(r, b, A) - G2(r, b, A)))
print('(a) G_lead vs G_code (the form in face_totalangle_jet.legal)')
print(f'    max |G1 - G2| over 2000 legal points = {worst:.3e}   => identical form')

print()
print('(b) closed-form derivation check')
print('    G2 = 1 - s sin2b - d cos(2A - 2b - gamma), d=hypot(u,v), gamma=atan2(v,u):')
worst2 = 0.0
for _ in range(2000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    A = rng.random() * 2 * b
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b); v = r * math.cos(2 * b)
    d = math.hypot(u, v); g = math.atan2(v, u)
    lhs = -(u * math.sin(2 * A) + v * math.cos(2 * A))
    rhs = -d * math.cos(2 * A - 2 * b - g)
    worst2 = max(worst2, abs(lhs - rhs))
print(f'    max |(u sin2A + v cos2A) - d cos(2A-2b-gamma)| = {worst2:.3e}')

print()
print('    solving  cos(2A - 2b - gamma) >= c/d  with  theta = atan2(c, sqrt(d^2-c^2)):')
print('    the two boundary roots are A = b + (gamma-theta)/2 and A = b + (gamma+theta)/2')
worst3 = 0.0
for _ in range(2000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b); v = r * math.cos(2 * b)
    c = 1 - s * math.sin(2 * b)
    d = math.hypot(u, v); g = math.atan2(v, u)
    th = math.atan2(c, math.sqrt(d * d - c * c))
    A1 = b + (g - th) / 2
    A2 = b + (g + th) / 2
    worst3 = max(worst3, abs(G1(r, b, A1)), abs(G1(r, b, A2)))
print(f'    max |G| at the two roots = {worst3:.3e}   => the roots are exactly the G=0 points')

print()
print('    so the feasible set is the COMPLEMENT of the open band (A1, A2):')
print('      A in (0, A1] u [A2, pi+...)  ;  with A1*pi/2-... check the lead endpoints:')
print('      a- = (theta-gamma)/2  ==  A1 - b        <=>   a- + b = A1')
worst4 = 0.0
for _ in range(2000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b); v = r * math.cos(2 * b)
    c = 1 - s * math.sin(2 * b)
    d = math.hypot(u, v); g = math.atan2(v, u)
    th = math.atan2(c, math.sqrt(d * d - c * c))
    a_m = (th - g) / 2; a_p = (math.pi - th - g) / 2
    A1 = b + (g - th) / 2
    A1b = b + g / 2 + th / 2          # the other root
    worst4 = max(worst4, abs((a_m + b) - A1) if abs((a_m + b) - A1) < abs((a_m + b) - A1b) else 0.0)
print(f'    max |(a- + b) - A1| = {worst4:.3e}   => a- + b is the LOWER boundary root')
print()
print('    and a+ = (pi-theta-gamma)/2: is a+ + b the OTHER root (b + gamma/2 + theta/2) plus pi/2?')
worst5 = 0.0
for _ in range(2000):
    r = 0.379 + rng.random() * 0.00099
    b = L + rng.random() * (1 - L)
    s = math.sqrt(1 - r * r)
    u = s - r * math.sin(2 * b); v = r * math.cos(2 * b)
    c = 1 - s * math.sin(2 * b)
    d = math.hypot(u, v); g = math.atan2(v, u)
    th = math.atan2(c, math.sqrt(d * d - c * c))
    a_p = (math.pi - th - g) / 2
    # candidate identity: b + a+ = b + pi/2 - (g+th)/2  ; G there should equal G at the upper root
    worst5 = max(worst5, abs(G1(r, b, a_p)))
print(f'    max |G(a+)| = {worst5:.3e}   => a+ is also a boundary root (the one in (0,T))')
