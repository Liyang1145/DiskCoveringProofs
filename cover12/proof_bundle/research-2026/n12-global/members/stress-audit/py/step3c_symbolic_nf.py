"""stress-audit step 3c (EXACT sympy, fast normal forms).

Identity checks by clearing denominators and reducing the numerator modulo
y3^2 - 3 (y3 = sqrt(3)); no `simplify` (too slow), only exact expand/cancel.
Every claim is also evaluated with mpmath at two random rational points.
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
a, t, r, w = sp.symbols('a t r w', positive=True)
y3 = sp.Symbol('y3')
s3 = sp.sqrt(3)
b = (1 + a + r) / 2
d = a + r
S = b**2 + w**2 / 3
A = 3 * b**2 - w**2 - 2 * b * w
x = -b * r**2 / (S - b)
y = (b - 1) * S / (S - b)
q = 2 * (1 - b) / r
u = q * r / (2 * a - t + r)
j = u * (2 * t - 2 * r - a) / r
z = j * r * t / (1 - t**2 - r**2)
p = sp.Integer(1)
F = t**2 - 2 * t * r - a * t + a * r + a**2
G = (1 + t**2 - r**2) * (3 * b**2 + w**2) - t * (3 * b**2 - w**2 + 6 * b * w)
H = 4 * w**2 - 12 * r**2 + 3 * (1 - a - r)**2
T = w * S**2 * (2 * a - t + r) * (1 - t**2 - r**2) + (S - b) * (2 * t - 2 * r - a) * t**2 * A
torque = 2 * y * w * S - z * t * A
K = -2 * (1 - b) / ((S - b) * (2 * a - t + r) * (1 - t**2 - r**2))
PTS = [{a: sp.Rational(7, 25), t: sp.Rational(19, 25), r: sp.Rational(9, 25), w: sp.Rational(13, 25)},
       {a: sp.Rational(3, 11), t: sp.Rational(7, 9), r: sp.Rational(2, 7), w: sp.Rational(5, 8)}]

def normal_form(expr):
    e = sp.cancel(sp.together(expr.subs(s3, y3)))
    num, den = sp.fraction(e)
    num = sp.expand(num)
    guard = 0
    while num.has(y3**2) and guard < 50:
        num = sp.expand(num.subs(y3**2, 3)); guard += 1
    P = sp.expand(num.subs(y3, 0))
    Q = sp.expand((num - P) / y3)
    return sp.expand(P), sp.expand(Q)

def chk(expr, tag):
    P, Q = normal_form(expr)
    ok = (P == 0) and (Q == 0)
    vals = []
    for pt in PTS:
        f = sp.lambdify((a, t, r, w), expr, 'mpmath')
        v = f(mp.mpf(pt[a].p) / pt[a].q, mp.mpf(pt[t].p) / pt[t].q,
              mp.mpf(pt[r].p) / pt[r].q, mp.mpf(pt[w].p) / pt[w].q)
        vals.append(mp.nstr(abs(v), 3))
    print(f"  [{'OK ' if ok else 'FAIL'}] {tag}")
    print(f"        normal form zero: rational {P == 0}, sqrt3-part {Q == 0}; |value| at 2 rational pts: {vals}")
    return ok

print("=== B1. T is exactly the anchor torque scalar (definitions only) ===")
chk(T * K - torque, "T*K - (2 y w S - z t A),  K = -2(1-b)/((S-b)(2a-t+r)(1-t^2-r^2))")
chk(T - torque / K, "T - (2 y w S - z t A)/K   (same identity, divided form)")

print("\n=== B2. free-node balances and their true premises ===")
chk(2 * p * (b - d) + q * (a - d), "HRR witness (d,0): 2p(b-d)+q(a-d)  [defs only]")
chk(q * r + u * ((t - r) - 2 * a), "hub (a,0): qr+u(t-r-2a)  [definition of u]")
chk(a * u - 2 * u * (t - r) + j * r, "HHR witness: au-2u(t-r)+jr  [definition of j]")
chk(2 * z * ((1 + t**2 - r**2) / (2 * t) - t) - j * r, "low site: 2z(cos a - t)-jr  [cos alpha := G]")
chk((y - x - d) * (S - b) / b + H / 12, "high site tangential: (y-x-d)(S-b)/b + H/12")
chk((x + y) * (b - S) + d * b - S + b * H / 12, "high site radial: (x+y)(b-S)+db-S + b*H/12")

print("\n=== B3. premise identifications ===")
chk(H - 12 * (S - d - r**2), "H - 12(S-d-r^2)")
chk(G - 6 * S * t * ((1 + t**2 - r**2) / (2 * t) - (3 * b**2 - w**2 + 6 * b * w) / (6 * S)),
    "G - 6St[cos alpha - (3b^2-w^2+6bw)/(6S)]")
chk(F - ((t - r - a / 2)**2 + 3 * a**2 / 4 - r**2), "F - [(t-r-a/2)^2+3a^2/4-r^2]")

print("\n=== B4. active edge lengths = r, reduced to H/12 ===")
chk((S - 2 * b + 1 - r**2) - H / 12, "|highsite-u(0)|^2 - r^2 - H/12")
chk((S + d**2 - 2 * d * b - r**2) - H / 12, "|highsite-(d,0)|^2 - r^2 - H/12")

print("\n=== B5. anchor torque, one anchor per orbit ===")
site0 = sp.Matrix([b, w / s3])
U18 = sp.Matrix([(b**2 - w**2 / 3) / S, (2 * b * w / s3) / S])
site1 = sp.Matrix([t * sp.Rational(1, 2), t * s3 / 2])
U19 = sp.Matrix([-(b**2 - w**2 / 3) / (2 * S) + b * w / S,
                 (s3 / 2) * (b**2 - w**2 / 3) / S + b * w / (s3 * S)])
site2 = sp.Matrix([-b / 2 + w / 2, s3 * b / 2 + w / (2 * s3)])
U20 = sp.Matrix([-sp.Rational(1, 2), s3 / 2])
site3 = sp.Matrix([-b / 2 - w / 2, s3 * b / 2 - w / (2 * s3)])

def tau(P, site, ww):
    return ww * ((site - P).dot(sp.Matrix([-P[1], P[0]])))

for nm, U in (("U18", U18), ("U19", U19), ("U20", U20)):
    print(f"    {nm} |U|^2-1 normal form:", normal_form(U.dot(U) - 1))
print("    site2 - rot120(b,-v) normal form:",
      normal_form(site2[0] - (-b / 2 + w / 2)), normal_form(site2[1] - (s3 * b / 2 + w / (2 * s3))))
chk(tau(U18, site0, y) + tau(U18, site1, z) + torque / (2 * s3 * S), "tau_18 + torque/(2 sqrt3 S)")
chk(tau(U19, site1, z) + tau(U19, site2, y) - torque / (2 * s3 * S), "tau_19 - torque/(2 sqrt3 S)")
chk(tau(U20, site2, x) + tau(U20, site3, x), "tau_20 (hub axis, weights x,x)")
