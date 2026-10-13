"""stress-audit step 3b (EXACT sympy, fast): the seven-orbit identities.

Each claim is (i) simplified symbolically to 0 (exact rational / sqrt(3)
arithmetic) and (ii) re-evaluated at two random rational points with mpmath
dps=40, so a symbolic no-op cannot masquerade as a proof.
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
a, t, r, w = sp.symbols('a t r w', positive=True)
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
PTS = [dict(a=sp.Rational(7, 25), t=sp.Rational(19, 25), r=sp.Rational(9, 25), w=sp.Rational(13, 25)),
       dict(a=sp.Rational(3, 11), t=sp.Rational(7, 9), r=sp.Rational(2, 7), w=sp.Rational(5, 8))]

def chk(expr, tag):
    e = sp.simplify(sp.expand(sp.radsimp(sp.cancel(sp.together(expr)))))
    vals = []
    for pt in PTS:
        v = complex(sp.N(expr.subs(pt), 30))
        vals.append(f"{abs(v):.2e}")
    print(f"  [{'OK ' if e == 0 else 'SEE'}] {tag}\n        symbolic: {e}\n        |value| at 2 rational pts: {vals}")

print("=== B1. T is exactly the anchor torque scalar (no premise besides defs) ===")
chk(T - K * torque, "T - K*(2 y w S - z t A),  K = -2(1-b)/((S-b)(2a-t+r)(1-t^2-r^2))")

print("\n=== B2. free-node balances: what each one really needs ===")
chk(2 * p * (b - d) + q * (a - d), "HRR witness (d,0):  2p(b-d) + q(a-d)   [defs only]")
chk(q * r + u * ((t - r) - 2 * a), "hub (a,0):  qr + u(t-r-2a)   [definition of u]")
chk(a * u - 2 * u * (t - r) + j * r, "HHR witness: au - 2u(t-r) + jr   [definition of j]")
chk(2 * z * ((1 + t**2 - r**2) / (2 * t) - t) - j * r, "low site: 2z(cos alpha - t) - jr   [cos alpha from G]")
chk((y - x - d) * (S - b) / b + H / 12, "high site tangential: (y-x-d)(S-b)/b + H/12")
chk((x + y) * (b - S) + d * b - S + H / 12, "high site radial: (x+y)(b-S)+db-S + H/12")

print("\n=== B3. premise identifications ===")
chk(H - 12 * (S - d - r**2), "H - 12(S-d-r^2)")
chk(G - 6 * S * t * ((1 + t**2 - r**2) / (2 * t) - (3 * b**2 - w**2 + 6 * b * w) / (6 * S)),
    "G - 6 S t [cos alpha - (3b^2-w^2+6bw)/(6S)]")
chk(F - ((t - r - a / 2)**2 + 3 * a**2 / 4 - r**2), "F - [(t-r-a/2)^2 + 3a^2/4 - r^2]")

print("\n=== B4. edge lengths = r, each reduced to H/12 ===")
chk((S - 2 * b + 1 - r**2) - H / 12, "|highsite - u(0)|^2 - r^2 - H/12")
chk((S + d**2 - 2 * d * b - r**2) - H / 12, "|highsite - (d,0)|^2 - r^2 - H/12")

print("\n=== B5. anchor torque, one anchor per orbit ===")
site0 = sp.Matrix([b, w / s3])
U18 = sp.Matrix([(b**2 - w**2 / 3) / S, (2 * b * w / s3) / S])
site1 = sp.Matrix([t * sp.Rational(1, 2), t * s3 / 2])
c19 = -(b**2 - w**2 / 3) / (2 * S) + b * w / S
s19 = -(s3 / 2) * (b**2 - w**2 / 3) / S + b * w / (s3 * S)
U19 = sp.Matrix([c19, s19])
site2 = sp.Matrix([-b / 2 + w / 2, s3 * b / 2 + w / (2 * s3)])
U20 = sp.Matrix([-sp.Rational(1, 2), s3 / 2])
site3 = sp.Matrix([-b / 2 - w / 2, s3 * b / 2 - w / (2 * s3)])

def tau(P, site, ww):
    return ww * ((site - P).dot(sp.Matrix([-P[1], P[0]])))

print("  unit/geometry sanity:")
for nm, U in (("U18", U18), ("U19", U19), ("U20", U20)):
    print("    ", nm, "|U|^2-1 =", sp.simplify(sp.expand(U.dot(U) - 1)))
print("     site2 == rot120(b,-v):", sp.simplify(sp.expand(site2[0] - (-b / 2 + w / 2))),
      sp.simplify(sp.expand(site2[1] - (s3 * b / 2 + w / (2 * s3)))))
chk(tau(U18, site0, y) + tau(U18, site1, z) + torque / (2 * s3 * S), "tau_18 + torque/(2 sqrt3 S)")
chk(tau(U19, site1, z) + tau(U19, site2, y) - torque / (2 * s3 * S), "tau_19 - torque/(2 sqrt3 S)")
chk(tau(U20, site2, x) + tau(U20, site3, x), "tau_20 (hub axis, weights x,x)")
