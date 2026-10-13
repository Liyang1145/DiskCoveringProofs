"""stress-audit step 3 (EXACT symbolic, sympy): all identities behind the
seven-orbit stress, the anchor torques, and T.

Rational arithmetic only (no floats anywhere).  Checks:
  A1  T, J membership in the ideal <F,G,H>                       (groebner/reduce)
  A2  free-node force balances, each reduced to its true premise
  A3  T = -2(1-b)/((S-b)(2a-t+r)(1-t^2-r^2)) * (2 y w S - z t A)
  A4  anchor torque residual T_i at one anchor of each of the three orbits,
      reduced symbolically to the same scalar (2 y w S - z t A)
  A5  radical identities sin(alpha)=A/(2 sqrt3 S), cos(alpha)=(1+t^2-r^2)/(2t)
  A6  exact rational cosine constants cos(dL)=T_d(1-2U^2), 4L<pi, 9L>2pi
"""
from pathlib import Path
import sympy as sp

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

def zero(expr, tag):
    """exact zero test after cancel/expand; radicals handled by splitting Q(sqrt3)."""
    e = sp.cancel(sp.expand(sp.together(expr)))
    num, den = sp.fraction(e)
    num = sp.expand(num)
    num = sp.collect(num, s3)
    parts = {}
    rest = num
    for powr in (sp.Integer(1), s3):
        c = sp.expand(rest).coeff(sp.sqrt(3)) if powr == s3 else None
        parts[powr] = c
    # generic: expand as P + Q*sqrt(3)
    P = sp.expand(num.subs(s3, 0))
    Q = sp.expand((num - P) / s3)
    ok = sp.simplify(P) == 0 and sp.simplify(Q) == 0
    print(f"  [{'OK ' if ok else 'FAIL'}] {tag}   (num rational part zero: {sp.simplify(P)==0}, sqrt3 part zero: {sp.simplify(Q)==0})")
    return ok

print("=== A1. ideal membership ===")
gb = sp.groebner([F, G, H], a, t, r, w, order='grevlex')
remT = sp.simplify(gb.reduce(T)[1])
remF = sp.simplify(gb.reduce(F)[1]); remG = sp.simplify(gb.reduce(G)[1]); remH = sp.simplify(gb.reduce(H)[1])
print("  reduce(F)= ", remF, "  reduce(G)= ", remG, "  reduce(H)= ", remH)
print("  T in <F,G,H>?  remainder =", remT, "->", remT == 0)
Jm = sp.Matrix([F, G, H]).jacobian([a, t, w])
J = sp.factor(Jm.det())
remJ = sp.simplify(gb.reduce(J)[1])
print("  J in <F,G,H>?  remainder =", remJ, "->", remJ == 0)

print("\n=== A2. free-node force balances ===")
# HRR witness at (d,0):  2p(b-d) + q(a-d) along u(0);  b-d = -(1-d)/2
zero(2 * p * (b - d) + q * (a - d), "HRR witness (d,0) radial")
# hub at (a,0):  q r + u((t-r) - 2a)
zero(q * r + u * ((t - r) - 2 * a), "hub (a,0) radial (== definition of u)")
# HHR witness at (t-r)u(pi/3):  a u - 2u(t-r) + j r
zero(a * u - 2 * u * (t - r) + j * r, "HHR witness radial (== definition of j)")
# low site: 2 z (cos(alpha) - t) - j r  with cos(alpha)=(1+t^2-r^2)/(2t)
zero(2 * z * ((1 + t**2 - r**2) / (2 * t) - t) - j * r, "low site radial (uses cos(alpha))")
# high site: tangential  y - x - d ;  radial (x+y)(cos(beta) - s) + d cos(beta) - s
# with cos(beta)=b/s: multiply by s  ->  (x+y)(b - S) + d b - S
zero(y - x - d, "high site tangential  (y - x - d)")
zero((x + y) * (b - S) + d * b - S, "high site radial *s  (== H at d=2b-1)")
print("  [note] H <-> S=d+r^2 :", sp.simplify(sp.expand(H) - sp.expand(sp.Rational(4) * (S - d - r**2) * 3 / 3 * 1)) is not None)
print("      exact: H - 4(S - d - r^2) =", sp.simplify(H - 4 * (S - d - r**2)))

print("\n=== A3. T vs torque scalar ===")
torque = 2 * y * w * S - z * t * A          # == 2 sqrt3 S (y v - z t sin alpha), v=w/sqrt3
K = -2 * (1 - b) / ((S - b) * (2 * a - t + r) * (1 - t**2 - r**2))
zero(T - K * torque, "T - K*(2 y w S - z t A)")

print("\n=== A4. anchor torques (one per orbit), unnormalised ===")
# anchor 18 at angle 2beta: neighbours site0=(b,v) [y] and site1=t*u(pi/3) [z]
# basis: U = u(2beta); tangent tau = u(2beta+pi/2);  cos2b=(b^2-w^2/3)/S, sin2b=2b(w/sqrt3)/S
site0 = (b, w / s3)                     # cartesian
U18 = (b**2 - w**2 / 3, 2 * b * w / s3) / S    # unit vector at 2beta  (cos2b, sin2b)
site1 = t * (sp.Rational(1, 2), s3 / 2)        # t*u(pi/3)
torque18 = sp.simplify(sp.expand(
    y * ((site0[0] - U18[0]) * (-U18[1]) + (site0[1] - U18[1]) * (U18[0]))
    + z * ((site1[0] - U18[0]) * (-U18[1]) + (site1[1] - U18[1]) * (U18[0]))))
print("  tau_18 (radical form) =", sp.nsimplify(sp.simplify(torque18)))
zero(torque18 - (-y * w / s3 * 1) + (z * t * A / (2 * s3 * S)), "tau_18 == -y v + z t sin(alpha)")
# anchor 19 at angle 2pi/3-2beta: neighbours site1 (z) and site2 = rot120 (b,-v) (y)
U19 = (sp.cos(2 * sp.pi / 3), sp.sin(2 * sp.pi / 3))     # placeholder replaced below
c19 = sp.Rational(-1, 2) * (b**2 - w**2 / 3) / S - (s3 / 2) * (2 * b * w / s3) / S
s19 = (s3 / 2) * (b**2 - w**2 / 3) / S + sp.Rational(-1, 2) * (2 * b * w / s3) / S
U19 = (c19, s19)                                        # exact unit vector at 2pi/3-2beta
site2 = (sp.Rational(-1, 2) * b - (s3 / 2) * (-w / s3), (s3 / 2) * b + sp.Rational(-1, 2) * (-w / s3))
torque19 = sp.simplify(sp.expand(
    z * ((site1[0] - U19[0]) * (-U19[1]) + (site1[1] - U19[1]) * (U19[0]))
    + y * ((site2[0] - U19[0]) * (-U19[1]) + (site2[1] - U19[1]) * (U19[0]))))
zero(torque19 - (z * t * A / (2 * s3 * S) - y * w / s3), "tau_19 == +z t sin(alpha) - y v")
# anchor 20 at angle 2pi/3 (hub axis): sites 2 and 3 both weight x -> reflection cancel
U20 = (sp.Rational(-1, 2), s3 / 2)
site3 = (sp.Rational(-1, 2) * b - (s3 / 2) * (w / s3), (s3 / 2) * b + sp.Rational(-1, 2) * (w / s3))
torque20 = sp.simplify(sp.expand(
    x * ((site2[0] - U20[0]) * (-U20[1]) + (site2[1] - U20[1]) * (U20[0]))
    + x * ((site3[0] - U20[0]) * (-U20[1]) + (site3[1] - U20[1]) * (U20[0]))))
zero(torque20, "tau_20 (hub axis, both weights x)")

print("\n=== A5. radical geometric identities ===")
beta_cos = b / sp.sqrt(S); beta_sin = (w / s3) / sp.sqrt(S)
al = sp.pi / 3 - 2 * sp.atan2(w / s3, b)     # not used algebraically; use cos/sin forms
zero(sp.sin(sp.pi / 3) * (b**2 - w**2 / 3) / S - sp.cos(sp.pi / 3) * (2 * b * w / s3) / S - A / (2 * s3 * S),
     "sin(pi/3-2beta) == A/(2 sqrt3 S)")
zero(sp.cos(sp.pi / 3) * (b**2 - w**2 / 3) / S + sp.sin(sp.pi / 3) * (2 * b * w / s3) / S
     - (3 * b**2 - w**2 + 6 * b * w) / (6 * S), "cos(pi/3-2beta) == (3b^2-w^2+6bw)/(6S)")
print("  G <-> cos(alpha)=(1+t^2-r^2)/(2t) : G -(6S)*((1+t^2-r^2)/(2t) - (3b^2-w^2+6bw)/(6S))*t =",
      sp.simplify(sp.expand(G - 6 * S * t * ((1 + t**2 - r**2) / (2 * t) - (3 * b**2 - w**2 + 6 * b * w) / (6 * S)))))
print("  F <-> (t-r-a/2)^2 + 3a^2/4 - r^2 =", sp.simplify(sp.expand(F - ((t - r - a / 2)**2 + 3 * a**2 / 4 - r**2))))

print("\n=== A6. exact rational cosine constants and domain guards ===")
U = sp.Rational('361102963744508672616920293904', 10**30)
c1 = 1 - 2 * U**2
cosd = {1: c1}
cosd[2] = sp.expand(2 * c1 * cosd[1] - 1)
cosd[3] = sp.expand(2 * c1 * cosd[2] - cosd[1])
cosd[4] = sp.expand(2 * c1 * cosd[3] - cosd[2])
for kk in (1, 2, 3, 4):
    val = sp.nsimplify(cosd[kk])
    print(f"  cos({kk}L) = T_{kk}(1-2U^2) = {sp.nstr(val, 30)}   (rational: {val.is_rational})")
# 4L < pi  <=>  U < sin(pi/8)  <=>  sqrt2 < 2-4U^2
rhs = 2 - 4 * U**2
print("  2-4U^2 =", sp.nstr(rhs, 30), " >0:", rhs > 0, " ; (2-4U^2)^2 - 2 =", sp.nstr(sp.expand(rhs**2 - 2), 30), ">0:", sp.expand(rhs**2 - 2) > 0)
print("  => sqrt2 < 2-4U^2 => U < sin(pi/8) => 4L < pi  [L=2 asin U]")
print("  9L > 2pi needs U > sin(pi/9):  sin(pi/9) < pi/9 < 22/63 =", sp.nstr(sp.Rational(22, 63), 20), "< U =", sp.nstr(U, 20), ":", sp.Rational(22, 63) < U)
