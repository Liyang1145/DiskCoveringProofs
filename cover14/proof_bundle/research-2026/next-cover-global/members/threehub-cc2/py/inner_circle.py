# -*- coding: utf-8 -*-
"""
inner_circle.py -- members/threehub-cc2

Exact treatment of the INNER-CIRCLE capacity test for the middle annulus (part of
L5 in MEMBER-NOTES.md).

Test.  Points p on the inner circle |x| = s = 2r; centres c with |c| = rho >= rho0 =
1-r; the arc of that circle covered by the disk B(c,r) has half-aperture alpha with
        cos alpha = (rho^2 + s^2 - r^2) / (2 rho s).                        (1)
For 11 equally spaced centres the circle is covered iff  cos(pi/11) <= (1).
For a general 11-tuple the largest angular gap is >= 2pi/11, so substituting
alpha = pi/11 is the necessary test (not sufficient).

Monotonicity.  The RHS of (1) is >= 1 for rho <= rho1 = (s^2-r^2)/s (degenerate, full
circle) and DECREASING in rho for rho >= rho1; hence the necessary test is weakest at
the largest admissible rho.  Two upper bounds are used: the inactivity window
rho <= 1+r, where (1) becomes 1 for s = 2r (trivial), and rho = 1-rho0 = r, which is
weaker still.  At the *smallest* admissible rho = rho0 = 1-r the test is strongest:
        cos(pi/11) <= (rho0^2 + s^2 - r^2)/(2 rho0 s),  s = 2r, rho0 = 1-r
                <=>  cos(pi/11) <= (1-r)^2 + 3r^2)/(2r(1-r))   [dividing by s=2r]
                <=>  2r(1-r) cos(pi/11) <= (1-r)^2 + 3r^2.
Subtracting RHS from LHS:
        Q(r) := (cos(pi/11)+1)(2r^2 - 2r) + 1,  a convex-upward quadratic in r with
        minimum at r = 1/2,
and numerically  min_r Q(r) = 1 - (cos(pi/11)+1)/2 = (1-cos(pi/11))/2 > 0.
THEREFORE Q(r) > 0 for all real r: the inner-circle test holds for EVERY r, so the
inner circle alone never excludes the k=11 branch.  (This corrects an earlier
misreading in my own log where the roles of rho and s were swapped.)
"""
import math

C11 = math.cos(math.pi / 11)
print("cos(pi/11) = %.17f" % C11)
print("min_r Q(r) = (1-cos(pi/11))/2 = %.17f > 0" % ((1 - C11) / 2))
print("=> inner-circle test: HOLDS FOR ALL r  (no exclusion from the inner circle alone)")
print()
U = 0.33173203427623414
print("at r = U: 2r(1-r)cos(pi/11) = %.12f ; (1-r)^2+3r^2 = %.12f ; Q = %+.6e"
      % (2 * U * (1 - U) * C11, (1 - U) ** 2 + 3 * U * U,
         2 * U * (1 - U) * C11 - ((1 - U) ** 2 + 3 * U * U)))
print()
print("=== theoretical inner-boundary lower bound R_in(r) = sqrt(rho0^2+s^2-2 rho0 s cos(pi/11))")
print("    (necessary: R(r) >= R_in(r)) vs the numeric R(r) from py/rstar.py")
num = {0.24: 0.338881, 0.26: 0.315640, 0.28: 0.322905, 0.30: 0.338436,
       0.315: 0.352623, 0.3317: 0.367695, 0.335: 0.362513, 0.34: 0.369482}
for r, v in num.items():
    rho0, s = 1 - r, 2 * r
    rin = math.sqrt(rho0 ** 2 + s ** 2 - 2 * rho0 * s * C11)
    print(f"  r={r:.4f}  R_in={rin:.6f}  numeric R={v:.6f}  ratio={v/rin:.4f}  R-r={v-r:+.6f}")
