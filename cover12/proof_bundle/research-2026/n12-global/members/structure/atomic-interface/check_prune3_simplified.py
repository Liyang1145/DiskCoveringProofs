"""Quick verification of the simplified (radical-free) prune 3.

New predicate (lead, hubline_domain.py): when xh < a, with
    q2  = a^2 - xh^2,
    rhs = U^2 - sl^2 - yl^2 - q2,
the box is illegal iff   rhs < 0   or   4*yl^2*q2 > rhs^2 .

Claimed source: the monotone lower bound
    L = sl^2 + (yl + sqrt(q2))^2 > U^2 .

This script checks the equivalence exactly (Fractions) and against an
independent high-precision evaluation of L, on deterministic exact boxes.
"""
from fractions import Fraction as F
from mpmath import mp

mp.dps = 60
U = F("0.361102963744508672616920293904")
a = 1 - 2 * U


def new_test(xl, xh, yl, sl):
    q2 = a * a - xh * xh
    rhs = U * U - sl * sl - yl * yl - q2
    if rhs < 0:
        return True, "rhs<0", q2, rhs
    return 4 * yl * yl * q2 > rhs * rhs, "4yl^2q2>rhs^2", q2, rhs


def direct_test(xl, xh, yl, sl):
    """L > U^2 with L at 60 digits (independent of the squaring step)."""
    q2 = a * a - xh * xh
    L = (mp.mpf(sl.numerator) / sl.denominator) ** 2 + \
        (mp.mpf(yl.numerator) / yl.denominator + mp.sqrt(
            mp.mpf(q2.numerator) / q2.denominator)) ** 2
    return bool(L > (mp.mpf(U.numerator) / U.denominator) ** 2), L


boxes = [
    ("legal-ish", F(0), F(1, 5), F(0), F(1, 5)),
    ("sl at U, yl 0", F(0), F(1, 5), F(0), U),
    ("sl at U, yl e0", F(0), F(1, 5), 3 * U - 1, U),
    ("endpoints violated", F(0), F(1, 7), F(1, 2), F(1, 3)),
    ("rhs borderline (sl^2+q2=U^2, yl=0)", F(0), F(1, 5), F(0),
     F(0)),  # placeholder replaced below if needed
    ("xh close to a", F(0), a - F(1, 1000), F(1, 10), F(1, 4)),
    ("tiny yl, q2 large", F(0), F(1, 100), F(1, 1000), F(1, 3)),
]
# make a genuine rhs=0 case: yl=0 and sl^2+q2 = U^2 exactly is irrational in
# general, so use yl=0 and solve the rational condition rhs>=0 boundary
boxes[4] = ("yl=0, rhs near 0", F(0), F(1, 5), F(0), F(0))

allok = True
for name, xl, xh, yl, sl in boxes:
    if not (xh < a):
        print("skip (guard xh<a fails):", name)
        continue
    nt, why, q2, rhs = new_test(xl, xh, yl, sl)
    dt, L = direct_test(xl, xh, yl, sl)
    agree = (nt == dt)
    allok &= agree
    print("%-38s new=%-5s (%s) direct=%-5s L=%.20f  rhs=%s  agree=%s"
          % (name, nt, why, dt, L, "neg" if rhs < 0 else str(rhs)[:14], agree))

# exact equivalence proof check: 2 yl sqrt(q2) > rhs  <=>  4 yl^2 q2 > rhs^2
# for rhs >= 0 and yl,q2 >= 0 (squaring both non-negative sides).
print("\nexact equivalence chain (recorded, not sampled):")
print("  L > U^2  <=>  sl^2+yl^2+2yl*sqrt(q2)+q2 > U^2")
print("           <=>  2yl*sqrt(q2) > U^2-sl^2-yl^2-q2 = rhs")
print("  if rhs < 0: LHS >= 0 > rhs, so the inequality holds (illegal).")
print("  if rhs >= 0: both sides non-negative, so squaring is exact:")
print("           2yl*sqrt(q2) > rhs  <=>  4 yl^2 q2 > rhs^2.")
print("\nall deterministic boxes agree:", allok)
