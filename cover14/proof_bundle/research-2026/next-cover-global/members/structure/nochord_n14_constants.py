"""Exact rational verification of the constants in NO-CHORD-n14.md.

Everything is Fractions except the two elementary polygon facts (which enter as
the cited inscribed-polygon inequalities).  No inverse-trig value is ever
evaluated numerically; sines are bounded by the alternating Taylor lower bound
sin x >= x - x^3/6 + x^5/120 - x^7/5040 for x in [0,1].
"""
from fractions import Fraction as F

out = []


def say(s):
    out.append(s)
    print(s)


def sin_lb7(x):
    """lower bound for sin(x) using 4 alternating Taylor terms (valid x in [0,1])"""
    return x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040


# ---- 1. the n14 upper bound against 1/3 (exact rational)
U14 = F("0.33173203427623414")   # goal U (C411 value), not the longer n1314-table bound
say("U14            = %s" % U14)
say("U14 < 1/3      : %s   (1/3 - U14 = %s)" % (U14 < F(1, 3), F(1, 3) - U14))

# ---- 2. asin(2/3) < 73/100 and asin(1/3) < 17/50 via Taylor lower bounds
a, b = F(73, 100), F(17, 50)
sa, sb = sin_lb7(a), sin_lb7(b)
say("sin(73/100)LB  = %s > 2/3 ? %s" % (sa, sa > F(2, 3)))
say("sin(17/50) LB  = %s > 1/3 ? %s" % (sb, sb > F(1, 3)))
say("=> asin(2/3) < 73/100 and asin(1/3) < 17/50")
sum_ab = a + 7 * b
say("73/100+7*17/50 = %s = %.4f" % (sum_ab, float(sum_ab)))

# ---- 3. pi bounds from inscribed polygons (rational enclosures of radicals)
s6lo, s6hi = F(2449, 1000), F(2450, 1000)     # sqrt6
s2lo, s2hi = F(1414, 1000), F(1415, 1000)     # sqrt2
# sqrt6 - sqrt2 > 0.2449 - 0.1415/... careful: use lo of first minus hi of second
d = s6lo - s2hi
pi_12 = 12 * (d / 4)                        # pi > 12 sin(pi/12) = 3(sqrt6-sqrt2)
say("sqrt6 > %s, sqrt2 < %s" % (s6lo, s2hi))
say("pi > 3*(sqrt6-sqrt2) > %s = %.4f  (>3.06 ? %s)" % (pi_12, float(pi_12), pi_12 > F(306, 100)))
say("9*asin(1/3) < 9*17/50 = %s = %.4f  < pi (12-gon bound above) ? %s"
    % (9 * b, float(9 * b), 9 * b < pi_12))

# ---- 4. pi > 16*sin(pi/16) > 3.1184 > 3.11
# sin(pi/16) = sqrt(2-sqrt(2+sqrt2))/2 ; use sqrt2 < 14143/10000
s2u = F(14143, 10000)
inner = 2 + s2u
say("2+sqrt2 < %s = %.6f" % (inner, float(inner)))
# sqrt(inner) < 1.8480 because 1.8480^2 > inner
sq_18480 = F(18480, 10000) ** 2
say("1.8480^2 = %s > 2+sqrt2 ? %s" % (sq_18480, sq_18480 > inner))
rem = 2 - F(18480, 10000)
say("2-sqrt(2+sqrt2) > %s = %.6f" % (rem, float(rem)))
# sqrt(rem) > 0.3898 because 0.3898^2 < rem
sq_03898 = F(3898, 10000) ** 2
say("0.3898^2 = %s < 2-sqrt(2+sqrt2) ? %s" % (sq_03898, sq_03898 < rem))
sin_pi16_lo = F(3898, 10000) / 2
pi_16 = 16 * sin_pi16_lo
say("sin(pi/16) > %s = %.6f" % (sin_pi16_lo, float(sin_pi16_lo)))
say("pi > 16*sin(pi/16) > %s = %.4f  (> 3.11 ? %s)" % (pi_16, float(pi_16), pi_16 > F(311, 100)))

# ---- 5. the contradiction
say("")
say("chain: pi <= asin(2r)+7asin(r) < asin(2/3)+7asin(1/3) < 73/100+7*17/50")
say("     = %s = %.4f < %.4f < 16 sin(pi/16) < pi" % (sum_ab, float(sum_ab), float(pi_16)))
say("=> CONTRADICTION for every 0 < r < 1/3; non-adjacent active disks are disjoint.")

# ---- 6. margins (display only)
import math
for r, tag in ((1 / 3, "r=1/3"), (float(U14), "r=U14")):
    val = math.degrees(math.asin(2 * r) + 7 * math.asin(r))
    say("display-only margin at %-6s: asin(2r)+7asin(r) = %.4f deg, pi - that = %+.4f deg"
        % (tag, val, 180 - val))

open("nochord_n14_constants.out.txt", "w", encoding="utf8").write("\n".join(out) + "\n")
print("\n[written] nochord_n14_constants.out.txt")
