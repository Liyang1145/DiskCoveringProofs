"""Exact interval checks for the Voronoi fan area inequalities."""

from fractions import Fraction as Q
from math import acos, comb

from rational_trig import cos_lower, cos_upper, pi_bounds, sin_lower, sin_upper, sqrt_bounds


HALF_PI_HI = Q("1.570796326794897")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def asin_upper(x):
    """Positive Maclaurin series and a geometric bound on the tail."""
    return sum(
        (Q(comb(2 * j, j), 4**j * (2 * j + 1)) * x ** (2 * j + 1)
         for j in range(8)),
        Q(0),
    ) + x**17 / (1 - x * x)


def c_bounds(lam):
    # An approximate acos supplies endpoints that are checked by exact cosines.
    scale = 10**12
    j = int(scale * acos(float(2 * lam)))
    lo, hi = Q(j - 1, scale), Q(j + 2, scale)
    require(0 < lo < hi < HALF_PI_HI, "Invalid acos bracket")
    require(cos_lower(lo) >= 2 * lam >= cos_upper(hi), "Unverified acos bracket")
    slo, shi = sqrt_bounds(1 - 4 * lam * lam)
    return slo / 2 - lam * hi, shi / 2 - lam * lo


def cap_upper(alpha):
    return alpha - sin_lower(2 * alpha) / 2


def arc_terms(r, hi, pi0):
    z = min(Q(1), sin_upper(hi)) if hi < pi0 / 2 else Q(1)
    # Keep the rational input to the higher powers small, rounding upward.
    denom = 10**13
    z = r * z * denom
    z = Q(-((-z.numerator) // z.denominator), denom)
    alpha = asin_upper(z)
    clo, _ = sqrt_bounds(1 - z * z)
    return alpha, alpha - z * clo


def fan_line(r, lam, intercept, slope, theta_limit=HALF_PI_HI, offset=Q(0)):
    """Verify H(alpha) <= intercept + slope*alpha on 0 <= alpha <= asin(r)."""
    pi0, pi1 = pi_bounds()
    require(HALF_PI_HI >= pi1 / 2, "Invalid pi/2 bracket")
    clo, chi = c_bounds(lam)
    passed = 0
    pending = [(Q(0), theta_limit, 0)]
    while pending:
        lo, hi, depth = pending.pop()
        alpha, cap = arc_terms(r, hi, pi0)
        g = chi
        if lo > pi1 / 6:
            mid = (lo + hi) / 2
            # 0.5 sin(2 theta) is 1-Lipschitz.
            g = min(g, (sin_upper(2 * mid) + hi - lo) / 2 - 2 * lam * lo)
        line_arg = alpha
        if slope > 0:
            z = max(Q(0), r * sin_lower(lo))
            line_arg = z + z**3 / 6 + 3 * z**5 / 40
        if g + cap / (r * r) - 2 * clo - slope * line_arg + offset <= intercept:
            passed += 1
            continue
        if depth >= 25:
            raise ValueError(f"Fan line not verified near theta={float(lo):.12f}")
        mid = (lo + hi) / 2
        pending.extend(((lo, mid, depth + 1), (mid, hi, depth + 1)))
    return passed, chi


def main():
    r = Q(".2265")
    pi0, pi1 = pi_bounds()

    lam, a, b = Q(".198"), Q(0), Q("-1.332")
    boxes, c = fan_line(r, lam, a, b)
    alpha = asin_upper(r)
    truncated = r * r * (25 * 2 * pi1 * lam + 147 * c + b * (pi0 - alpha)) + cap_upper(alpha)
    require(truncated < pi0, "Truncated-disk area bound does not exclude a repeated arc")
    print(f"PASS repeated arcs at r={float(r)}: area+cap <= {float(truncated):.12f}, boxes={boxes}")

    lam, a, b = Q(".225"), Q(".94350"), Q("-6.475")
    boxes, c = fan_line(r, lam, a, b)
    full = r * r * (26 * 2 * pi1 * lam + 150 * c + 16 * a + b * pi0)
    require(full < pi0, "Full disk with at most 16 boundary arcs is not excluded")
    print(f"PASS b<=16 at r={float(r)}: area <= {float(full):.12f}, boxes={boxes}")

    r = Q(".23185")
    lam, a, b = Q(".251"), Q("3.52605"), Q("-18.28756")
    boxes, c = fan_line(r, lam, a, b)
    full = r * r * (26 * 2 * pi1 * lam + 150 * c + 14 * a + b * pi0)
    require(full < pi0, "Full disk with at most 14 boundary arcs is not excluded")
    print(f"PASS b<=14 at r={float(r)}: area <= {float(full):.12f}, boxes={boxes}")

    r = Q(".234701")
    lam, a, b = Q(".247"), Q("2.857"), Q("-15.07861")
    boxes, c = fan_line(r, lam, a, b)
    full = r * r * (25 * 2 * pi1 * lam + 144 * c + 14 * a + b * pi0)
    require(full < pi0, "25 disks with 14 boundary arcs are not excluded")
    print(f"PASS 25 disks, b<=14 at r={float(r)}: area <= {float(full):.12f}, boxes={boxes}")

    r, a = Q(".235"), Q(".23725")
    require(sin_lower(a) > r, "Exterior half-angle bound")
    require((1-r) * sin_lower(pi0 - 11*a - Q(".215")) > r, "k=14 separation, short caps")
    angle = Q(".43") - a
    _, h = sqrt_bounds(r*r - sin_lower(angle)**2)
    require(cos_lower(angle) - h > Q(".84"), "k=14 exterior norm")
    require(Q(".84") * sin_lower(pi0 - 12*a) > r, "k=14 separation, long caps")
    print("PASS: k=14 nonconsecutive exterior disks are disjoint at r<=0.235")


if __name__ == "__main__":
    main()
