"""Exclude a three-step exterior shortcut in the fourteen-arc branch."""

from fractions import Fraction as Q
from functools import lru_cache

from rational_trig import cos_lower, pi_bounds, sin_lower, sqrt_bounds
from verify_fan import asin_upper, fan_line, require


RADIUS = Q(".234701")
ARC_CAP = Q(".473822")
OUTER_NORM = Q(".7858")


@lru_cache(maxsize=1)
def window_deficits():
    """Upper bounds on the total angular deficit of any m exterior arcs."""
    table = (
        (".10858", "-.14245", "0", "6.98565", "-33.04423"),
        (".32760", ".12852", "-1.82531", "8.91928", "-41.30893"),
        (".55273", ".45228", "-3.67734", "11.49771", "-52.28233"),
        (".78161", ".73871", "-5.18382", "15.53197", "-69.39713"),
        ("1.01326", "1.00147", "-6.50294", "23.36557", "-102.55036"),
        ("1.24719", "1.25089", "-7.71749", "47.53015", "-204.64290"),
    )
    pi0, _ = pi_bounds()
    r, lam = RADIUS, Q(".256")
    require(sin_lower(ARC_CAP / 2) > r, "Invalid exterior angle cap")
    result = {}
    for m, row in enumerate(table, start=1):
        half, a, b, c, d = map(Q, row)
        require(52 * lam + d < 0 and b > d, "Invalid window bound signs")
        _, upper_c = fan_line(r, lam, a, b)
        fan_line(r, lam, c, d)
        area = r*r * (
            (52*lam + d) * pi0 + 150*upper_c + m*a + (14-m)*c + (b-d)*half
        )
        require(area < pi0, "The angular window was not excluded")
        result[m] = m * ARC_CAP - 2 * half
    alpha = Q(table[0][0])
    _, root = sqrt_bounds(r*r - sin_lower(alpha)**2)
    require(cos_lower(alpha) - root > OUTER_NORM, "The minimum exterior norm is not verified")
    return result


def verify():
    r = RADIUS
    lam = Q(".258")
    block_sum = Q(".7811592")
    small_intercept, small_slope = Q(".74120"), Q("-5.1956")
    large_intercept, large_slope = Q("16.01650"), Q("-71.45558")
    pi0, _ = pi_bounds()
    require(4 * asin_upper(r) < pi0 / 2, "The four-arc sine is not monotone")
    require(sin_lower(block_sum) > 3 * r, "Unverified four-arc half-angle bound")
    require(52 * lam + large_slope < 0 and small_slope > large_slope,
            "Invalid signs for the area substitution")
    small_boxes, c = fan_line(r, lam, small_intercept, small_slope)
    large_boxes, _ = fan_line(r, lam, large_intercept, large_slope)
    area = r**2 * (
        (52 * lam + large_slope) * pi0 + 150 * c
        + 4 * small_intercept + 10 * large_intercept
        + (small_slope - large_slope) * block_sum
    )
    require(area < pi0, "The four-arc shortcut was not excluded")
    print(f"PASS b=14, shared interior neighbor across three steps: "
          f"area <= {float(area):.12f}, boxes={[small_boxes, large_boxes]}")
    limits = window_deficits()
    print("PASS b=14, angular deficit upper bounds",
          {m: float(d) for m, d in limits.items()})
    print(f"PASS b=14, each exterior norm exceeds {float(OUTER_NORM)}")


if __name__ == "__main__":
    verify()
