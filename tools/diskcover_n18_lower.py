# SPDX-License-Identifier: MIT
"""Fresh exact two-circle exclusion for eighteen equal disks at r=0.26590."""
import json
from fractions import Fraction as F

SCALE = 100_000
R = 26_590
T = 58_670
W = 78
U = 47_037  # check the inner-owner angular bound before using it


def _require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def _sin_lower(x):
    return x - x**3/6 + x**5/120 - x**7/5040


def _pi_lower():
    # Machin: the even-length alternating sum is a lower bound.
    positive = sum((-1)**i * F(1, (2*i+1)*5**(2*i+1)) for i in range(6))
    return 16*positive - F(4, 239)


def check_n18_lower():
    """Prove r_D(18)>0.26590 by exact rational angle bounds."""
    s = SCALE
    r, t = F(R, s), F(T, s)
    pi = _pi_lower()
    _require(pi > F("3.14159"), "Machin lower bound")
    _require(0 < r < t < 1 and t**2 + (1-r)**2 - r**2 > 0,
             "circle and radial ratio domain")
    _require(pi > 11*F(".28") and _sin_lower(F(".28")) > r,
             "at most eleven boundary disks not excluded")
    _require(pi > 5*F(".62") and (1-2*r)*_sin_lower(F(".62")) > r,
             "at least thirteen boundary disks not excluded")
    _require(_sin_lower(F(U, s)) > r/t, "inner angular cap is not an upper bound")

    # Truncation through x^8 upper-bounds cos(x) for 0 <= x <= 3/5.
    den = 40320*s**8
    table = [den - 20160*a*a*s**6 + 1680*a**4*s**4 - 56*a**6*s**2 + a**8
             for a in range(3*s//5 + 1)]
    _require(all(a > b for a, b in zip(table, table[1:])), "cos table unsorted")

    def angle_upper(n, d):
        if n >= d:
            return 0
        lo, hi = 0, len(table)-1
        _require(n*den >= table[hi]*d, "angle exceeds tabulated range")
        while hi-lo > 1:
            m = (hi+lo)//2
            if n*den >= table[m]*d:
                hi = m
            else:
                lo = m
        return hi

    worst = 0
    for j in range(s-R, s+R):
        outer = angle_upper(s*s+j*j-R*R, 2*s*(j+1))
        inner = angle_upper(T*T+j*j-R*R, 2*T*(j+1))
        worst = max(worst, W*outer + (100-W)*inner)
    total = F(12*worst + 6*(100-W)*U, 100*s)
    _require(total < pi, "weighted angle exclusion did not close")
    return {
        "n": 18,
        "status": "certified_strict_lower_only",
        "lower_exact": "0.26590",
        "radial_bins": 2*R,
        "inner_circle_radius": str(t),
        "outer_weight": str(F(W, 100)),
        "max_weighted_sum_upper": str(total),
        "pi_lower": str(pi),
    }


if __name__ == "__main__":
    print(json.dumps(check_n18_lower(), indent=2))
