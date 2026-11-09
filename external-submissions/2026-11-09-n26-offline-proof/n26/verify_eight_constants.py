"""Check rational numerical inequalities in the eight-disk and k-count proofs."""

from fractions import Fraction as Q

from rational_trig import cos_lower, cos_upper, pi_bounds, sin_lower, sin_upper


def check(condition, name):
    if not condition:
        raise ValueError(name)


def main():
    pi0, pi1 = pi_bounds()
    r0, r1 = Q(".445"), Q(".4451")
    a1 = Q(".4613")
    x = Q(".365")
    check(sin_lower(a1) > r1, "upper bound for asin(r)")
    check(6 * a1 < pi0, "six peripheral disks are insufficient")
    check(0 < pi0 - 6 * a1 < Q(1), "range of the minimum assigned half-angle")
    check(sin_lower(pi0 - 6 * a1) > x, "lower bound for sin(minimum half-angle)")
    check(Q(".254") ** 2 < r0 * r0 - x * x < r1 * r1 - x * x < Q(".255") ** 2,
          "square root bounds at x")
    check(1 - x * x > Q(".93") ** 2 and Q(".93") - Q(".255") > Q(2, 3),
          "lower bound on peripheral center norm")
    check(0 < pi0 - 5 * a1 < pi1 / 2 and sin_lower(pi0 - 5 * a1) > Q(".73"),
          "lower bound on sine for non-neighbors")
    check(2 * Q(2, 3) * Q(".73") > 2 * r1, "non-neighbor separation")

    g0, g1 = pi0 / 7, pi1 / 7
    check(sin_lower(g0) > Q(".43") and sin_upper(g1) < r0, "sin(pi/7) bounds")
    c0, c1 = cos_lower(g1), cos_upper(g0)
    check(r0 * (4 * c1 * c1 - 1) < 1 < r1 * (4 * c0 * c0 - 1),
          "eight-disk candidate inside radius bracket")

    def v2(r):
        return 4 * r * r - (1 - r) ** 2

    check(Q(".695") ** 2 < v2(r0) and v2(r1) < Q(".697") ** 2, "bounds for V")
    check((1 - r0) / Q(".695") < Q(".81"), "bound for H")
    check(Q(".19") < 1 - r1 / (1 - r1), "lower bound for c")
    check(2 * (1 - r1 * r1) > Q("1.6"), "penalty from two opposite directions")
    check((Q("1.6") + (7 - Q("1.6")) * Q(".19")) / (2 * Q(".697")) > Q("1.8"),
          "bound for B")
    check(7 * (Q(".81") / Q(".43")) ** 2 < 4 * 4 * Q("1.8"),
          "quadratic perimeter inequality")

    check(r1 * r1 < Q(2, 9), "power-series derivative monotonicity")
    check(r1 * r1 - 2 * x * x < 0, "negative middle term")
    fpp = (
        -8 * x
        + 2 * x * (r0 * r0 - 2 * x * x) / Q(".254")
        + 2 * x * (3 * r0 * r0 - 2 * x * x) * (1 - x * x) / Q(".255") ** 3
    )
    check(fpp - 2 * (1 - r0) * (r1 - x) > 8, "uniform lower bound for f''")

    trial = Q(".235")
    check(trial < sin_lower(pi0 / 13), "at least fourteen exterior disks")
    check(2 * trial < sin_lower(pi0 / 6), "at least seven half-circle disks")
    check(2 * trial < Q(1, 2) < 1 - 2 * trial, "half-radius circle separated")
    check(trial / (1 - 2 * trial) < r0, "k=18 implies impossible eight-disk covering")
    print("PASS: all exact inequalities in the eight-disk proof and k=14..17 reduction")


if __name__ == "__main__":
    main()
