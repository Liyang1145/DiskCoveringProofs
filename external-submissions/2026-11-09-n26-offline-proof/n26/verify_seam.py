"""Exact constants for the seam-coupled fan bound and no-repeat reduction."""

from fractions import Fraction as Q
from functools import lru_cache
from math import acos

from rational_trig import cos_lower, pi_bounds, sin_lower, sqrt_bounds
from verify_fan import c_bounds, fan_line, require


NO_REPEAT_RADIUS = {25: Q(".235"), 26: Q(".231")}


def acos_lower(x):
    scale = 10**12
    j = int(acos(float(x)) * scale)
    while j > 0:
        a = Q(j, scale)
        if cos_lower(a) >= x:
            return a
        j -= 1
    return Q(0)


@lru_cache(maxsize=None)
def seam_upper(lam, tau, copies):
    require(0 < tau < lam < Q(1, 2) and copies in (1, 2), "Invalid seam parameters")
    pi0, _ = pi_bounds()
    _, c = c_bounds(lam - tau / copies)
    full = copies * c - pi0 * tau
    hlo, hhi = sqrt_bounds(2 * lam)
    _, side_radius = sqrt_bounds(1 - 2 * lam)
    side_slope = (side_radius - hlo * acos_lower(hhi)) / 2
    side = hhi * max(Q(0), copies * side_slope - 2 * tau)
    value = max(Q(0), full, side) * 10**12
    return Q(-((-value.numerator) // value.denominator), 10**12)


@lru_cache(maxsize=None)
def no_repeat_bound(disks=26):
    n = disks - 1
    r, lam, tau = NO_REPEAT_RADIUS[disks], Q(".205"), Q(".118")
    slope = Q("-1.376") if disks == 25 else Q("-1.409")
    pi0, pi1 = pi_bounds()
    clo, chi = c_bounds(lam)
    _, arc_chi = c_bounds(lam - tau)
    seam = seam_upper(lam, tau, 1)
    offset = 2 * arc_chi - 3 * clo + seam
    boxes, _ = fan_line(r, lam - tau, Q(0), slope, offset=offset)
    area = r*r * (n*2*pi1*lam + (6*n-6)*chi - 2*pi0*tau + slope*pi0)
    require(area < pi0, f"{n} disks not excluded by the seam bound")
    return area, boxes


def main():
    for disks, r in NO_REPEAT_RADIUS.items():
        area, boxes = no_repeat_bound(disks)
        print(f"PASS: {disks-1} disks at r<={float(r)} require area <= {float(area):.12f}, boxes={boxes}")
        print(f"PASS: no repeated Voronoi boundary arcs for {disks} disks in this radius range")
    pi0, _ = pi_bounds()
    for separation, path in ((3, 4), (5, 6), (6, 8)):
        half_angle = pi0 - (14 - separation) * Q(".23725")
        require(2 * sin_lower(half_angle) > path * Q(".235"),
                f"Unverified distance pruning at separation {separation}")
    print("PASS: exact graph-distance pruning constants for fourteen boundary vertices")


if __name__ == "__main__":
    main()
