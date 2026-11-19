"""Exact polar-cell angular bounds for anchored_search.cpp."""
import argparse
from fractions import Fraction as Q
from itertools import chain
from math import acos, ceil, factorial, isqrt, pi

TURN = 1008000000
SCALE = 10**9
R = 361102964
START = SCALE-R
END = 933000000
RINGS = (
    278, 295, 313, 326, 340, 354, 365, 380, 394, 408, 421, 437, 453, 470,
    488, 506, 525, 545, 565, 586, 607, 627, 642, 665, 690, 720, 760,
    810, 880, 1000,
)
DEAD = -2*TURN
PI_LO = Q("3.141592653589793238462643383279")
PI_HI = Q("3.141592653589793238462643383280")
COEFF = [Q((-1)**j, factorial(2*j)) for j in range(12, -1, -1)]


def check_constants():
    def arctan(q):
        x = Q(1, q)
        lo = sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(24))
        return lo, lo+x**49/49
    a, b = arctan(5)
    c, d = arctan(239)
    assert PI_LO < 16*a-4*d
    assert 16*b-4*c < PI_HI
    assert END**2 > SCALE**2-R**2
    assert 3*(778070000-R)**2 > 4*R**2
    # asin(r) < .370 radians < .059 turns.
    phi = Q(".370")
    assert phi-phi**3/6 > Q(R, SCALE)
    assert phi < 2*PI_LO*Q(".059")


def beta(s, lo, hi):
    if lo > s+R or hi < s-R:
        return DEAD
    if lo == 0 and s <= R:
        return TURN//2
    a = s*s-R*R
    if hi*hi <= a:
        g = Q(a+hi*hi, 2*s*hi)
    elif lo*lo >= a:
        g = Q(a+lo*lo, 2*s*lo)
    else:
        q = 10**18
        g = Q(isqrt(a*q*q), s*q)
    if g >= 1:
        return 0
    if g <= -1:
        return TURN//2

    def verifies(h):
        if h >= TURN//2:
            return True
        x2 = (2*PI_LO*h/TURN)**2
        v = COEFF[0]
        for c in COEFF[1:]:
            v = v*x2+c
        return v <= g

    lo_h = max(0, min(TURN//2, ceil(acos(float(g))*TURN/(2*pi))+1))
    hi_h = lo_h
    while not verifies(hi_h):
        step = max(1, 2*(hi_h-lo_h))
        hi_h = min(TURN//2, hi_h+step)
    return hi_h


def bins(lo, hi, n):
    return [(lo+(hi-lo)*i//n, lo+(hi-lo)*(i+1)//n) for i in range(n)]


def generate(n):
    radii = set(chain(
        bins(START, 778070000, max(5,n//2)),
        bins(START, 2*R, max(5,n//2)),
        bins(START, END, n),
        bins(0, START, 2*n),
    ))
    for ring in RINGS:
        s = ring*1000000
        for lo,hi in sorted(radii):
            yield s,lo,hi,beta(s,lo,hi)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("n_radial", type=int)
    p.add_argument("output")
    args = p.parse_args()
    check_constants()
    with open(args.output, "w", encoding="ascii") as out:
        for row in generate(args.n_radial):
            print(*row, file=out)
