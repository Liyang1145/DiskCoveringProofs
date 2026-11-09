"""Verify the numerical inequalities in proof.md using only rational arithmetic."""

from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __add__(self, other):
        other = interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-interval(other))

    def __rsub__(self, other):
        return interval(other) + (-self)

    def __mul__(self, other):
        other = interval(other)
        endpoints = (
            self.lo * other.lo, self.lo * other.hi,
            self.hi * other.lo, self.hi * other.hi,
        )
        return Interval(min(endpoints), max(endpoints))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = interval(other)
        if other.lo <= 0 <= other.hi:
            raise ArithmeticError("denominator interval contains zero")
        return self * Interval(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return interval(other) / self


def interval(x):
    if isinstance(x, Interval):
        return x
    q = Q(x)
    return Interval(q, q)


def square(x):
    x = interval(x)
    lo = 0 if x.lo <= 0 <= x.hi else min(x.lo * x.lo, x.hi * x.hi)
    return Interval(Q(lo), max(x.lo * x.lo, x.hi * x.hi))


def sqrt(x):
    x = interval(x)
    if x.lo < 0:
        raise ArithmeticError("negative lower endpoint in sqrt")
    scale = 10**36

    def scaled_floor(q):
        return isqrt((q.numerator * scale**2) // q.denominator)

    return Interval(Q(scaled_floor(x.lo), scale), Q(scaled_floor(x.hi) + 1, scale))


def atan_series(x):
    term = x
    total = Q(0)
    for n in range(48):
        total += term / (2*n + 1)
        term *= -x*x
    return Interval(total, total + term / 97)


# Machin's identity, with both arctangents in the first quadrant.
PI = 16 * atan_series(Q(1, 5)) - 4 * atan_series(Q(1, 239))


def trig_series(x, parity):
    """parity 0 gives cos and parity 1 gives sin, for 0 <= x <= 1."""
    if not 0 <= x <= 1:
        raise ArithmeticError("trigonometric series outside [0, 1]")
    term = x if parity else Q(1)
    total = Q(0)
    for n in range(22):
        total += term
        k = 2*n + parity
        term *= -x*x / ((k + 1)*(k + 2))
    return Interval(total, total + term)


def sin(x):
    x = interval(x)
    return Interval(trig_series(x.lo, 1).lo, trig_series(x.hi, 1).hi)


def cos(x):
    x = interval(x)
    return Interval(trig_series(x.hi, 0).lo, trig_series(x.lo, 0).hi)


def inverse_on_unit(target, fn, increasing):
    target = interval(target)
    if not increasing:
        target = -target

    def monotone(t):
        val = fn(t)
        return val if increasing else -val

    lo, hi = Q(0), Q(1)
    if monotone(lo).hi > target.lo or monotone(hi).lo < target.hi:
        raise ArithmeticError("inverse outside [0, 1]")
    for _ in range(84):
        mid = (lo + hi) / 2
        val = monotone(mid)
        if val.hi < target.lo:
            lo = mid
        elif val.lo > target.hi:
            hi = mid
        else:
            break
    return Interval(lo, hi)


def asin(x):
    return inverse_on_unit(x, sin, True)


def acos(x):
    return inverse_on_unit(x, cos, False)


def less(a, b, name):
    diff = interval(b) - a
    if diff.lo <= 0:
        raise ArithmeticError(f"uncertified inequality: {name}")
    # Floating point is used only for this display, after the rational check.
    print(f"{name:37s}  certified margin ~ {float(diff.lo):.7g}")


def within(lo, val, hi, name):
    less(lo, val, name + " (lower)")
    less(val, hi, name + " (upper)")


def check():
    theta = PI / 7
    c, s = cos(theta), sin(theta)
    x = 2*c
    diameter_factor = 1 - 8*square(c) + 32*square(square(c))
    t = 1 / diameter_factor
    radius = sqrt(t)
    R = sqrt(diameter_factor)
    rho = sqrt(1 + 2*square(x))
    r_hi = Q("0.253252")
    r_lo = Q("0.25019")

    print("Construction and constants for the sevenfold proof")
    within("0.0641", t, "0.0642", "t")
    within("0.25325145983509235", radius, "0.25325145983509237", "r_star")
    less(radius, r_hi, "r_star < r_hi")
    within("0.90", c, "0.905", "cos(theta)")
    within("0.43", s, "0.44", "sin(theta)")
    within("3.94", R, "3.95", "R_star")
    within("2.73", rho, "2.75", "rho_star")
    less(2 * Q("0.17"), theta, "2 beta < theta")
    less(sqrt(1 + x * Q("3.7")), Q("2.8"), "rho at D=3.7")
    less(asin(1 / R), Q("0.257"), "maximum outer half arc")

    print("\nUniversal area inequality")
    M = 3*sqrt(3)/4
    G = Q(23057, 50000)
    v = (sqrt(33) - 1)/8
    less(sqrt(1 - square(v)) * (1 + 2*v), M + G, "one marked side")
    w = (sqrt(3) - 1)/2
    less((2 + w) * sqrt(1 - square(w)), M + 2*G, "two marked sides")
    less(3*sqrt(3)/2, M + 3*G, "three marked sides")
    less(r_hi, G, "edge between two boundary points")
    less(G, M, "G < M")
    less(r_hi, sqrt(Q(1, 2)), "concavity of arc-area bound")

    def arc_area(r, a):
        sa = sin(a)
        return a - sa * (cos(a) - sqrt(r*r - square(sa)))

    def straight_area(r, k):
        return r*r*((42 - k)*M + k*G)

    def area(r, b, k):
        return straight_area(r, k) + b*arc_area(r, PI/b)

    print("\nBoundary counts")
    A_hi = asin(r_hi)
    a_hi = 1 - 2*r_hi
    H_hi, C_hi = asin(r_hi / a_hi), acos(a_hi / (2*r_hi))
    less(12*A_hi, PI, "at least 13 distinct disks")
    less(sqrt(2)*r_hi, a_hi, "central half-arc monotonicity")
    less(5*H_hi + C_hi, PI, "at most 15 boundary disks")

    print("\nExclude 15 boundary disks at r_hi")

    def half_arc(circle, distance):
        return acos((circle*circle + distance*distance - r_hi*r_hi) / (2*circle*distance))

    small = Q(1, 10)
    optimum_inner_distance = sqrt(a_hi*a_hi - r_hi*r_hi)
    less(3*r_hi - a_hi, optimum_inner_distance, "central pair arc monotonicity")
    less(r_hi+small, optimum_inner_distance, "five other disks arc monotonicity")
    less(half_arc(a_hi, r_hi+small), PI-4*H_hi-2*C_hi, "five disks miss the small circle")
    less(r_hi*r_hi, (a_hi-r_hi)**2+small*small, "central pair covers less than a circle")
    less(small, a_hi, "outer disks miss the small circle")

    y = Q(521, 1000)
    h = asin(r_hi / y)
    omega = acos((1 + y*y - 4*r_hi*r_hi) / (2*y))
    short_arc = half_arc(1, y+r_hi)
    deficit = 2*(H_hi-h)
    total_deficit = 12*H_hi-2*PI
    less(2*r_hi, y, "central disk misses witness circle")
    less(y+r_hi, sqrt(1-r_hi*r_hi), "witness disk arc monotonicity")
    less(A_hi, H_hi, "inner arc bound > outer arc bound")
    less(total_deficit, 3*deficit, "at least four witness gaps")
    less(2*A_hi, 2*h-2*omega, "q=0 boundary interval")
    less(6*A_hi, 4*H_hi-total_deficit+deficit-2*omega, "four witnesses, q=1")
    less(10*A_hi, 6*H_hi-total_deficit-2*omega, "four witnesses, q>=2")
    less(4*A_hi, 4*H_hi-total_deficit-2*omega, "five witnesses, q=1")
    less(11*A_hi+short_arc, PI, "four witnesses need >=2 used arcs")
    less(10*A_hi+4*short_arc, PI, "five witnesses need all five arcs")
    less(9*A_hi+6*short_arc, PI, "six witnesses: arcs too short")

    print("\nRemaining generic branches at r <= r_star")
    for b, k in ((13, 14), (14, 16)):
        less(area(r_hi, b, k), PI, f"excluded: b={b}, k>={k}")
    L = r_hi / (1 + sqrt(1 - r_hi*r_hi))
    lhs = area(r_hi, 14, 15) - 2*r_hi*r_hi*(G - L)
    less(lhs, PI, "excluded: b=14, one enclosed arc")
    less(area(Q("0.25201"), 13, 13), PI, "b=13 also needs r > 0.25201")

    print("\nGeometric restrictions on the remaining Voronoi graphs")
    S2, S3 = asin(2*r_hi), asin(3*r_hi)
    less(16*A_hi, 2*PI-2*S3, "short-span orientation")
    less(10*A_hi+S2, PI, "exclude long boundary chords")
    less(8*A_hi+2*S2, PI, "exclude two disjoint chords for b=14")
    for b in (13, 14):
        m = b-9
        less(S3/m, PI/b, f"small angular block, b={b}")
        bound = straight_area(r_hi, b) + m*arc_area(r_hi, S3/m)
        bound += 9*arc_area(r_hi, (PI-S3)/9)
        less(bound, PI, f"exclude a common neighbor, b={b}")
    less(3*r_hi, sqrt(1-r_hi*r_hi), "origin-neighbor arc monotonicity")
    thin = Q(1, 10)
    less(half_arc(1, 3*r_hi), thin, "origin-neighbor arc is short")
    less(thin, PI/13, "thin arc below equal share")
    bound = straight_area(r_hi, 13) + arc_area(r_hi, thin)
    bound += 12*arc_area(r_hi, (PI-thin)/12)
    less(bound, PI, "b=13: origin disk has no boundary neighbor")

    for b, cycle, enclosed in ((13, 3, 1), (13, 4, 1), (14, 3, 1), (14, 4, 2)):
        polygon = sqrt(3) if cycle == 3 else 4
        faces = cycle - 2 + 2*enclosed
        loss = faces*M - polygon - cycle*(Q(1, 2)-G)
        less(area(r_hi, b, b)-r_hi*r_hi*loss, PI,
             f"b={b}: no {cycle}-cycle enclosing {enclosed} sites")

    bound = straight_area(r_hi, 14) + 2*arc_area(r_hi, thin)
    bound += 12*arc_area(r_hi, (PI-2*thin)/12)
    less(bound, PI, "b=14: origin disk has at most one boundary neighbor")
    cap_pair = (2+w)*sqrt(1-square(w))
    for marks in range(1, 5):
        quad = 2+cap_pair if marks == 1 else 2*cap_pair+Q(marks-2, 2)
        loss = 4*M + marks*G - quad
        less(area(r_hi, 14, 14)-r_hi*r_hi*loss, PI,
             f"b=14: no filled 4-cycle with {marks} boundary edges")
    pentagon = 5*cos(PI/5)/sin(PI/5)
    loss = 7*M - pentagon - 5*(Q(1, 2)-G)
    less(area(r_hi, 14, 14)-r_hi*r_hi*loss, PI,
         "b=14: no 5-cycle enclosing two sites")
    less(area(r_hi, 14, 14)-2*r_hi*r_hi*(4*M-4), PI,
         "b=14: no two disjoint degree-four stars")
    gamma = 2*PI/9
    degree_loss = 9*(M-sin(gamma)*(1+cos(gamma)))
    less(area(r_hi, 14, 14)-r_hi*r_hi*(degree_loss-2*(Q(1, 2)-G)), PI,
         "b=14: no degree >=9 with <=2 marked faces")
    less(S3/4, PI/14, "b=14: four-arc block below average")
    bound = straight_area(r_hi, 14) - r_hi*r_hi*(degree_loss-3*(Q(1, 2)-G))
    bound += 4*arc_area(r_hi, S3/4) + 10*arc_area(r_hi, (PI-S3)/10)
    less(bound, PI, "b=14: no degree >=9 with 3 marked faces")

    print("\nExclude all generic covers at the lower test radius")
    for b in (13, 14):
        less(area(r_lo, b, b), PI, f"excluded: b={b}, k>=b")


if __name__ == "__main__":
    check()
