"""Check the numerical inequalities used in the N=25 proof with rational intervals."""

from argparse import ArgumentParser
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product
from math import isqrt


SCALE = 10**30


def ceil_div(a, b):
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    # Both endpoints are integers in units of 1/SCALE.
    lo: int
    hi: int

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __add__(self, other):
        other = rational(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-rational(other))

    def __rsub__(self, other):
        return rational(other) + (-self)

    def __mul__(self, other):
        other = rational(other)
        products = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(products) // SCALE, ceil_div(max(products), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = rational(other)
        assert other.lo > 0 or other.hi < 0
        quotients = [(a * SCALE, b) for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(
            min(a // b for a, b in quotients),
            max(ceil_div(a, b) for a, b in quotients),
        )

    def __rtruediv__(self, other):
        return rational(other) / self


def rational(numerator, denominator=1):
    if isinstance(numerator, Interval):
        return numerator
    assert isinstance(numerator, int) and isinstance(denominator, int) and denominator > 0
    scaled = numerator * SCALE
    return Interval(scaled // denominator, ceil_div(scaled, denominator))


def sqrt(value):
    value = rational(value)
    assert value.lo >= 0
    low = isqrt(value.lo * SCALE)
    high = isqrt(value.hi * SCALE)
    return Interval(low, high + (high * high < value.hi * SCALE))


def positive(value, label):
    if value.lo <= 0:
        raise ArithmeticError(f"Could not establish {label} with interval {value}")


def with_tail(value, term):
    error = max(abs(term.lo), abs(term.hi))
    return Interval(value.lo - error, value.hi + error)


def atan_small(x):
    # Alternating series, with the first omitted term as an error bound.
    assert max(abs(x.lo), abs(x.hi)) < SCALE
    square = x * x
    power = x
    total = rational(0)
    for k in range(100):
        total += power / (2 * k + 1)
        power *= -square
    return with_tail(total, power / 201)


PI = 16 * atan_small(rational(1, 5)) - 4 * atan_small(rational(1, 239))


def sin_cos(x):
    assert 0 <= x.lo <= x.hi <= SCALE
    square = x * x
    sin_term, cos_term = x, rational(1)
    sine, cosine = rational(0), rational(0)
    for k in range(20):
        sine += sin_term
        cosine += cos_term
        sin_term *= -square / ((2 * k + 2) * (2 * k + 3))
        cos_term *= -square / ((2 * k + 1) * (2 * k + 2))
    return with_tail(sine, sin_term), with_tail(cosine, cos_term)


def atan_nonnegative(x):
    assert x.lo >= 0
    if x.hi <= SCALE // 2:
        return atan_small(x)

    def endpoint(value):
        point = Interval(value, value)
        if value <= SCALE // 2:
            return atan_small(point)
        return PI / 4 + atan_small((point - 1) / (point + 1))

    if x.lo == x.hi:
        return endpoint(x.lo)
    return Interval(endpoint(x.lo).lo, endpoint(x.hi).hi)


def asin(x):
    assert 0 <= x.lo <= x.hi < SCALE
    tangent = x / sqrt(1 - x * x)
    return atan_nonnegative(tangent)


def display(value, digits=9):
    step = SCALE // 10**digits

    def format_endpoint(endpoint):
        sign = "-" if endpoint < 0 else ""
        whole, fractional = divmod(abs(endpoint), 10**digits)
        return f"{sign}{whole}.{fractional:0{digits}d}"

    lo = format_endpoint(value.lo // step)
    hi = format_endpoint(ceil_div(value.hi, step))
    return f"[{lo}, {hi}]"


SPAN_PRICE = rational(7, 4)
ACTIVE_SPAN_CAPS = (rational(737, 1000), rational(1131, 1000))


def arc_cosine(t, u):
    return (t * t + u * u - 1) / (2 * t * u)


def half_arc(t, u):
    cosine = arc_cosine(t, u)
    assert 0 < cosine.lo <= cosine.hi < SCALE
    return asin(sqrt(1 - cosine * cosine))


def arc_derivatives(t, u):
    x = arc_cosine(t, u)
    sine = sqrt(1 - x * x)
    derivative_t = -(t * t - u * u + 1) / (2 * t * t * u * sine)
    derivative_u = -(u * u - t * t + 1) / (2 * t * u * u * sine)
    return derivative_t, derivative_u


def rim_angle_below(radius, inward_limit, upper_q, bound):
    """Compare the maximum rim angle at center radius <= 1+upper_q with bound."""
    if bound.lo <= 0:
        return False
    _, upper_cosine = sin_cos(Interval(bound.lo, bound.lo))
    t_max = SCALE + upper_q
    if t_max >= inward_limit.lo:
        lower_cosine = inward_limit / radius
    else:
        lower_cosine = arc_cosine(Interval(t_max, t_max), radius)
    return lower_cosine.lo > upper_cosine.hi


@lru_cache(maxsize=None)
def seam_gap_trig(endpoint):
    angle = Interval(endpoint, endpoint)
    sine_half, cosine_half = sin_cos(angle / 2)
    _, cosine = sin_cos(angle)
    return sine_half, cosine_half, cosine


def seam_q_upper(d_lo, u_hi):
    # G decreases with d and increases with u. Use the appropriate corner.
    sine, cosine_half, cosine = seam_gap_trig(d_lo)
    u_max = Interval(u_hi, u_hi)
    upper_q = (1 / sine).hi
    if (cosine - u_max * sine).lo > 0:
        v = u_max * sine
        formula = u_max * cosine + 2 * cosine_half * sqrt(1 - v * v)
        upper_q = min(upper_q, formula.hi)
    return upper_q


def check_classification_and_symmetry():
    radius = sqrt(6) + sqrt(3)
    root_two = sqrt(2)
    cos_delta = sqrt(2 + root_two) / 2
    sin_delta = sqrt(2 - root_two) / 2
    a0 = 2 * cos_delta
    b0 = 2 + root_two
    c0 = 2 * a0
    w0 = sqrt(9 * cos_delta * cos_delta + sin_delta * sin_delta)
    b_min = rational(67, 20)
    w_max = rational(141, 50)
    inward_limit = sqrt(radius * radius - 1)

    sin_pi_13, _ = sin_cos(PI / 13)
    positive(sin_pi_13 - 1 / radius, "at least 14 rim disks")
    positive(radius - 4, "at least 7 disks at the inner circle")
    positive(sin_delta - 1 / radius, "maximum outer arc is shorter than delta")
    positive(inward_limit - c0, "c0 is on the increasing branch")
    positive(b_min - (radius - 1), "b_min lies on the boundary-reaching branch")
    positive(b0 - b_min, "b_min < b0")
    positive(
        arc_cosine(b_min, radius)
        - (cos_delta * sqrt(1 - 1 / (radius * radius)) + sin_delta / radius),
        "b > 67/20 from the rim angle budget",
    )

    b_rim_dt, _ = arc_derivatives(b0, radius)
    c_rim_dt, _ = arc_derivatives(c0, radius)
    positive(c_rim_dt, "c0 outer arc derivative is positive")
    positive(b_rim_dt - rational(5, 2) * c_rim_dt, "c >= c0 + (5/2)s")
    positive(rational(113, 1000) - c_rim_dt, "c0 outer arc derivative < .113")

    positive(w0 - rational(25, 9), "(1+w)/w < 1.36")
    positive(w_max - (w0 + (b0 - b_min) / 3), "w < 2.82")
    positive(a0 + 1 - w_max, "A arc stays positive")
    positive(w0 * w0 - 1 - a0 * a0, "A arc increases with the inner radius")
    positive(1 - b0 + w0, "B arc stays positive")
    positive(b_min * b_min - w_max * w_max - 1, "B increases in w and decreases in b")
    positive(c0 - b_min, "C increases in w and decreases in c")
    positive(w_max + 1 - c0, "C derivative at (c0,w_max) is defined")
    positive(arc_cosine(a0, w0) - arc_cosine(b0, w0), "A(0) < B(0)")
    positive(arc_cosine(b_min, w_max) - cos_delta, "B < delta")
    positive(arc_cosine(c0, w_max) - cos_delta, "C < delta")

    _, a_w_du = arc_derivatives(a0, w0)
    b_w_dt, b_w_du = arc_derivatives(b0, w0)
    c_w_dt, _ = arc_derivatives(c0, w_max)
    positive(-a_w_du - rational(136, 100), "A has w derivative < -1.36")
    positive(rational(293, 1000) + b_w_dt, "-dB/db < .293")
    positive(rational(210, 1000) - b_w_du, "dB/dw < .210")
    positive(-c_w_dt - rational(58, 100), "-dC/dc > .58")
    positive(rational(136, 300) - rational(363, 1000), "A+B is decreasing in s")
    positive(
        rational(58, 100) * (rational(5, 2) - rational(136, 300))
        - rational(5, 2) * rational(113, 1000) - rational(363, 1000),
        "B+C+outer arc widths are decreasing along c*(s)",
    )
    print("rim classification and rotational-case constants verified")
    print("construction radius:", display(1 / radius, digits=20))


def check_seven_inner_disks():
    radius = sqrt(6) + sqrt(3)
    inner_radius = radius - 2
    outer_center_min = radius - 1
    inward_limit = sqrt(radius * radius - 1)
    inner_width = asin(1 / inner_radius)
    outer_width = asin(1 / radius)
    regular_gap = 2 * PI / 7

    gap_lower = 2 * PI - 12 * inner_width
    gap_upper = 2 * inner_width
    box_left = rational(568, 1000)
    box_right = rational(953, 1000)
    positive(gap_lower - inner_width, "each gap exceeds every individual inner half-arc")
    positive(gap_lower - box_left, "lower endpoint for all seam gaps")
    positive(box_right - gap_upper, "upper endpoint for all seam gaps")
    positive(2 * PI - 10 * inner_width - rational(3, 2), "sum of any two gaps exceeds 1.5")

    # For t >= 1.5 use the universal bound on the arc at inner_radius.
    # Below 1.5 the two summands are monotone in opposite directions.
    polar_limit = PI - 4 * inner_width
    split_points = (
        inner_radius - 1, rational(122, 100), rational(127, 100),
        rational(132, 100), rational(137, 100), rational(142, 100),
        rational(147, 100), rational(3, 2),
    )
    positive(inner_radius * inner_radius - 1 - rational(9, 4), "inner half-arc increases up to 1.5")
    for left, right in zip(split_points, split_points[1:]):
        upper = asin(1 / left) + half_arc(right, inner_radius)
        positive(polar_limit - upper, "nonadjacent inner disks have disjoint polar projections")
    positive(polar_limit - asin(rational(2, 3)) - inner_width, "disjoint polar projections for t >= 1.5")

    split_radius = rational(12, 5)
    positive(split_radius - inner_radius, "seam radii can be split at 2.4")
    positive(outer_center_min * outer_center_min - 1 - split_radius * split_radius,
             "outer half-arc increases with u up to 2.4 at t=R-1")
    positive(rational(3, 4) - inner_width - half_arc(outer_center_min, split_radius),
             "width bound at seam radii <= 2.4")
    positive(rational(3, 4) - asin(1 / split_radius) - asin(1 / outer_center_min),
             "width bound at seam radii >= 2.4")

    def check_angle_upper(upper_q, affine):
        if upper_q < inner_radius.lo:
            return True
        return rim_angle_below(radius, inward_limit, upper_q, affine)

    ranges = [(box_left.lo, box_right.hi)]
    checked_ranges = 0
    while ranges:
        d_lo, d_hi = ranges.pop()
        checked_ranges += 1
        upper_q = (1 / seam_gap_trig(d_lo)[0]).hi
        gap = Interval(d_lo, d_hi)
        bound = rational(132, 1000) - rational(1129, 1000) * (gap - regular_gap)
        if check_angle_upper(upper_q, bound):
            continue
        if d_hi - d_lo < SCALE // 2**20:
            raise ArithmeticError("one-dimensional seam inequality unresolved")
        mid = (d_lo + d_hi) // 2
        ranges.extend(((d_lo, mid), (mid, d_hi)))
    smaller_rim_deficit = PI - 7 * rational(132, 1000) - 9 * outer_width
    positive(smaller_rim_deficit, "seven seam disks and at most 9 other rim disks are insufficient")
    print(f"seven inner disks excluded with b <= 16: {checked_ranges} intervals, "
          f"rim half-angle deficit {display(smaller_rim_deficit)}")

    def check_box(d_lo, d_hi, u_lo, u_hi):
        upper_q = seam_q_upper(d_lo, u_hi)
        sine_range = Interval(seam_gap_trig(d_lo)[0].lo, seam_gap_trig(d_hi)[0].hi)
        u = Interval(u_lo, u_hi)
        gap = Interval(d_lo, d_hi)
        affine = (
            rational(1, 10)
            - rational(1093, 1000) * (gap - regular_gap)
            + rational(199, 500) * sine_range * (u - 1)
        )
        return check_angle_upper(upper_q, affine)

    boxes = [(box_left.lo, box_right.hi, 0, 2 * SCALE)]
    visited = 0
    while boxes:
        d_lo, d_hi, u_lo, u_hi = boxes.pop()
        visited += 1
        if check_box(d_lo, d_hi, u_lo, u_hi):
            continue
        if max(d_hi - d_lo, u_hi - u_lo) < SCALE // 2**20:
            raise ArithmeticError("seam inequality unresolved on a box of width below 2^-20")
        if 5 * (d_hi - d_lo) >= u_hi - u_lo:
            mid = (d_lo + d_hi) // 2
            boxes.extend(((d_lo, mid, u_lo, u_hi), (mid, d_hi, u_lo, u_hi)))
        else:
            mid = (u_lo + u_hi) // 2
            boxes.extend(((d_lo, d_hi, u_lo, mid), (d_lo, d_hi, mid, u_hi)))

    deficit = PI - rational(7, 10) - 10 * outer_width
    positive(deficit, "seven distinct seam disks make the 17-disk rim budget too small")
    print(f"17 boundary disks excluded: {visited} boxes, rim half-angle deficit {display(deficit)}")


REPEAT_LOSS_ONE = rational(1047, 500)
REPEAT_LOSS_TWO = rational(2829, 1000)
REPEAT_ADJACENT_LOSS = rational(17, 200)


def fan_price_max(price):
    cosine = (sqrt(9 + 8 * price) - 1) / 4
    alpha = PI / 2 - asin(cosine)
    return sqrt(1 - cosine * cosine) * (1 + cosine) - price * alpha


def check_repeat_area_losses():
    a0 = 3 * sqrt(3) / 4
    for groups, price, required_loss in (
        (1, rational(23, 20), REPEAT_LOSS_ONE),
        (2, rational(21, 25), REPEAT_LOSS_TWO),
    ):
        x = price / 4
        middle = 4 * sqrt(1 - x * x) - price * (PI / 2 - asin(x))
        if price.lo > SCALE:
            x = price / 2
            low = sqrt(3) + 2 * sqrt(1 - x * x) - price * (PI / 2 - asin(x))
        else:
            low = 2 * sqrt(3) - price * PI / 3
        group_bound = Interval(max(low.lo, middle.lo), max(low.hi, middle.hi))
        pair_count = 8 - 2 * groups
        area_upper = groups * group_bound + 2 * pair_count * fan_price_max(price / 2) + 2 * PI * price
        loss = 16 * a0 - area_upper
        positive(loss - required_loss, f"area deduction for {groups} repeated connectors")
        print(f"{groups} repeated connectors: paired-star area deduction {display(loss)}")


def check_repeat_with_sixteen_active_arcs():
    radius = sqrt(6) + sqrt(3)
    a0 = 3 * sqrt(3) / 4
    price = rational(23, 20)
    extra = REPEAT_ADJACENT_LOSS
    side = rational(39, 20)
    side_half = side / 2
    side_cosine = sqrt(1 - side_half * side_half)

    x = price / 4
    middle = 4 * sqrt(1 - x * x) - price * (PI / 2 - asin(x))
    x = price / 2
    low = sqrt(3) + 2 * sqrt(1 - x * x) - price * (PI / 2 - asin(x))
    high = 4 - price * PI / 2
    positive(middle - low - extra, "repeat area loss for s <= pi/3")
    positive(middle - high - extra, "repeat area loss for s >= pi/2")

    long_loss = rational(23, 500)
    normal_pair = 2 * fan_price_max(price / 2)
    equal_angle_limit = 2 * side_half * side_cosine
    cap_angle = sqrt(3) / 2
    intervals = [(0, SCALE)]
    visited = 0
    while intervals:
        lo, hi = intervals.pop()
        visited += 1
        sine = Interval(lo, hi)
        cosine = sqrt(1 - sine * sine)
        fan = sine * (1 + cosine)
        cap_upper = fan if sine.hi <= cap_angle.lo else a0
        central = fan
        if sine.lo >= equal_angle_limit.hi:
            central = 2 * sine * side_half * (sine * side_cosine + cosine * side_half)
        angle_lower = asin(Interval(lo, lo))
        upper = cap_upper + central - price * angle_lower
        if upper.hi < (normal_pair - long_loss).lo:
            continue
        if hi - lo < SCALE // 2**22:
            raise ArithmeticError("long radial edge paired-star deduction unresolved")
        mid = (lo + hi) // 2
        intervals.extend(((lo, mid), (mid, hi)))

    positive((4 - side * side) * sqrt(3) / 4 - extra, "both radial edges are short")
    positive((2 - side) * sqrt(3) / 2 + long_loss - extra, "one radial edge is long")
    positive(2 * long_loss - extra, "both radial edges are long")
    weight, increment = rational(9, 50), rational(139, 1000)
    _, height, _ = rim_fan_at_mean(radius, 16, weight)
    slack = 32 * a0 + 16 * (increment + height) - 2 * weight * PI - PI * radius * radius
    deficit = REPEAT_LOSS_ONE + extra - slack
    positive(deficit, "degree-8 core with all 16 outer cells active has no repeated connector")
    print(f"16 active cells, degree-8 core: repeated connector excluded on {visited} intervals, "
          f"area deficit {display(deficit)}")


def check_degree_eight_seam_charges():
    radius = sqrt(6) + sqrt(3)
    inner_radius = radius - 2
    inward_limit = sqrt(radius * radius - 1)
    rim_width = asin(1 / radius)
    regular_gap = PI / 4
    intercept = rational(141, 2000)
    slope = rational(23, 50)
    eccentricity_weight = rational(59, 200)
    cap = rational(19, 125)
    pair_cap = rational(41, 250)
    low, high = rational(2, 5), rational(953, 1000)
    positive(high - 2 * asin(1 / inner_radius), "degree-8 seam gap domain")
    positive(2 * PI - 12 * asin(1 / inner_radius), "at most one nonpositive directed gap")
    positive(2 * slope - eccentricity_weight, "negative directed gaps have no higher charge")
    low_sine, _ = sin_cos(low / 2)
    positive(-(intercept + slope * (low - regular_gap) + eccentricity_weight * low_sine),
             "small gaps have nonpositive charge")

    boxes = [(low.lo, high.hi, 0, 2 * SCALE)]
    visited = 0
    while boxes:
        d_lo, d_hi, u_lo, u_hi = boxes.pop()
        visited += 1
        upper_q = seam_q_upper(d_lo, u_hi)
        if upper_q < inner_radius.lo:
            continue
        sine = Interval(seam_gap_trig(d_lo)[0].lo, seam_gap_trig(d_hi)[0].hi)
        gap = Interval(d_lo, d_hi)
        u = Interval(u_lo, u_hi)
        charge = intercept + slope * (gap - regular_gap) - eccentricity_weight * sine * (u - 1)
        if charge.hi < cap.lo and rim_angle_below(radius, inward_limit, upper_q, rim_width - charge):
            continue
        if max(d_hi - d_lo, u_hi - u_lo) < SCALE // 2**22:
            raise ArithmeticError("degree-8 seam charge unresolved")
        if 5 * (d_hi - d_lo) >= u_hi - u_lo:
            mid = (d_lo + d_hi) // 2
            boxes.extend(((d_lo, mid, u_lo, u_hi), (mid, d_hi, u_lo, u_hi)))
        else:
            mid = (u_lo + u_hi) // 2
            boxes.extend(((d_lo, d_hi, u_lo, mid), (d_lo, d_hi, mid, u_hi)))

    print(f"degree-8 single-edge charges verified on {visited} boxes")

    center_min = radius - 1
    max_gap = 2 * asin(1 / inner_radius)
    max_span = 2 * asin(2 / center_min)
    positive(2 * PI - 5 * max_gap - max_span, "nonadjacent connector edges: directed span exceeds the cone")
    positive(2 * PI - 2 * max_span - 2 * max_gap, "nonadjacent connector edges: both spans cannot wrap")
    positive(2 * PI - max_span - 2 * max_gap, "adjacent connector edges: sum cannot wrap")

    q_min = rational(109, 50)
    positive(inner_radius - q_min, "pair charge uses q >= 2.18")
    _, half_cosine = sin_cos(high / 2)
    positive(half_cosine - rational(7, 8), "pair charge uses cos(d/2) >= 7/8")
    common = (13 * q_min - 1) / 4
    positive(rational(7, 8) + rational(21, 16) * q_min * q_min - common,
             "pair charge concavity when the square root is at least 1/2")
    positive(rational(21, 8) * (q_min * q_min - 2) - common,
             "pair charge concavity when the square root is at most 1/2")

    def pair_at_limit(t):
        q = t - 1
        sine = 2 / t
        cosine = sqrt(1 - sine * sine)
        sine_half = sqrt((1 - cosine) / 2)
        cosine_half = sqrt((1 + cosine) / 2)
        square_root = 1 - q * q * sine_half * sine_half
        if square_root.lo <= 0:
            return None
        h = sqrt(square_root)
        tilt = sine_half * (1 - q + 2 * q * sine_half * sine_half) + sine * h
        tilt_derivative = (
            cosine_half * (1 - q + 6 * q * sine_half * sine_half) / 2
            + cosine * h - q * q * sine * sine / (4 * h)
        )
        charge = intercept + slope * (asin(sine) - regular_gap) + eccentricity_weight * tilt
        return 2 * charge, slope + eccentricity_weight * tilt_derivative

    pair_upper, _ = pair_at_limit(center_min)
    positive(pair_cap - pair_upper, "inactive disk with two seam edges has charge below .164")
    intervals = [(center_min.lo, inward_limit.hi)]
    visited = 0
    while intervals:
        t_lo, t_hi = intervals.pop()
        visited += 1
        result = pair_at_limit(Interval(t_lo, t_hi))
        if result is not None:
            charge, derivative = result
            if derivative.lo > 0 and rim_angle_below(radius, inward_limit, t_hi - SCALE, rim_width - charge):
                continue
        if t_hi - t_lo < SCALE // 2**22:
            raise ArithmeticError("degree-8 paired connector charge unresolved")
        mid = (t_lo + t_hi) // 2
        intervals.extend(((t_lo, mid), (mid, t_hi)))
    print(f"degree-8 double-edge charges verified on {visited} intervals")

    a0 = 3 * sqrt(3) / 4
    for m, lam, inc in (
        (14, rational(0), rational(231, 500)),
        (15, rational(107, 500), rational(4009, 50000)),
        (16, rational(9, 50), rational(139, 1000)),
    ):
        _, height, _ = rim_fan_at_mean(radius, m, lam)
        slack = (48 - m) * a0 + m * (inc + height) - 2 * lam * PI - PI * radius * radius
        positive(REPEAT_LOSS_TWO - slack, "two repeated connectors violate area bound")

    positive(pair_cap - cap, "repeat charge cap dominates single charge cap")
    loss14 = 8 * intercept - cap - pair_cap - (14 * rim_width - PI)
    positive(loss14, "16 outer, 14 active, degree-8 core impossible")
    print(f"16 outer, 14 active, degree-8 core excluded: rim half-angle deficit {display(loss14)}")
    negative_gain = slope * regular_gap - intercept
    positive(negative_gain - cap, "a group with a nonpositive step has nonpositive charge")
    positive(8 * intercept - (15 * rim_width - PI), "the inactive disk at m=15 must be a connector")
    positive(8 * intercept + negative_gain - pair_cap - (15 * rim_width - PI),
             "nonpositive step with active connector at m=15")
    positive(8 * intercept + negative_gain - (16 * rim_width - PI), "nonpositive step at m=16")


def check_core_requires_inner_exterior():
    radius = sqrt(6) + sqrt(3)
    inner_radius = radius - 2
    width = asin(1 / radius)
    max_gap = 2 * asin(1 / inner_radius)
    positive(2 * PI - 6 * max_gap, "at most six all-outer exterior sides cannot span the core")
    positive(2 * PI - 5 * max_gap - 2 * asin(2 / (radius - 1)),
             "seven all-outer exterior sides have distinct connectors")
    seven_charge_cap = rational(9, 25)
    largest_seven_charge = (
        width - rational(1, 10)
        + rational(1093, 1000) * (max_gap - 2 * PI / 7)
        + rational(199, 500) * (3 - inner_radius) / inner_radius
    )
    positive(seven_charge_cap - largest_seven_charge, "individual seven-edge charge below .36")
    for m in (14, 15, 16):
        deficit = 7 * (width - rational(1, 10)) - (16 - m) * seven_charge_cap - (m * width - PI)
        positive(deficit, "seven all-outer exterior sides exceed rim budget")
    positive(rational(141, 250) - rational(41, 250) - (14 * width - PI),
             "eight all-outer exterior sides with at most one inactive connector, m=14")
    positive(rational(141, 250) - (15 * width - PI),
             "eight all-outer exterior sides with all connectors active, m=15")
    print("every origin-covering core needs an all-inner exterior triangle")


def check_wide_core_cone():
    radius = sqrt(6) + sqrt(3)
    radial = radius - 3
    gap = 2 * asin(1 / (radius - 2))
    root_limit = rational(203, 100)
    positive(root_limit - 2 * asin(1 / radial), "wide-side chord span")
    xi = PI / 2 - asin((3 - radial * radial) / (2 * radial))
    swing = root_limit / 2 - xi
    _, cosine = sin_cos(swing)
    positive(radial - 2 + cosine, "a core outside the unit circle cannot cross the opposite ray")
    positive(PI - 2 * gap, "a maximal two-core block exceeds a half-turn")
    sine, cosine = sin_cos(gap)
    end = -radial * cosine + sqrt(4 - radial * radial * sine * sine)
    positive(rational(1069, 1000) - end, "wide-side core can be chosen within radius 1.069")
    positive(radial - rational(1069, 1000), "wide-side core is still deep")
    print(f"wide-side two-core annulus is within radius {display(end)}")
    positive(PI - 3 * gap, "wide-side complement of three edges spans less than a half-turn")
    sine = 1 / (radius - 2)
    cosine = sqrt(1 - sine * sine)
    sin_three = 3 * sine - 4 * sine * sine * sine
    cos_three = 4 * cosine * cosine * cosine - 3 * cosine
    end = -radial * cos_three + sqrt(4 - radial * radial * sin_three * sin_three)
    positive(rational(1455, 1000) - end, "six-edge side of nine-ring can be swapped into radius 1.455")
    print(f"six-edge side of the two-core nine-ring is within radius {display(end)}")


def check_inner_octagon_types():
    size = 8
    core = size
    radius = sqrt(6) + sqrt(3)
    gap_max = 2 * asin(1 / (radius - 2))
    repeat_max = 2 * asin(2 / (radius - 1))
    positive(2 * gap_max - repeat_max, "each repeat reduces the maximum sum of gaps")
    positive(2 * PI - 3 * repeat_max - 2 * gap_max, "at most two repeat groups")

    inward_limit = sqrt(radius * radius - 1)
    rim_width = asin(1 / radius)
    slope = rational(5, 4)
    single_cap, repeat_cap = rational(1012, 1000), rational(1517, 1000)
    visited = 0
    for maximum, intercept, multiplicity in ((gap_max, single_cap, 1), (repeat_max, repeat_cap, 2)):
        positive(intercept - slope / 2, "small interface groups have a trivial arc bound")
        intervals = [(SCALE // 2, maximum.hi)]
        while intervals:
            lo, hi = intervals.pop()
            visited += 1
            sine, _ = sin_cos(Interval(lo, lo) / 2)
            cap = (1 + 1 / sine) if multiplicity == 1 else 2 / sine
            bound = rim_width + intercept - slope * Interval(hi, hi)
            if (cap.hi < (radius - 1).lo or bound.lo > rim_width.hi
                    or rim_angle_below(radius, inward_limit, cap.hi - SCALE, bound)):
                continue
            if hi - lo < SCALE // 2**20:
                raise ArithmeticError("rim charge for interface groups unresolved")
            mid = (lo + hi) // 2
            intervals.extend(((lo, mid), (mid, hi)))

    minimum = None
    for m in (14, 15, 16):
        for inactive_single in range(17 - m):
            for inactive_repeat in range(17 - m - inactive_single):
                total = 2 * PI - inactive_single * gap_max - inactive_repeat * repeat_max
                loss = slope * total - (4 - inactive_single) * single_cap - (2 - inactive_repeat) * repeat_cap
                deficit = loss - (m * rim_width - PI)
                positive(deficit, "two interface repeat groups violate rim coverage")
                if minimum is None or deficit.lo < minimum.lo:
                    minimum = deficit
    print(f"two interface repeat groups excluded on {visited} intervals, rim half-angle deficit {display(minimum)}")

    for m in (14, 15):
        for groups in range(1, 7):
            for multiple in range(1, min(groups, 9 - groups) + 1):
                if groups == 6 and multiple == 3:
                    continue
                single = groups - multiple
                if (single * gap_max + multiple * repeat_max).hi < (2 * PI).lo:
                    continue
                for i in range(min(single, 15 - m) + 1):
                    for j in range(min(multiple, 15 - m - i) + 1):
                        active_span = 2 * PI - i * gap_max - j * repeat_max
                        loss = slope * active_span - (single - i) * single_cap - (multiple - j) * repeat_cap
                        positive(loss - (m * rim_width - PI), "nine positive edges need at least six connectors")
    print("nine positive interface edges with fifteen outer sites need at least six connectors; six means three pairs")
    for single, multiple in ((3, 3), (6, 1)):
        loss = slope * 2 * PI - single * single_cap - multiple * repeat_cap
        positive(loss - (14 * rim_width - PI), "nine positive edges with fourteen outer sites need seven connectors")

    # A second angular price retains the joint restriction when one connector
    # has no active arc. The bounds concern the union of its positive spans.
    span_price = SPAN_PRICE
    span_bounds = ACTIVE_SPAN_CAPS
    span_boxes = 0
    for multiple, cap in enumerate(span_bounds):
        intervals = [((radius - 1).lo, inward_limit.hi)]
        while intervals:
            lo, hi = intervals.pop()
            t = Interval(lo, lo)
            if multiple:
                span = 2 * asin(2 / t)
            else:
                short = 2 * asin(1 / (t - 1))
                span = min((gap_max, short), key=lambda x: x.hi)
            span_boxes += 1
            if rim_angle_below(radius, inward_limit, hi - SCALE, rim_width + (cap - span) / span_price):
                continue
            if hi - lo < SCALE // 2**20:
                raise ArithmeticError("fourteen-arc connector-span charge unresolved")
            mid = (lo + hi) // 2
            intervals.extend(((lo, mid), (mid, hi)))
    allowance = span_price * (14 * rim_width - PI)
    for singles, multiples, free_span in (
        (5, 1, gap_max), (6, 0, repeat_max),  # eight edges, one pair and one inactive group
        (2, 3, gap_max), (3, 2, repeat_max),  # six groups, one inactive
        # The same first two inequalities cover a triple and six singles.
        (4, 1, repeat_max),                  # one pair outside a three-edge pocket
    ):
        positive(2 * PI - free_span - singles * span_bounds[0] - multiples * span_bounds[1] - allowance,
                 "nine-edge ring with fourteen active arcs: connector span charge")
    positive(2 * PI - repeat_max - 5 * gap_max, "a four-edge pocket cannot wind with the five other edges")
    print(f"fourteen-arc connector-span charge certified on {span_boxes} intervals")

    for h in range(1, 7):
        for j in range(1, min(h, 10 - h) + 1):
            if (h, j) == (6, 4):
                continue
            single = h - j
            if (single * gap_max + j * repeat_max).hi < (2 * PI).lo:
                continue
            loss = slope * 2 * PI - single * single_cap - j * repeat_cap
            positive(loss - (14 * rim_width - PI), "ten positive edges with few connector groups")

    fan_cap = rational(801, 1000)
    apex = rational(99, 50)
    positive((radius - 1) * (radius - 1) - 4 - apex * apex, "angular cone grows with small apex radius")
    for small_apex, cap in ((False, fan_cap), (True, PI - 10 * rim_width)):
        hi = (apex + 2).hi if small_apex else inward_limit.hi
        intervals = [((radius - 1).lo, hi)]
        while intervals:
            lo, hi = intervals.pop()
            t = Interval(lo, lo)
            if small_apex:
                cosine = (t * t + apex * apex - 4) / (2 * apex * t)
                sine_sq = 1 - cosine * cosine
                sine = sqrt(Interval(max(0, sine_sq.lo), max(0, sine_sq.hi)))
                reach = asin(sine)
            else:
                reach = asin(2 / t)
            if rim_angle_below(radius, inward_limit, hi - SCALE, cap - reach):
                continue
            if hi - lo < SCALE // 2**20:
                raise ArithmeticError("fourteen outer sites: fan angular capacity unresolved")
            mid = (lo + hi) // 2
            intervals.extend(((lo, mid), (mid, hi)))
    positive(PI - (fan_cap + 9 * rim_width), "no fan contains four rim gaps")
    positive(PI - (2 * fan_cap + 6 * rim_width), "two three-gap fans must intersect")
    positive(PI - (fan_cap + gap_max / 2 + 7 * rim_width), "two intersecting three-gap fans cannot be consecutive inner sites")
    positive(PI - (fan_cap + asin(1 / apex) + 7 * rim_width),
             "two intersecting three-gap fans cannot have a joining inner chord")
    print("fourteen outer sites: fans have at most three gaps, three gaps need apex radius above 1.98")

    @lru_cache(maxsize=None)
    def cap_faces(path):
        if len(path) < 3:
            return ((),)
        return tuple(
            ((path[0], path[i], path[-1]),) + left + right
            for i in range(1, len(path) - 1)
            for left in cap_faces(path[:i + 1])
            for right in cap_faces(path[i:])
        )

    def canonical(faces, repeats=()):
        forms = []
        for shift in range(size):
            for direction in (1, -1):
                index = [(direction * i + shift) % size for i in range(size)] + [core]
                transformed = tuple(sorted(tuple(sorted(index[i] for i in face)) for face in faces))
                chosen = tuple(sorted(index[i] for i in repeats))
                forms.append((transformed, chosen))
        return min(forms)

    for degree in range(4, 8):
        inner_types = set()
        labeled = 0
        for neighbors in combinations(range(size), degree):
            core_faces = []
            caps = []
            for a, b in zip(neighbors, neighbors[1:] + neighbors[:1]):
                path = tuple((a + i) % size for i in range((b - a) % size + 1))
                caps.append(cap_faces(path))
                core_faces.append((core, a, b))
            for parts in product(*caps):
                faces = tuple(core_faces) + tuple(face for cap in parts for face in cap)
                assert len(faces) == size
                labeled += 1
                inner_types.add(canonical(faces)[0])

        with_repeats = set()
        for faces in inner_types:
            ring_degrees = [set() for _ in range(size)]
            for face in faces:
                for vertex in face:
                    if vertex != core:
                        ring_degrees[vertex].update(other for other in face if other != vertex)
            eligible = [i for i, adjacent in enumerate(ring_degrees) if len(adjacent) >= 3]
            for count in range(min(1, len(eligible)) + 1):
                for repeats in combinations(eligible, count):
                    if any((i + 1) % size in repeats for i in repeats):
                        continue
                    with_repeats.add(canonical(faces, repeats))
        print(f"inner octagon degree {degree}: {labeled} labeled triangulations, "
              f"{len(inner_types)} dihedral types, {len(with_repeats)} types with connector repeats")

def check_fourteen_outer_eight_inner():
    radius = sqrt(6) + sqrt(3)
    inner_radius = radius - 2
    inward_limit = sqrt(radius * radius - 1)
    rim_width = asin(1 / radius)
    regular_gap = PI / 4
    intercept = rational(2939, 100000)
    slope = rational(4709, 10000)
    extra = rational(43, 10000)
    charge_start = rational(64, 100)
    gap_low, gap_high = rational(735, 1000), rational(835, 1000)
    gap_end = rational(953, 1000)

    @lru_cache(maxsize=None)
    def witness_radius(endpoint):
        sine, _ = sin_cos(Interval(endpoint, endpoint) / 2)
        return 1 / sine

    charge_radius = witness_radius(charge_start.lo)
    positive(charge_start - 2 * asin(1 / (radius - 1)), "distinct positive-charge witnesses")
    positive(radius - charge_radius, "positive-charge witnesses lie inside the target")
    positive(charge_radius + 1 - inward_limit, "zero charge for gaps <= .64")
    positive(gap_end - 2 * asin(1 / inner_radius), "witness gap domain")
    positive(-intercept - slope * (charge_start - regular_gap) - extra,
             "small gaps satisfy the strengthened deficit bound")

    ranges = [
        (charge_start.lo, gap_low.hi, extra),
        (gap_low.lo, gap_high.hi, rational(0)),
        (gap_high.lo, gap_end.hi, extra),
    ]
    visited = 0
    while ranges:
        d_lo, d_hi, bonus = ranges.pop()
        visited += 1
        q_upper = witness_radius(d_lo).hi
        if q_upper < inner_radius.lo:
            continue
        gap = Interval(d_lo, d_hi)
        bound = rim_width - intercept - slope * (gap - regular_gap) - bonus
        if rim_angle_below(radius, inward_limit, q_upper, bound):
            continue
        if d_hi - d_lo < SCALE // 2**22:
            raise ArithmeticError("eight-inner witness inequality unresolved")
        mid = (d_lo + d_hi) // 2
        ranges.extend(((d_lo, mid, bonus), (mid, d_hi, bonus)))

    residual = 14 * rim_width - PI - 8 * intercept
    positive(extra - residual, "any gap outside [.735,.835] exhausts the rim budget")
    positive(rational(41, 10000) - residual, "residual rim budget < .0041")

    q_max = witness_radius(gap_low.lo)
    q_min = witness_radius(gap_high.hi)
    positive(inward_limit - (1 + q_max), "every remaining witness has positive charge")
    positive(q_min - rational(245, 100), "witness radius > 2.45")
    derivative, _ = arc_derivatives(1 + q_max, radius)
    positive(derivative - rational(79, 1000), "rim-width derivative > .079")
    radial_loss = rational(52, 1000)
    positive(radial_loss * rational(79, 1000) - rational(41, 10000), "radial shortfall < .052")
    positive(q_min + 1 - radial_loss - rational(339, 100), "witness disk center radius > 3.39")
    phase_bound = rational(12, 100)
    _, cos_phase_bound = sin_cos(phase_bound)
    positive(1 - radial_loss / (rational(245, 100) * rational(339, 100)) - cos_phase_bound,
             "witness disk phase differs from midpoint by less than .12")
    positive(gap_low - 2 * (rim_width + phase_bound), "all eight assigned rim arcs are pairwise disjoint")
    print(f"14 outer, 8 inner reaching R-2 excluded: {visited} intervals, "
          f"residual rim budget {display(residual)}")

    connector_cone = 2 * asin(2 / (radius - 1))
    repeat_bonus = -(2 * intercept + slope * (connector_cone - 2 * regular_gap))
    positive(slope * regular_gap - intercept, "additional repeated edges only improve the bonus")
    positive(repeat_bonus - residual, "repeated connector impossible for eight positive interface arcs")
    q_floor = rational(12, 5)
    positive(q_min - radial_loss - q_floor, "actual exterior seam radius > 2.4")
    seam_phase = rational(1, 100)
    positive(seam_phase - radial_loss / (q_floor * sqrt(q_floor * q_floor - 1)),
             "actual exterior seam within .01 radians of the midpoint direction")
    connector_phase = rational(57, 500)
    _, cosine = sin_cos(connector_phase)
    positive(1 - radial_loss / (q_floor * rational(339, 100)) - cosine,
             "connector phase within .114 radians of the actual seam")
    total_phase = seam_phase + connector_phase
    positive(gap_low - 2 * (rim_width + total_phase), "eight interface rim arcs are disjoint")
    positive(total_phase * slope - rational(41, 10000), "backtracking reduces the total phase budget")
    positive(gap_low * slope - rational(41, 10000), "overlap shorter than either positive arc")
    print("14 outer disks require at least nine positive edges in every winding inner interface cycle")


def marked_full_distance_bounds(weight):
    # Closed-form maximizers when the rim vertex has distance 1 from its two sites.
    y1 = (sqrt(33 + 32 * weight) - 1) / 8
    x1 = sqrt(1 - y1 * y1)
    one = x1 * (1 + 2 * y1) - 2 * weight * asin(x1)
    z2 = (1 + sqrt(3 - 4 * weight)) / 4
    x2 = sqrt(z2)
    two = (2 + 4 * z2) * x2 * sqrt(1 - z2) - 4 * weight * asin(x2)
    return one, two


def rim_fan_at_angle(radius, theta, weight):
    sine, cosine = sin_cos(theta)
    q = radius * sine
    y = sqrt(1 - q * q)
    segment = radius * radius * (theta - sine * cosine)
    height = segment + q * y + 2 * weight * asin(q)
    slope = 2 * q * q + radius * cosine * (1 - 2 * q * q + 2 * weight) / y
    return q, height, slope


def rim_fan_at_mean(radius, m, weight):
    theta = PI / m
    q, height, slope = rim_fan_at_angle(radius, theta, weight)
    return q, height, height - theta * slope - weight * PI


def check_area_bounds():
    rows = (
        # m, test radius, lambda, D_lambda
        (14, rational(1701, 400), rational(0), rational(231, 500)),
        (15, rational(4277, 1000), rational(3, 25), rational(24271, 100000)),
        (16, rational(21347, 5000), rational(1, 5), rational(21, 200)),
    )
    a0 = 3 * sqrt(3) / 4
    positive(1 - rational(43, 200) * PI, "sin(g)/2 >= lambda*(pi-g) for g >= pi/2")
    positive(rational(1, 4) - PI / 14, "theta0 < 1/4")
    positive(
        rational(57, 100) * rational(31, 32) * rational(9, 16)
        - rational(7, 24) - rational(7, 512),
        "tangent-intercept monotonicity for q >= 3/4",
    )

    for m, radius, weight, increment in rows:
        max_one, max_two = marked_full_distance_bounds(weight)
        positive(a0 + increment - max_one, f"m={m}: one marked edge")
        positive(a0 + 2 * increment - max_two, f"m={m}: two marked edges")

        q, height, intercept_margin = rim_fan_at_mean(radius, m, weight)
        positive(q - rational(3, 4), f"m={m}: q > 3/4")
        positive(intercept_margin, f"m={m}: tangent at theta0 dominates the small-arc term")

        area_upper = (48 - m) * a0 + m * (increment + height) - 2 * weight * PI
        deficit = PI * radius * radius - area_upper
        positive(deficit, f"m={m}: strict area contradiction at the test radius")
        print(f"m={m}: test R={display(radius, 4)}, area deficit {display(deficit)}")


def check_fourteen_mark_mean():
    for radius, pairs in ((rational(8493, 2000), 0), (rational(1697, 400), 3)):
        theta = PI / 14
        sine, cosine = sin_cos(theta)
        q = radius * sine
        x = (radius * cosine - sqrt(1 - q * q)) * sine
        y_peak = (sqrt(33) - 1) / 8
        positive(x - sqrt(1 - y_peak * y_peak), "fourteen-mark mean exceeds the area maximum's half-chord")
        _, height, intercept = rim_fan_at_mean(radius, 14, rational(0))
        positive(intercept, "fourteen-mark mean tangent dominates the small-arc term")
        marked = x * (1 + 2 * sqrt(1 - x * x))
        deficit = PI * radius * radius - 20 * (3 * sqrt(3) / 4) - 14 * (height + marked) + rational(pairs, 20)
        positive(deficit, "fourteen-mark area contradiction with the polar mean")
        print(f"m=14: polar mean at R={display(radius, 4)}, area deficit {display(deficit)}")


def check_outer_face_loss(radius, weight, increment, outer_face_cost, triangle_bound=None):
    a0 = 3 * sqrt(3) / 4
    positive(a0 + 2 * increment - (2 - weight * PI) - outer_face_cost,
             "two-rim-edge ear pays for all its active sites")

    outer_floor = radius - 1
    outer_ceiling = sqrt(radius * radius - 1)
    span = 2 * asin(1 / outer_floor)
    positive(PI - 2 * span, "three outer sites with pairwise overlap lie in one short sector")
    extremes = (outer_floor, outer_ceiling)
    if triangle_bound is None:
        triangle_bound = rational(11, 10)
    boxes = [(0, span.hi, 0, SCALE)]
    visited = 0
    while boxes:
        d_lo, d_hi, s_lo, s_hi = boxes.pop()
        visited += 1
        d, s = Interval(d_lo, d_hi), Interval(s_lo, s_hi)
        sin_a, _ = sin_cos(d * s)
        sin_b, _ = sin_cos(d * (1 - s))
        sin_d, _ = sin_cos(d)
        upper = 0
        for r1 in extremes:
            for r2 in extremes:
                for r3 in extremes:
                    double_area = r1 * r2 * sin_a + r2 * r3 * sin_b - r1 * r3 * sin_d
                    upper = max(upper, abs(double_area.lo), abs(double_area.hi))
        if upper < 2 * triangle_bound.lo:
            continue
        if max(d_hi - d_lo, s_hi - s_lo) < SCALE // 2**20:
            raise ArithmeticError("three-outer triangle area unresolved")
        if d_hi - d_lo >= s_hi - s_lo:
            mid = (d_lo + d_hi) // 2
            boxes.extend(((d_lo, mid, s_lo, s_hi), (mid, d_hi, s_lo, s_hi)))
        else:
            mid = (s_lo + s_hi) // 2
            boxes.extend(((d_lo, d_hi, s_lo, mid), (d_lo, d_hi, mid, s_hi)))
    x = sqrt(rational(1, 2) - weight)
    max_mark = x * sqrt(1 - x * x) - 2 * weight * asin(x)
    positive(max_mark - increment, "one rim mark can only reduce this triangle deduction")
    positive(a0 - triangle_bound - (max_mark - increment) - outer_face_cost,
             "all-outer triangle with zero or one rim mark pays for all its active sites")
    return visited


def check_rim_angle_stability():
    radius = rational(21347, 5000)
    weight = rational(3, 25)
    increment = rational(24271, 100000)
    local_loss = rational(143, 10000)
    triangle_loss = 2 * local_loss
    a0 = 3 * sqrt(3) / 4
    theta0 = PI / 15
    q0, height, slope = rim_fan_at_angle(radius, theta0, weight)
    intercept = height - slope * theta0
    slack = 33 * a0 + 15 * (increment + height) - 2 * weight * PI - PI * radius * radius
    positive(15 * local_loss - slack, "rim-angle losses exceed the total area slack")
    one, two = marked_full_distance_bounds(weight)
    positive(a0 + increment - one, "rim-angle test one-marked bound")
    positive(a0 + 2 * increment - two, "rim-angle test two-marked bound")
    visited = check_outer_face_loss(radius, weight, increment, 3 * local_loss)

    theta_low, theta_high = rational(191, 1000), rational(28, 125)
    for theta in (theta_low, theta_high):
        _, h, _ = rim_fan_at_angle(radius, theta, weight)
        positive(intercept + slope * theta - h - local_loss, "rim fan angle range")
    small_q = sqrt(rational(1, 2))
    small_theta = asin(small_q / radius)
    small_segment = radius * radius * small_theta - small_q * sqrt(radius * radius - small_q * small_q)
    positive(intercept - weight * PI - local_loss, "short fan at theta=0")
    positive(intercept + slope * small_theta - small_segment - weight * PI - local_loss,
             "short fan at q=1/sqrt(2)")
    q_low, _, _ = rim_fan_at_angle(radius, theta_low, weight)
    positive(q_low - small_q, "rim fan endpoints have chord length > 1")
    beta_price = rational(1, 5)
    positive(q_low * q_low / 2 - weight - beta_price, "extra rim fan angle price")

    fan_cost = rational(23, 100)
    intervals = [(theta_low.lo, theta_high.hi)]
    while intervals:
        lo, hi = intervals.pop()
        theta = Interval(lo, hi)
        sine, _ = sin_cos(theta)
        q = radius * sine
        y = sqrt(1 - q * q)
        chord_x = sqrt(radius * radius - q * q)
        second = q * y + q * (
            (6 * q * q - 4 - slope) * radius * radius + slope + 2 * q * q - 4 * q * q * q * q
        ) / (4 * chord_x * chord_x * chord_x)
        if (second - 2 * fan_cost).lo > 0:
            continue
        if hi - lo < SCALE // 2**22:
            raise ArithmeticError("rim fan curvature bounds unresolved")
        mid = (lo + hi) // 2
        intervals.extend(((lo, mid), (mid, hi)))

    lower_a, upper_a = rational(77, 100), rational(1)
    for a in (lower_a, upper_a):
        sine, cosine = sin_cos(a)
        positive(one - (sine + 2 * sine * cosine - 2 * weight * a) - triangle_loss,
                 "marked base angle range")
    sine_low, cosine_low = sin_cos(lower_a)
    sine_high, cosine_high = sin_cos(upper_a)
    marked_cost = rational(54, 25)
    positive(sine_low * cosine_low - sine_high * cosine_high, "sin(2a) lower bound at the upper endpoint")
    positive(sine_low + 8 * sine_high * cosine_high - 2 * marked_cost,
             "quadratic marked base angle cost")
    _, cosine = sin_cos(rational(7, 20))
    positive(sine_low * sine_low * (1 - cosine) - triangle_loss, "marked endpoint angle imbalance < .175")
    delta_cost = rational(19, 20)
    positive(rational(197, 100) * sine_low * sine_low - delta_cost,
             "quadratic endpoint imbalance cost")
    extra_angle = rational(899, 1000)
    sine, cosine = sin_cos(extra_angle)
    positive(a0 - sine * (1 + cosine) - triangle_loss, "any extra unmarked angle is > .899")

    a_star = PI / 2 - asin((sqrt(33 + 32 * weight) - 1) / 8)
    mismatch = 3 * a_star - 2 * asin(q0)
    variance_factor = 4 * (rational(9, 4) / marked_cost + 1 / delta_cost) + 1 / fan_cost
    positive(sine_low * sine_low / 2 - beta_price, "shared lower price for the linear angle losses")
    positive(beta_price * beta_price * variance_factor - 4 * local_loss,
             "linear angle loss cannot increase the deviation bound")
    deviation = sqrt(local_loss * variance_factor)
    positive(mismatch - deviation, "two marked corners cannot close the angle sum")
    positive(extra_angle - mismatch - deviation, "an extra unmarked corner exceeds the angle sum")
    print(f"R={display(radius, 4)} excluded by rim angle stability; "
          f"annular triangle bound verified on {visited} boxes, deficit {display(15 * local_loss - slack)}")


def check_rim_angle_dual():
    radius = rational(213, 50)
    weight = rational(3, 25)
    increment = rational(24271, 100000)
    a0 = 3 * sqrt(3) / 4
    marked = a0 + increment
    theta0 = PI / 15
    _, height, slope = rim_fan_at_angle(radius, theta0, weight)
    intercept = height - slope * theta0
    slack = 33 * a0 + 15 * (increment + height) - 2 * weight * PI - PI * radius * radius
    e0, e1 = rational(217, 10000), rational(2971, 100000)
    d0, d1 = rational(275, 100000), rational(345, 100000)
    e0_star, e1_star = e0 + 2 * d0, e1 + 2 * d1
    positive(e1_star - e0_star, "a connector carries the stronger corner deduction")
    positive(7 * e0_star + 8 * e1_star - slack, "fifteen active arcs and at least eight seam faces exceed the area slack")

    one, two = marked_full_distance_bounds(weight)
    positive(marked - one, "dual angle test one-marked bound")
    positive(a0 + 2 * increment - two, "dual angle test two-marked bound")
    positive(intercept - weight * PI, "dual angle fan tangent dominates small-arc term")
    outer_boxes = check_outer_face_loss(radius, weight, increment,
                                       3 * e0_star + 4 * (e1_star - e0_star) + 6 * d1, rational(107, 100))

    @lru_cache(maxsize=None)
    def endpoint_asin(endpoint):
        if endpoint == SCALE:
            return PI / 2
        x = Interval(endpoint, endpoint)
        if endpoint >= 7 * SCALE // 10:
            return PI / 2 - asin(sqrt(1 - x * x))
        return asin(x)

    def closed_asin(x):
        return Interval(endpoint_asin(x.lo).lo, endpoint_asin(x.hi).hi)

    def check_maximum(lo, hi, bound, evaluate, label):
        pending = [(lo, hi)]
        visited = 0
        while pending:
            a, b = pending.pop()
            visited += 1
            if evaluate(Interval(a, b)).hi < bound.lo:
                continue
            if b - a < SCALE // 2**24:
                raise ArithmeticError(f"unresolved angle dual {label}: {display(Interval(a, b))}")
            mid = (a + b) // 2
            pending.extend(((a, mid), (mid, b)))
        return visited

    def fan(q, price):
        theta = closed_asin(q / radius)
        g = 2 * closed_asin(q)
        h = sqrt(1 - q * q)
        k = weight + price
        first = q * h + k * g
        second = k * PI
        return ((radius * radius - slope) * theta - q * sqrt(radius * radius - q * q) - intercept
                + Interval(max(first.lo, second.lo), max(first.hi, second.hi)))

    def marked_corner(x, price):
        a = closed_asin(x)
        base = x * (1 + 2 * sqrt(1 - x * x)) - 2 * weight * a
        abs_price = -price if price.hi < 0 else price
        # The maximized imbalance correction is nonincreasing in x.
        x_low = Interval(x.lo, x.lo)
        r = abs_price / x_low
        critical = (abs_price * closed_asin(r) - x_low * (1 - sqrt(1 - r * r))) / 2
        boundary = abs_price * PI / 2 - x_low
        return (price * (PI - 3 * a / 2) + (base - marked) / 2
                + Interval(max(critical.lo, boundary.lo), max(critical.hi, boundary.hi)))

    checked = 0
    p0, p1 = rational(9, 100), rational(-53, 500)
    t0, t1 = rational(17, 100), rational(-18348, 100000)
    for price, f, t, loss, cutoff in (
        (p0, rational(20378, 100000), t0, e0, rational(1, 5)),
        (p1, rational(-21996, 100000), t1, e1, rational(231, 500)),
    ):
        positive(weight + price, "nonnegative priced fan angle coefficient")
        checked += check_maximum(0, SCALE, f, lambda q: fan(q, price), "fan")
        a = closed_asin(cutoff)
        small = (cutoff * (1 + 2 * sqrt(1 - cutoff * cutoff)) - 2 * weight * a - marked) / 2
        positive(sqrt(1 - cutoff * cutoff) - (sqrt(33 + 32 * weight) - 1) / 8,
                 "marked area rises up to the cutoff")
        if price.lo > 0:
            small += price * 3 * PI / 2
        else:
            positive(cutoff * cutoff + 2 * price, "opposite angle optimizes at its minimum above cutoff")
        positive(t - small, "short marked edges cannot maximize the angle dual")
        checked += check_maximum(cutoff.lo, SCALE, t, lambda x: marked_corner(x, price), "marked corner")
        u = rational(0)
        if price.hi < 0:
            u = rational(-10882, 100000)
            positive(-u - (e1_star - e0_star), "each further seam corner pays its increment")
            positive(u - price * PI / 3, "extra corner past pi/3")
            limit = sqrt(3) / 2
            checked += check_maximum(0, limit.hi, u,
                                     lambda x: price * closed_asin(x) + x * (1 + sqrt(1 - x * x)) - a0,
                                     "extra corner")
        positive(2 * PI * price - f - 2 * t - u - loss, "local angle dual deduction")

    def marked_pair(x, price, diff):
        a = closed_asin(x)
        base = x * (1 + 2 * sqrt(1 - x * x)) - 2 * weight * a
        orient = rational(0)
        if diff.lo > 0:
            lower = Interval(x.lo, x.lo)
            r = diff / (2 * lower)
            critical = diff * closed_asin(r) / 2 - lower * (1 - sqrt(1 - r * r))
            boundary = diff * PI / 2 - 2 * lower
            orient = Interval(max(critical.lo, boundary.lo), max(critical.hi, boundary.hi))
        return price * (PI - 3 * a / 2) + base - marked + orient

    for price, diff, positive_price, cutoff, bound in (
        (2 * p0, rational(0), 2 * p0, rational(1, 5), 2 * (t0 - d0)),
        (p0 + p1, p0 - p1, p0, rational(1, 5), t0 + t1 - d0 - d1),
        (2 * p1, rational(0), rational(0), rational(231, 500), 2 * (t1 - d1)),
    ):
        positive(cutoff * cutoff + price, "opposite angle optimizes at its minimum for the marked pair")
        positive(2 * cutoff - diff, "marked-pair critical azimuth is defined above cutoff")
        positive(2 * weight + price, "rim angle excess only reduces the marked pair")
        small = cutoff * (1 + 2 * sqrt(1 - cutoff * cutoff)) - 2 * weight * closed_asin(cutoff) - marked
        positive(bound - small - positive_price * 3 * PI / 2, "short marked pairs cannot maximize the dual")
        checked += check_maximum(cutoff.lo, SCALE, bound, lambda x: marked_pair(x, price, diff), "marked pair")
    print(f"R={display(radius, 4)} excluded by angle dual: {outer_boxes} outer-face boxes, {checked} intervals, "
          f"deficit {display(7 * e0_star + 8 * e1_star - slack)}")


def check_outer_projection_clusters():
    radius = sqrt(6) + sqrt(3)
    cutoff = rational(21, 5)
    mu = rational(1, 5)
    increment = rational(427, 500)
    a0 = 3 * sqrt(3) / 4
    one, two = marked_full_distance_bounds(-mu)
    positive(increment - mu * PI, "zero-height rim triangle bound")
    positive(a0 + increment - one, "one marked edge with negative angle weight")
    positive(a0 + 2 * increment - two, "two marked edges with negative angle weight")

    outer_width = asin(1 / radius)
    v = asin(2 / radius)
    v_cutoff = asin(2 / cutoff)
    positive(PI - 10 * outer_width - v, "at least 11 cells outside a projection cluster")
    positive(PI - 11 * asin(1 / cutoff) - v_cutoff, "cluster impossible for R >= 4.2")
    positive(3 * PI - 14 * v, "the mean angle inside a cluster is smaller")

    def area_term(q):
        return q * sqrt(radius * radius - q * q) - q * sqrt(1 - q * q) + 2 * mu * asin(q)

    sine_outside, _ = sin_cos((PI - v) / 11)
    q_outside = radius * sine_outside
    outside_area = 11 * area_term(q_outside)
    for k in (3, 4, 5):
        sine_inside, _ = sin_cos(v_cutoff / k)
        inside_area = k * area_term(cutoff * sine_inside)
        m = 11 + k
        deficit = inside_area + outside_area - (48 - m) * a0 - m * increment - 2 * mu * PI
        positive(deficit, f"m={m}: clustered rim arcs violate the area bound")
        print(f"m={m}: overlapping polar projections span at most {k - 2} gaps, "
              f"cluster area deficit {display(deficit)}")

    sine, cosine = sin_cos(PI / 14)
    rim_center_min = radius * cosine - sqrt(1 - radius * radius * sine * sine)
    reverse_seam_lower = (rim_center_min * rim_center_min - 1) / radius
    positive(reverse_seam_lower - rational(305, 100), "average reverse seam radius > 3.05 for b=14")
    print("14-outer reverse-seam mean radius lower bound:", display(reverse_seam_lower))


def check_core_degree():
    radius0 = sqrt(6) + sqrt(3)
    a0 = 3 * sqrt(3) / 4
    def area_slack(m, radius, weight, increment):
        max_one, max_two = marked_full_distance_bounds(weight)
        positive(a0 + increment - max_one, "core test rim one-edge bound")
        positive(a0 + 2 * increment - max_two, "core test rim two-edge bound")
        q, height, intercept = rim_fan_at_mean(radius, m, weight)
        positive(q - rational(3, 4), "core test mean arc q > .75")
        positive(intercept, "core test rim tangent")
        return (48 - m) * a0 + m * (increment + height) - 2 * weight * PI - PI * radius * radius

    rows = (
        # m, weight, D_lambda, degree-3 rim-mark bound, R cutoffs for degrees 8, 7, 4, 5
        (14, rational(0), rational(231, 500), rational(1, 2), 4208, 4240, 4217, 4245),
        (15, rational(107, 500), rational(4009, 50000), None, 4225, 4265, 4236, 4270),
        (16, rational(9, 50), rational(139, 1000), rational(251, 1000), 4210, 4250, 4220, 4256),
    )
    sine_complement, cosine_complement = sin_cos(PI / 10)
    sine5, cosine5 = cosine_complement, sine_complement
    value5 = sine5 * (1 + cosine5)
    slope5 = 2 * cosine5 * cosine5 + cosine5 - 1
    positive(value5 + slope5 * 3 * PI / 5, "degree-5 angle tangent dominates at pi")
    for m, weight, increment, mark_bound, cutoff8, cutoff7, cutoff4, cutoff5 in rows:
        slack0 = area_slack(m, radius0, weight, increment)
        degree3_loss = 2 * a0
        if mark_bound is not None:
            if m == 16:
                x = sqrt(rational(1, 2) - weight)
                mark = x * sqrt(1 - x * x) - 2 * weight * asin(x)
                positive(mark_bound - mark, "degree-3 star rim-mark bound")
            positive(mark_bound - increment, "degree-3 rim mark correction")
            degree3_loss -= 3 * (mark_bound - increment)
        deficit3 = degree3_loss - slack0
        positive(deficit3, f"m={m}: degree-3 star is impossible")

        sine, cosine = sin_cos(3 * PI / 14)
        obtuse_loss = a0 - 1 + 14 * (a0 - sine * (1 + cosine))
        positive(obtuse_loss - slack0, f"m={m}: no right or obtuse angle at a degree-8 core")
        scope = "without rim marks" if mark_bound is None else "at an interior site"
        print(f"m={m}: degree-3 star {scope} excluded with area deficit {display(deficit3)}; "
              "degree-8 core angles are acute")

        for k, radius in ((9, radius0), (8, rational(cutoff8, 1000)), (7, rational(cutoff7, 1000))):
            sine, cosine = sin_cos(2 * PI / k)
            loss = 2 * k * (a0 - sine * (1 + cosine))
            deficit = loss - area_slack(m, radius, weight, increment)
            positive(deficit, f"m={m}, core degree >= {k}: area contradiction")
            print(f"m={m}, core degree >= {k} excluded from R={display(radius)}, "
                  f"area deficit {display(deficit)}")

        for k, cutoff, loss in ((4, cutoff4, 4 * a0 - 4), (5, cutoff5, 5 * (a0 - value5))):
            radius = rational(cutoff, 1000)
            deficit = loss - area_slack(m, radius, weight, increment)
            positive(deficit, f"m={m}, core degree {k}: area contradiction")
            print(f"m={m}, core degree {k} excluded from R={display(radius)}, "
                  f"area deficit {display(deficit)}")


def check_degree_eight_disjoint_clusters():
    # Fifteen active arcs, two disjoint three-site groups.
    radius = sqrt(6) + sqrt(3)
    cutoff = rational(169, 40)
    a0 = 3 * sqrt(3) / 4
    paired_loss = 16 * (a0 - (1 + sqrt(2)) / 2)
    increment = rational(231, 500)
    v0 = asin(2 / radius)
    positive(PI / 15 - v0 / 3, "cluster mean angle below the overall mean")
    sine1, _ = sin_cos(asin(2 / cutoff) / 3)
    sine2, _ = sin_cos((PI - 2 * v0) / 9)

    def area_term(q):
        return q * sqrt(radius * radius - q * q) - q * sqrt(1 - q * q)

    deficit = (6 * area_term(cutoff * sine1) + 9 * area_term(radius * sine2)
               - 33 * a0 - 15 * increment + paired_loss)
    positive(deficit, "degree-8 core with 15 active arcs and two disjoint clusters is impossible")
    print(f"m=15: degree-8 core with two disjoint 3-site clusters excluded, area deficit {display(deficit)}")


def check_fifteen_active_octagonal_star():
    radius = sqrt(6) + sqrt(3)
    width = asin(1 / radius)
    a0 = 3 * sqrt(3) / 4
    increment = rational(231, 500)
    charges = rational(141, 250)
    single_cap = rational(19, 125)
    pair_cap = rational(41, 250)
    price = rational(5, 4)
    degree4_loss = (19 * a0 - 4 - fan_price_max(price) - 14 * fan_price_max(price / 2)
                    - 2 * PI * price - (rational(1, 2) - increment))

    def area_term(theta):
        sine, cosine = sin_cos(theta)
        q = radius * sine
        return q * (radius * cosine - sqrt(1 - q * q))

    for count, inactive_cap, deduction, label in (
        (6, pair_cap, REPEAT_LOSS_ONE + REPEAT_ADJACENT_LOSS, "repeated connector"),
        (7, single_cap, degree4_loss, "inactive connector with four neighbors"),
    ):
        short_sum = count * width - (charges - inactive_cap)
        short_mean = short_sum / count
        long_mean = (PI - short_sum) / (15 - count)
        positive(long_mean - short_mean, "connector group has shorter mean arc")
        deficit = (count * area_term(short_mean) + (15 - count) * area_term(long_mean)
                   - 33 * a0 - 15 * increment + deduction)
        positive(deficit, f"15 active arcs: {label} impossible")
        print(f"16 outer, 15 active, degree-8 core: {label} excluded, area deficit {display(deficit)}")


def check_inactive_connector_outer_triangles():
    radius = sqrt(6) + sqrt(3)
    cutoff = rational(169, 40)
    outer_floor, outer_ceiling = rational(159, 50), rational(411, 100)
    inactive_ceiling = rational(343, 100)
    area_bound = rational(397, 200)
    floor_sq, ceiling_sq = outer_floor * outer_floor, outer_ceiling * outer_ceiling
    inactive_sq = inactive_ceiling * inactive_ceiling
    m0 = asin(1 / radius)
    inactive_arc = 16 * m0 - PI - rational(141, 250)
    sine, cosine = sin_cos(inactive_arc)
    t_cap = cutoff * cosine - sqrt(1 - cutoff * cutoff * sine * sine)
    positive(inactive_ceiling - t_cap, "inactive connector radius <= 3.43")
    positive(radius - 1 - outer_floor, "outer annulus lower endpoint")
    positive(ceiling_sq - cutoff * cutoff + 1, "outer annulus upper endpoint")

    def square(x):
        if x.lo >= 0 or x.hi <= 0:
            return x * x
        top = max(abs(x.lo), abs(x.hi))
        return Interval(0, ceil_div(top * top, SCALE))

    def support(vx, vy, norm_sq):
        # Highest ordinate in the unit disk centered at (vx, vy) and in the annulus.
        top = vy + 1
        candidates = []
        top_norm = norm_sq + 2 * vy + 1
        if top_norm.hi >= floor_sq.lo and top_norm.lo <= ceiling_sq.hi:
            candidates.append(top.hi)
        if (square(vx) + square(outer_ceiling - vy)).lo <= SCALE:
            candidates.append(outer_ceiling.hi)
        abs_x = Interval(0, max(abs(vx.lo), abs(vx.hi)))
        for edge in (outer_floor, outer_ceiling):
            lower = (edge - 1) * (edge - 1)
            upper = (edge + 1) * (edge + 1)
            a_lo, a_hi = max(norm_sq.lo, lower.lo), min(norm_sq.hi, upper.hi)
            if a_lo > a_hi:
                continue
            a = Interval(a_lo, a_hi)
            radicand = (upper - a) * (a - lower)
            height = sqrt(Interval(max(0, radicand.lo), max(0, radicand.hi)))
            y = ((edge * edge + a - 1) * vy + abs_x * height) / (2 * a)
            candidates.append(y.hi)
        if not candidates:
            return None
        return min(top.hi, outer_ceiling.hi, max(candidates))

    # Parameters: squared radial distances of the two base endpoints, and half the base length.
    z_min = area_bound / 4
    boxes = [(floor_sq.lo, inactive_sq.hi, floor_sq.lo, ceiling_sq.hi, z_min.lo, SCALE)]
    visited = 0
    while boxes:
        b_lo, b_hi, a_lo, a_hi, z_lo, z_hi = boxes.pop()
        visited += 1
        b2, a2, z = Interval(b_lo, b_hi), Interval(a_lo, a_hi), Interval(z_lo, z_hi)
        mx = (a2 - b2) / (4 * z)
        base_projection = mx - z
        perpendicular_sq = b2 - square(base_projection)
        if perpendicular_sq.hi < 0:
            continue
        my = sqrt(Interval(max(0, perpendicular_sq.lo), perpendicular_sq.hi))
        h = sqrt(1 - z * z)
        b = sqrt(b2)
        norm_min, norm_max = (b - 1) * (b - 1), (b + 1) * (b + 1)
        heights = []
        for side in (1, -1):
            vy = side * my + h
            norm_sq = b2 + 1 + 2 * z * base_projection + side * 2 * h * my
            norm_sq = Interval(max(norm_min.lo, norm_sq.lo), min(norm_max.hi, norm_sq.hi))
            if norm_sq.lo > norm_sq.hi:
                heights.append(None)
                break
            heights.append(support(mx, vy, norm_sq))
        if None in heights:
            continue
        total = sum(heights)
        if total <= 0 or (z * Interval(total, total)).hi < area_bound.lo:
            continue
        widths = (3 * (b_hi - b_lo), a_hi - a_lo, 6 * (z_hi - z_lo))
        axis = max(range(3), key=lambda i: widths[i])
        if widths[axis] < SCALE // 2**20:
            raise ArithmeticError("inactive-connector two-triangle bound unresolved")
        endpoints = (b_lo, b_hi, a_lo, a_hi, z_lo, z_hi)
        offset = 2 * axis
        mid = (endpoints[offset] + endpoints[offset + 1]) // 2
        boxes.append(endpoints[:offset + 1] + (mid,) + endpoints[offset + 2:])
        boxes.append(endpoints[:offset] + (mid,) + endpoints[offset + 1:])

    a0 = 3 * sqrt(3) / 4
    increment = rational(231, 500)
    paired_loss = 16 * (a0 - (1 + sqrt(2)) / 2)
    short_sum = 7 * m0 - rational(103, 250)

    def area_term(theta):
        sine, cosine = sin_cos(theta)
        q = radius * sine
        return q * (radius * cosine - sqrt(1 - q * q))

    additional_loss = 2 * a0 - area_bound - 2 * (rational(1, 2) - increment)
    deficit = (7 * area_term(short_sum / 7) + 8 * area_term((PI - short_sum) / 8)
               - 33 * a0 - 15 * increment + paired_loss + additional_loss)
    positive(deficit, "inactive connector and two all-outer triangles exceed the area budget")
    print(f"16 outer, 15 active, degree-8 core excluded on {visited} boxes, area deficit {display(deficit)}")


def check_sharp_octagonal_star(report_remaining=False):
    """Sharp fan and seam bounds for sixteen active outer sites."""
    radius = sqrt(6) + sqrt(3)
    radius_limit = rational(4271, 1000)
    radius_sq = radius * radius
    inward_sq = radius_sq - 1
    center_min = radius - 1
    root_two = sqrt(2)
    cosine_delta = sqrt(2 + root_two) / 2
    weight = root_two / 4
    slope = 1 + 2 * weight
    price = slope - radius_sq
    t_c, t_d = 2 + root_two, 4 * cosine_delta
    half_span = PI / 8
    regular_gap = PI / 4
    tilt = 1 / cosine_delta
    q_c, q_d = root_two / 2, cosine_delta
    f_c = -price * asin(q_c / radius) - t_c * q_c + weight * PI / 2
    f_d = -price * asin(q_d / radius) - t_d * q_d + 2 * weight * (PI / 2 - half_span)
    a0 = 3 * sqrt(3) / 4
    m1 = slope - weight * PI / 2
    _, m2 = marked_full_distance_bounds(weight)
    positive(2 * m1 - a0 - m2, "sharp two-marked-edge bound")
    positive((1 - 2 * weight) * radius_sq - rational(5, 4), "sharp fan concavity")
    positive(radius * (radius - t_d) - slope, "monotonic connector fan below t_D")
    u14, v14 = sin_cos(PI / 14)
    t14 = radius * v14 - sqrt(1 - radius_sq * u14 * u14)
    x14 = t14 * u14
    positive(x14 - root_two / 2, "mean mark exceeds the maximizing half chord")
    mark_loss = rational(11379, 10000)
    face14 = x14 * (1 + 2 * sqrt(1 - x14 * x14)) - 2 * weight * asin(x14)
    positive(14 * (m1 - face14) - mark_loss, "fourteen rim marks lose area from their polar gaps")
    u15, v15 = sin_cos(PI / 15)
    t15 = radius * v15 - sqrt(1 - radius_sq * u15 * u15)
    x15 = t15 * u15
    face15 = x15 * (1 + 2 * sqrt(1 - x15 * x15)) - 2 * weight * asin(x15)
    mark_loss_15 = rational(123, 1000)
    positive(x15 - root_two / 2, "the mean mark for fifteen arcs exceeds the maximizing half chord")
    positive(15 * (m1 - face15) - mark_loss_15, "fifteen rim marks lose area from their polar gaps")
    positive(2 * face15 - a0 - (2 - weight * PI) - rational(98, 1000),
             "a two-mark triangle saves a further 0.098 in the fifteen-arc tangent bound")

    boxes = [(radius.lo, radius_limit.hi, 0, SCALE // 2),
             (radius.lo, radius_limit.hi, SCALE // 2, SCALE)]
    visited = 0
    while boxes:
        r_lo, r_hi, q_lo, q_hi = boxes.pop()
        visited += 1
        big_r = Interval(r_lo, r_hi)
        q = Interval(q_lo, q_hi)
        limit = sqrt(big_r * big_r - 1)
        h = (1 - q * q) / (sqrt(big_r * big_r - q * q) + limit)
        if q_hi <= SCALE // 2:
            angle = atan_nonnegative(q / h)
        else:
            angle = PI / 2 - atan_nonnegative(h / q)
        normalized = -q * limit + 2 * weight * angle - price * asin(q / big_r)
        if normalized.hi < f_d.lo:
            continue
        if max(r_hi - r_lo, q_hi - q_lo) < SCALE // 2**20:
            raise ArithmeticError("sharp nonconnector fan bound unresolved")
        if 10 * (r_hi - r_lo) >= q_hi - q_lo:
            mid = (r_lo + r_hi) // 2
            boxes.extend(((r_lo, mid, q_lo, q_hi), (mid, r_hi, q_lo, q_hi)))
        else:
            mid = (q_lo + q_hi) // 2
            boxes.extend(((r_lo, r_hi, q_lo, mid), (r_lo, r_hi, mid, q_hi)))
    print(f"sharp nonconnector fan bound verified on {visited} boxes")

    joint_nonconnector = rational(823, 250)
    visited = 0
    intervals = [(0, SCALE // 2), (SCALE // 2, SCALE)]
    while intervals:
        lo, hi = intervals.pop()
        visited += 1
        q = Interval(lo, hi)
        h = sqrt(1 - q * q)
        angle = asin(q) if hi <= SCALE // 2 else PI / 2 - atan_nonnegative(h / q)
        upper = (10 - price) * asin(q / radius) - q * sqrt(radius_sq - q * q) + q * h + 2 * weight * angle
        if upper.hi < joint_nonconnector.lo:
            continue
        if hi - lo < SCALE // 2**23:
            raise ArithmeticError("joint nonconnector fan bound unresolved")
        mid = (lo + hi) // 2
        intervals.extend(((lo, mid), (mid, hi)))

    boxes = [(radius.lo, radius_limit.hi, 0, SCALE // 2),
             (radius.lo, radius_limit.hi, SCALE // 2, SCALE)]
    while boxes:
        r_lo, r_hi, q_lo, q_hi = boxes.pop()
        visited += 1
        big_r, q = Interval(r_lo, r_hi), Interval(q_lo, q_hi)
        limit = sqrt(big_r * big_r - 1)
        h = (1 - q * q) / (sqrt(big_r * big_r - q * q) + limit)
        angle = atan_nonnegative(q / h) if q_hi <= SCALE // 2 else PI / 2 - atan_nonnegative(h / q)
        upper = -q * limit + 2 * weight * angle + (10 - price) * asin(q / big_r)
        if upper.hi < joint_nonconnector.lo:
            continue
        if max(r_hi - r_lo, q_hi - q_lo) < SCALE // 2**20:
            raise ArithmeticError("joint nonconnector fan second endpoint unresolved")
        if 10 * (r_hi - r_lo) >= q_hi - q_lo:
            mid = (r_lo + r_hi) // 2
            boxes.extend(((r_lo, mid, q_lo, q_hi), (mid, r_hi, q_lo, q_hi)))
        else:
            mid = (q_lo + q_hi) // 2
            boxes.extend(((r_lo, r_hi, q_lo, mid), (r_lo, r_hi, mid, q_hi)))
    print(f"joint nonconnector fan bound verified on {visited} intervals and boxes")

    d_low, d_high = rational(72, 100), rational(85, 100)
    u_low, u_high = rational(4, 5), rational(6, 5)
    positive(regular_gap - d_low, "tangency angle inside Hessian rectangle")
    positive(d_high - regular_gap, "tangency angle inside Hessian rectangle")

    def hessian_box_ok(d, u):
        k, p = sin_cos(d / 2)
        sine, cosine = sin_cos(d)
        if (cosine - u * k).lo <= 0:
            return False
        radical = 1 - u * u * k * k
        if radical.lo <= 0:
            return False
        h = sqrt(radical)
        t = 1 + u * cosine + 2 * p * h
        if (t - center_min).lo <= 0 or (t_d - t).lo <= 0:
            return False
        t_height = (inward_sq - t * t) / (2 * t)
        radicand = 1 - t_height * t_height
        if t_height.lo <= 0 or radicand.lo <= 0:
            return False
        q = sqrt(radicand)
        fp = (2 * t_height * t_height - 1 + 2 * weight) / q
        fpp = -t_height * (3 + 2 * weight - 2 * t_height * t_height) * (t + t_height) / (t * q * q * q)

        h_cube = h * h * h
        hd = -u * u * sine / (4 * h)
        hu = -u * k * k / h
        hdd = -u * u * cosine / (4 * h) - u * u * u * u * sine * sine / (16 * h_cube)
        hdu = -u * sine / (2 * h) - u * u * u * k * k * sine / (4 * h_cube)
        huu = -k * k / h_cube
        gd = -u * sine - k * h + 2 * p * hd
        gu = cosine + 2 * p * hu
        gdd = -u * cosine - p * h / 2 - 2 * k * hd + 2 * p * hdd
        gdu = -sine - k * hu + 2 * p * hdu
        guu = 2 * p * huu

        dd = fpp * gd * gd + fp * gdd + tilt * k * (u - 1) / 4
        du = fpp * gd * gu + fp * gdu - tilt * p / 2
        uu = fpp * gu * gu + fp * guu
        return dd.hi < 0 and (dd * uu - du * du).lo > 0

    def certify_boxes(boxes, check, label):
        visited = 0
        while boxes:
            d_lo, d_hi, u_lo, u_hi = boxes.pop()
            visited += 1
            if check(d_lo, d_hi, u_lo, u_hi):
                continue
            if max(d_hi - d_lo, u_hi - u_lo) < SCALE // 2**22:
                raise ArithmeticError(f"{label} unresolved")
            if 4 * (d_hi - d_lo) >= u_hi - u_lo:
                mid = (d_lo + d_hi) // 2
                boxes.extend(((d_lo, mid, u_lo, u_hi), (mid, d_hi, u_lo, u_hi)))
            else:
                mid = (u_lo + u_hi) // 2
                boxes.extend(((d_lo, d_hi, u_lo, mid), (d_lo, d_hi, mid, u_hi)))
        print(f"{label} verified on {visited} boxes")

    certify_boxes(
        [(d_low.lo, d_high.hi, u_low.lo, u_high.hi)],
        lambda dl, dh, ul, uh: hessian_box_ok(Interval(dl, dh), Interval(ul, uh)),
        "sharp seam Hessian",
    )

    low, high = rational(2, 5), rational(953, 1000)
    low_sine, _ = sin_cos(low / 2)
    positive(f_c - root_two * (low - regular_gap) - tilt * low_sine - f_d,
             "sharp seam bound at gaps <= .4")

    def f_at_upper_radius(t_hi):
        if t_hi >= t_d.lo:
            return f_d
        t = Interval(max(t_hi, center_min.hi), max(t_hi, center_min.hi))
        h = (inward_sq - t * t) / (2 * t)
        q_sq = 1 - h * h
        q = sqrt(Interval(max(0, q_sq.lo), q_sq.hi))
        return -price * asin(q / radius) - t * q + 2 * weight * asin(q)

    def support_box_ok(dl, dh, ul, uh):
        q_hi = seam_q_upper(dl, uh)
        if q_hi < (radius - 2).lo:
            return True
        d, u = Interval(dl, dh), Interval(ul, uh)
        sine = Interval(seam_gap_trig(dl)[0].lo, seam_gap_trig(dh)[0].hi)
        plane = f_c - root_two * (d - regular_gap) + tilt * sine * (u - 1)
        return f_at_upper_radius(SCALE + q_hi).hi < plane.lo

    d_splits = (low.lo, d_low.lo, d_high.hi, high.hi)
    u_splits = (0, u_low.lo, u_high.hi, 2 * SCALE)
    boxes = [
        (dl, dh, ul, uh)
        for i, (dl, dh) in enumerate(zip(d_splits, d_splits[1:]))
        for j, (ul, uh) in enumerate(zip(u_splits, u_splits[1:]))
        if (i, j) != (1, 1)
    ]
    certify_boxes(boxes, support_box_ok, "sharp seam supporting plane outside the Hessian rectangle")
    print("16 outer, 16 active, degree-8 core excluded by the sharp area bound")

    mu = 10
    rim_width = asin(1 / radius)
    intercept, rim_slope, rim_tilt = rational(141, 2000), rational(23, 50), rational(59, 200)
    defect, defect_slope = rational(77, 1000), rational(31, 10)
    defect_angle = rational(17, 20)
    seam_constant = f_c + mu * (rim_width - intercept)
    seam_slope = root_two + mu * rim_slope
    seam_tilt = tilt + mu * rim_tilt
    total_slope = seam_slope + defect_slope

    def p_at_upper_radius(t_hi):
        if t_hi >= sqrt(inward_sq).lo:
            return rim_width
        t = Interval(max(t_hi, center_min.hi), max(t_hi, center_min.hi))
        h = (inward_sq - t * t) / (2 * t)
        q_sq = 1 - h * h
        q = sqrt(Interval(max(0, q_sq.lo), q_sq.hi))
        return asin(q / radius)

    def improved_plane(d, sine, u):
        return (seam_constant - seam_slope * (d - regular_gap) + seam_tilt * sine * (u - 1)
                - defect - defect_slope * (d - defect_angle))

    positive(improved_plane(low, low_sine, rational(0)) - f_d - mu * rim_width,
             "combined seam plane for gaps <= .4")

    def combined_box_ok(dl, dh, ul, uh):
        q_hi = seam_q_upper(dl, uh)
        if q_hi < (radius - 2).lo:
            return True
        d, u = Interval(dl, dh), Interval(ul, uh)
        sine = Interval(seam_gap_trig(dl)[0].lo, seam_gap_trig(dh)[0].hi)
        upper = f_at_upper_radius(SCALE + q_hi) + mu * p_at_upper_radius(SCALE + q_hi)
        return upper.hi < improved_plane(d, sine, u).lo

    certify_boxes([(low.lo, high.hi, 0, 2 * SCALE)], combined_box_ok,
                  "degree-7 combined seam plane")

    eta = rational(203, 200)
    a_star = (1 + root_two) / 2
    ordinary = (seam_constant + regular_gap * seam_slope - defect + defect_angle * defect_slope
                + 2 * fan_price_max(eta / 2))
    common = 2 * PI * (eta - total_slope) - 16 * a_star - 8 * f_c - mu * (PI - 8 * rim_width)
    normal, cap_two = rational(546, 100), rational(3215, 100)
    deficit = -common - 4 * ordinary - 2 * normal - cap_two
    positive(deficit, "degree-7 joint area and rim deficit given the two local bounds")
    print(f"degree-7 joint area and rim deficit given the two local bounds: {display(deficit)}")

    positive(radius - 3 - rational(118, 100), "local block radial lower endpoint")
    inactive_cost = 2 * a0 - m1
    positive(inactive_cost, "inactive outer arc area cost")
    positive(f_d + mu * rim_width - 2 * inactive_cost,
             "an inactive nonconnector saves more than two inactive arc costs")
    for gap_split, local_cost in (
        ("2+2", 2 * cap_two + 4 * normal),
        ("1+3", 2 * cap_two + 2 * normal + ordinary - rational(35, 100)),
        ("0+4", 2 * rational(27) + 2 * normal + 2 * ordinary),
    ):
        deficit = -common - local_cost
        positive(deficit, f"degree-6 isolated caps with split {gap_split}")
        if gap_split != "0+4":
            positive(deficit - inactive_cost, "one inactive connector still leaves a contradiction")
        print(f"degree-6 isolated caps, split {gap_split}: joint deficit {display(deficit)}")

    x = eta / 2
    low = 2 * sqrt(1 - x * x) + sqrt(3) - eta * (PI / 2 - asin(x))
    x = eta / 4
    middle = 4 * sqrt(1 - x * x) - eta * (PI / 2 - asin(x))
    high = 4 - eta * PI / 2
    group_area = Interval(max(low.lo, middle.lo, high.lo), max(low.hi, middle.hi, high.hi))
    p_x, p_y, p_rad = rational(1281, 1000), rational(-223, 1000), rational(-863, 250)
    positive(total_slope - (sqrt(p_x * p_x + p_y * p_y) + seam_tilt) / 2,
             "priced repeated group is increasing in its span at fixed outer radius")
    unpriced_limit, priced_limit = rational(1886, 100), rational(1331, 100)

    def repeated_group_cost(t, priced, active=True):
        sine = 2 / t
        cosine = sqrt(1 - sine * sine)
        span = 2 * asin(sine)
        score = f_at_upper_radius(t.hi) + mu * p_at_upper_radius(t.hi) if active else rational(0)
        if priced:
            x = p_x * cosine - p_y * sine - seam_tilt * sine
            y = p_x * sine + p_y * cosine
            norm_sq = x * x + y * y
            correction = sqrt(Interval(max(0, norm_sq.lo), norm_sq.hi)) + p_rad * (t - 2)
        else:
            correction = seam_tilt * sine
        return group_area + score + total_slope * span + correction

    visited = 0
    for priced, upper in ((False, unpriced_limit), (True, priced_limit)):
        intervals = [(center_min.lo, radius_limit.hi)]
        while intervals:
            lo, hi = intervals.pop()
            visited += 1
            if repeated_group_cost(Interval(lo, hi), priced).hi < upper.lo:
                continue
            if hi - lo < SCALE // 2**20:
                raise ArithmeticError("ordinary repeated group cost unresolved")
            mid = (lo + hi) // 2
            intervals.extend(((lo, mid), (mid, hi)))

    projection_group = rational(1855, 100)
    intervals = [(center_min.lo, radius_limit.hi)]
    while intervals:
        lo, hi = intervals.pop()
        t = Interval(lo, hi)
        g = 2 / t
        half = sqrt((1 - sqrt(1 - g * g)) / 2)
        tilt_bound = 2 * seam_tilt * (5 - radius) * half
        score = f_at_upper_radius(hi) + mu * p_at_upper_radius(hi)
        bound = group_area + score + 2 * total_slope * asin(g) + tilt_bound
        if bound.hi < projection_group.lo:
            continue
        if hi - lo < SCALE // 2**20:
            raise ArithmeticError("projected two-edge group cost unresolved")
        mid = (lo + hi) // 2
        intervals.extend(((lo, mid), (mid, hi)))

    extra_site = f_d + mu * rim_width
    unpriced_deficit = -common - extra_site - cap_two - 2 * normal - 2 * ordinary - unpriced_limit
    priced_deficit = -common - extra_site - cap_two - normal - 3 * ordinary - priced_limit
    positive(unpriced_deficit, "unpriced ordinary repeat with a degree-7 core")
    positive(priced_deficit, "priced ordinary repeat with a degree-7 core")
    inactive_limit = rational(1747, 100)
    inactive_span = 2 * asin(2 / center_min)
    positive(inactive_limit - group_area - total_slope * inactive_span - seam_tilt * 2 / center_min,
             "inactive unpriced repeated group")
    positive(unpriced_deficit + unpriced_limit - inactive_limit - inactive_cost,
             "m=15 with an inactive unpriced repeated group")
    priced_inactive = rational(12383, 1000)
    positive(priced_inactive - repeated_group_cost(center_min, True, False),
             "inactive priced repeated group")
    print(f"ordinary repeated groups checked on {visited} intervals, degree-7 joint deficits "
          f"{display(unpriced_deficit)} and {display(priced_deficit)}")

    joint_gain = extra_site - joint_nonconnector
    positive(joint_gain, "joint fan bound improves the independent budget")
    outer_limit = rational(104, 25)
    positive(outer_limit * outer_limit - (radius_limit * radius_limit - 1), "shared outer radial domain")
    mixed_normal = (rational(246, 100), rational(601, 200))
    mixed_cap = ((rational(318, 10), rational(30)), (rational(2982, 100), rational(285, 10)))
    for inactive in (0, 1):
        normal_bound, cap_bound = mixed_normal[inactive], mixed_cap[inactive][0]
        mixed_deficit = (-common - extra_site - 4 * ordinary - normal - normal_bound - cap_bound
                         + 9 * joint_gain - inactive * inactive_cost)
        positive(mixed_deficit, "ordinary edge and cap edge sharing one outer disk")
        print(f"mixed repeat joint deficit, shared disk inactive={bool(inactive)}: {display(mixed_deficit)}")
    positive(joint_nonconnector - 2 * inactive_cost,
             "a fifteen-outer octagon with one inactive connector has stricter budget")

    ordinary_inactive, normal_inactive = rational(513, 50), rational(1123, 250)
    priced_caps = (cap_two, rational(307, 10), rational(297, 10))
    mark_x = sqrt(rational(1, 2) - weight)
    mark_max = mark_x * sqrt(1 - mark_x * mark_x) - 2 * weight * asin(mark_x)
    positive(a0 - m1, "one mark reduces the sharp area budget")
    star_adjustment = 4 + mark_max - 2 * a0 - m1
    star_loss = min((ordinary_inactive - rational(932, 100) - star_adjustment,
                     normal_inactive - rational(358, 100) - star_adjustment), key=lambda x: x.lo)
    shared_star_loss = group_area - 2 * fan_price_max(eta) - 4 + 2 * a0
    pair_losses = tuple((2 - marks) * a0 + marks * (m1 - mark_max) - rational(1897, 1000)
                        for marks in range(3))
    pair_loss = min(pair_losses, key=lambda x: x.lo)
    pair_one_mark = min(pair_losses[:2], key=lambda x: x.lo)
    inactive_loss = min((star_loss, 2 * pair_loss, pair_one_mark), key=lambda x: x.lo)
    shared_inactive_loss = min((star_loss, shared_star_loss, pair_loss), key=lambda x: x.lo)
    seven_types = (
        ("distinct", 4, 2, 0, ((r, 0, bound) for r, bound in enumerate(priced_caps))),
        ("ordinary pair", 2, 2, 1, ((r, h, cap + group) for r, cap in enumerate(priced_caps)
                                   for h, group in enumerate((unpriced_limit, inactive_limit)))),
        ("priced ordinary pair", 3, 1, 1, ((r, h, cap + group) for r, cap in enumerate(priced_caps)
                                          for h, group in enumerate((priced_limit, priced_inactive)))),
        ("mixed pair", 4, 1, 1, ((r, h, mixed_cap[h][r] + mixed_normal[h]) for h in (0, 1) for r in (0, 1))),
    )
    for name, ordinary_count, normal_count, pair_count, caps in seven_types:
        minimum = None
        annular_cases = 0
        for cap_omissions, shared_inactive, cap_cost in caps:
            for a, b in product(range(ordinary_count + 1), range(normal_count + 1)):
                z = a + b + cap_omissions + shared_inactive
                if z > 2:
                    continue
                bound = (cap_cost + (ordinary_count - a) * ordinary + a * ordinary_inactive
                         + (normal_count - b) * normal + b * normal_inactive)
                for w in range(3 - z):
                    deficit = (-common - bound + 8 * joint_gain + (w - pair_count) * joint_nonconnector
                               - (z + w) * inactive_cost)
                    if deficit.lo <= 0 and z == 2 and w == 0 and cap_omissions == 0:
                        if name in ("distinct", "mixed pair") and shared_inactive == 0 and a + b == 2:
                            deficit += inactive_loss
                            annular_cases += 1
                        elif name == "priced ordinary pair" and shared_inactive == 1 and b == 1:
                            deficit += shared_inactive_loss
                            annular_cases += 1
                    positive(deficit, f"degree-7 {name}, m={16-z-w}, w={w}, omissions={(a,b,cap_omissions,shared_inactive)}")
                    if minimum is None or deficit.lo < minimum.lo:
                        minimum = deficit
        print(f"degree-7 {name}: {annular_cases} cases using the annulus correction, joint deficit {display(minimum)}")

    positive(rational(203, 100) - 2 * asin(1 / (radius - 3)), "root cap angular domain")
    cap_bounds = {
        1: (ordinary, ordinary_inactive),
        2: tuple(rational(v, 100) for v in (2147, 2020, 1912)),
        3: (*tuple(rational(v, 100) for v in (3042, 3010, 2919)), rational(2066, 100) + 4 * a0),
    }
    for length in (4, 5):
        root_bound = rational(2066, 100) + (2 * length - 2) * a0
        cap_bounds[length] = tuple(root_bound + (length - i) * joint_nonconnector for i in range(4))

    # The matching C++ modes use the same limits. Each row counts the other
    # inactive connectors in that cap, excluding the shared connector.
    ordinary_shared_cap = {
        2: ((2632, 2515), (2490, 2370)),
        3: ((3599, 3533, 3200), (3482, 3418, 3086)),
    }
    symmetric_shared_cap = {
        2: ((1972, 1851), (1922, 1814)),
        3: ((3037, 2974, 2644), (3020, 2957, 2630)),
    }
    inside_shared_cap = (2715, 2650, 2588)

    for degree in (4, 5, 6):
        minimum = None
        checked = 0
        for lengths in product(range(1, 10 - degree), repeat=degree):
            if tuple(sorted(lengths)) != lengths or sum(lengths) != 8:
                continue
            for omissions in product(*(range(len(cap_bounds[l])) for l in lengths)):
                z = sum(omissions)
                if z > 2:
                    continue
                bound = sum(cap_bounds[l][i] for l, i in zip(lengths, omissions))
                for w in range(3 - z):
                    deficit = (-common - bound + (8 - w) * joint_gain
                               - (z + w) * inactive_cost + w * extra_site)
                    positive(deficit, f"distinct connectors with degree {degree}, lengths {lengths}, omissions {omissions}")
                    checked += 1
                    if minimum is None or deficit.lo < minimum.lo:
                        minimum = deficit
        print(f"distinct connectors, degree {degree}: {checked} partition cases, joint deficit {display(minimum)}")

    for degree in (4, 5, 6):
        counts = {(m, w): [0, 0] for m in (14, 15, 16) for w in range(17 - m)}
        transfer_min = None
        minimum = None
        for lengths in product(range(1, 10 - degree), repeat=degree):
            if sum(lengths) != 8 or lengths != min(lengths[i:] + lengths[:i] for i in range(degree)):
                continue
            owner = tuple(i for i, length in enumerate(lengths) for _ in range(length))
            for first in range(8):
                second = (first + 1) % 8
                i, j = owner[first], owner[second]
                if i == j and lengths[i] == 2:
                    # The apex of a triangular cap has inner degree two.
                    continue
                groups = [(first, second)] + [(e,) for e in range(8) if e not in (first, second)]
                ordinary_pair = lengths[i] == lengths[j] == 1
                for m, w in counts:
                    for inactive in combinations(range(7), 16 - m - w):
                        removed = [e for g in inactive for e in groups[g]]
                        shared_inactive = 0 in inactive
                        choices = [removed] if shared_inactive else [removed + [first], removed + [second]]
                        bounds = []
                        for omitted in choices:
                            by_block = [0] * degree
                            for e in omitted:
                                by_block[owner[e]] += 1
                            cost = sum(cap_bounds[length][r] for k, (length, r) in
                                       enumerate(zip(lengths, by_block)) if not ordinary_pair or k not in (i, j))
                            if ordinary_pair:
                                cost += inactive_limit if shared_inactive else unpriced_limit
                            bounds.append(cost)
                        by_block = [0] * degree
                        for e in removed:
                            if e != first and e != second:
                                by_block[owner[e]] += 1
                        left, right = lengths[i], lengths[j]
                        pair_bound = None
                        if i == j and left == 3:
                            pair_bound = rational(inside_shared_cap[by_block[i] + shared_inactive], 100)
                        elif min(left, right) == 1 and max(left, right) in ordinary_shared_cap:
                            cap_index = j if left == 1 else i
                            cap_limit = ordinary_shared_cap[lengths[cap_index]][shared_inactive][by_block[cap_index]]
                            pair_bound = mixed_normal[shared_inactive] + rational(cap_limit, 100)
                        elif i != j and left in symmetric_shared_cap and right in symmetric_shared_cap:
                            left_limit = symmetric_shared_cap[left][shared_inactive][by_block[i]]
                            right_limit = symmetric_shared_cap[right][shared_inactive][by_block[j]]
                            pair_bound = rational(left_limit + right_limit, 100)
                        if pair_bound is not None:
                            bounds.append(pair_bound + sum(cap_bounds[length][r] for k, (length, r) in
                                                           enumerate(zip(lengths, by_block)) if k not in (i, j)))
                        bound = min(bounds, key=lambda cost: cost.hi)
                        deficit = (-common - bound + (8 - w) * joint_gain - (16 - m) * inactive_cost
                                   + w * extra_site - joint_nonconnector)
                        if m >= 15:
                            transfer = deficit + joint_nonconnector - inactive_cost
                            positive(transfer, "fifteen outer sites with a nine-vertex inner component")
                            if transfer_min is None or transfer.lo < transfer_min.lo:
                                transfer_min = transfer
                        counts[m, w][0] += 1
                        positive(deficit, f"shared connector, degree {degree}, {lengths}, {first}, m={m}, w={w}")
                        counts[m, w][1] += 1
                        if minimum is None or deficit.lo < minimum.lo:
                            minimum = deficit
        print(f"one shared connector, degree {degree}, (m, w): excluded/checked "
              + ", ".join(f"{key}: {good}/{total}" for key, (total, good) in counts.items())
              + f", joint deficit {display(minimum)}")
        print(f"fifteen outer sites, degree {degree}, nine-vertex inner component, one shared connector: "
              f"joint deficit {display(transfer_min)}")

    cap_bounds[6] = tuple(rational(2066, 100) + 10 * a0 + (6 - i) * joint_nonconnector for i in range(5))
    for length in (4, 5):
        cap_bounds[length] += (rational(2066, 100) + (2 * length - 2) * a0 + (length - 4) * joint_nonconnector,)
    for degree in (4, 5):
        proven = []
        for lengths in product(range(1, 11 - degree), repeat=degree):
            if tuple(sorted(lengths)) != lengths or sum(lengths) != 9:
                continue
            for repeats in range(4):
                minimum = None
                for omissions in product(*(range(len(cap_bounds[l])) for l in lengths)):
                    z = sum(omissions) - repeats
                    if not 0 <= z <= 1:
                        continue
                    cost = sum(cap_bounds[l][i] for l, i in zip(lengths, omissions))
                    for w in range(2 - z):
                        deficit = (-common - cost + 8 * joint_gain + (2 - repeats + w) * joint_nonconnector
                                   - (1 + z + w) * inactive_cost + 2 * a0)
                        if minimum is None or deficit.lo < minimum.lo:
                            minimum = deficit
                if degree == 4 and repeats == 0:
                    positive(minimum, "nine positive edges, distinct connectors, degree 4")
                if minimum.lo > 0:
                    proven.append((lengths, repeats))
        print(f"nine positive edges, fifteen outer sites, degree {degree}, excluded (lengths, repeat omissions): {proven}")

    for degree in (4, 5, 6):
        proven = []
        for lengths in product(range(1, 11 - degree), repeat=degree):
            if tuple(sorted(lengths)) != lengths or sum(lengths) != 9:
                continue
            for repeats in range(3):
                minimum = None
                for omissions in product(*(range(len(cap_bounds[l])) for l in lengths)):
                    if sum(omissions) != repeats:
                        continue
                    cost = sum(cap_bounds[l][i] for l, i in zip(lengths, omissions))
                    deficit = (-common - cost + 8 * joint_gain + (3 - repeats) * joint_nonconnector
                               - 2 * inactive_cost + 2 * a0)
                    if minimum is None or deficit.lo < minimum.lo:
                        minimum = deficit
                if repeats == 0:
                    positive(minimum, "nine positive edges, fourteen distinct outer sites, degree at most six")
                if minimum.lo > 0:
                    proven.append((lengths, repeats))
        print(f"nine positive edges, fourteen outer sites, degree {degree}, excluded (lengths, repeat omissions): {proven}")

    cap_bounds[7] = (rational(2066, 100) + 12 * a0 + 7 * joint_nonconnector,)
    joined = {
        1: {1: rational(1077, 100), 2: rational(1077, 100), 3: rational(936, 100)},
        2: {2: rational(199, 10), 5: rational(221, 10)},
        3: {6: rational(298, 10)},
    }
    for outer, size in ((14, 9), (14, 10), (15, 9)):
        available = 2 * size - outer
        join_sets = [sum(1 << i for i in indices) for indices in combinations(range(size), available)]
        budget = (-common + 8 * joint_gain + (size + 8 - outer) * joint_nonconnector
                  - (16 - outer) * inactive_cost + (2 * size - 16) * a0)
        for degree in (4, 5, 6, 7, 8):
            checked = 0
            proved = 0
            minimum = None
            for lengths in product(range(1, size - degree + 2), repeat=degree):
                if sum(lengths) != size or lengths != min(lengths[i:] + lengths[:i] for i in range(degree)):
                    continue
                # For each set of charged joins, compute a cost once. A join
                # not used by this bound is handled by selecting a subset.
                costs = {}
                for mask in range(1 << size):
                    if mask.bit_count() > available:
                        continue
                    offset = 0
                    cost = rational(0)
                    for length in lengths:
                        local = sum(((mask >> ((offset + i) % size)) & 1) << i for i in range(length + 1))
                        if local == 0:
                            cost += cap_bounds[length][0]
                        elif local in joined.get(length, {}):
                            cost += joined[length][local]
                        else:
                            break
                        offset += length
                    else:
                        costs[mask] = cost
                for mask in join_sets:
                    best = costs[0]
                    subset = mask
                    while subset:
                        option = costs.get(subset)
                        if option is not None and option.hi < best.hi:
                            best = option
                        subset = (subset - 1) & mask
                    deficit = budget - best
                    checked += 1
                    if deficit.lo > 0:
                        proved += 1
                    if outer == 14 and size == 9:
                        positive(deficit, f"nine distinct connectors, joined positions {mask}, lengths {lengths}")
                    if minimum is None or deficit.lo < minimum.lo:
                        minimum = deficit
            print(f"joined arcs, outer={outer}, ring={size}, degree={degree}: {proved}/{checked} excluded, "
                  f"smallest deficit {display(minimum)}")

    ten_prices = 2 * PI * (1 - 4 - (eta - total_slope))
    ten_budget = (-common - ten_prices + 8 * joint_gain + 4 * joint_nonconnector
                  - 2 * inactive_cost + 4 * a0 + mark_loss)
    ten_blocks = {1: rational(735, 100), 2: rational(1476, 100)}
    for length in range(3, 8):
        ten_blocks[length] = rational(216, 10) + (length - 3) * (2 * a0 + joint_nonconnector)
    positive(4 - seam_tilt / 2, "negative cap spans have no positive angular charge")
    positive(ten_blocks[1] - rational(54, 10) - joint_nonconnector / 2,
             "ordinary shared endpoint pays for its share of a repeat")
    positive(ten_blocks[1] - rational(351, 100) - joint_nonconnector,
             "intermediate ordinary shared edge pays for a repeat")
    positive(ten_blocks[2] - rational(1146, 100) - joint_nonconnector,
             "triangular cap with two shared endpoints pays for both shares")
    cap_end_cost = rational(66, 5) + joint_nonconnector / 2 - ten_blocks[2]
    mark_pair_loss = rational(7, 100)
    root_cross = (ten_blocks[3], rational(225, 10), rational(2355, 100))
    end_phase = rational(5, 2) * asin(2 / center_min) + (extra_site - joint_nonconnector) / 2
    for ends, bound in enumerate(root_cross):
        positive(bound - 3 * (2 * a0 + joint_nonconnector) - ends * end_phase,
                 "nonpositive longer cap span with shared ends")

    root_side = {
        (0, 0): rational(2103, 100), (0, 1): rational(2223, 100), (1, 1): rational(2304, 100),
        (0, 2): rational(2202, 100), (1, 2): rational(2282, 100), (2, 2): rational(2260, 100),
    }
    rim_priced_quad = {
        (0, 0): rational(2032, 100), (0, 1): rational(2092, 100), (1, 1): rational(2155, 100),
        (0, 2): rational(2087, 100), (1, 2): rational(2157, 100), (2, 2): rational(2169, 100),
    }
    strict_quad = rational(2251, 100)
    positive(strict_quad - 3 * (2 * a0 + joint_nonconnector) - 2 * end_phase,
             "nonpositive span of a strict quadrilateral")
    for charge, bound in root_side.items():
        positive(bound - 3 * (2 * a0 + joint_nonconnector) - sum(c != 0 for c in charge) * end_phase,
                 "nonpositive longer cap span with the side-area bounds")
        positive(rim_priced_quad[charge] - 3 * (2 * a0 + joint_nonconnector) - charge.count(1) * end_phase
                 - charge.count(2) * (extra_site - joint_nonconnector) / 2,
                 "nonpositive span of a rim-priced quadrilateral")

    reverse_short = (rational(1255, 100), rational(1192, 100) + joint_nonconnector / 2, 10 + joint_nonconnector)

    def shared_ten_cost(lengths, starts, neutral=None, reverse_block=-1, strict=False, rim_priced=False):
        size = sum(lengths)
        i = 0
        cost = rational(0)
        for block, length in enumerate(lengths):
            positions = ((i - 1) % size, (i + length - 1) % size)
            ends = sum(p in starts for p in positions)
            if length == 1:
                cost += (ten_blocks[1], rational(54, 10) + joint_nonconnector / 2,
                         rational(351, 100) + joint_nonconnector)[ends]
            elif length == 2:
                if i in starts:
                    return None
                if block == reverse_block:
                    cost += reverse_short[ends]
                else:
                    cost += (ten_blocks[2], rational(66, 5) + joint_nonconnector / 2,
                             rational(1146, 100) + joint_nonconnector)[ends]
            else:
                if length == 3 and i in starts and i + 1 in starts:
                    return None
                if block == reverse_block and length == 3 and not ends and all(p not in starts for p in range(i, i + 2)):
                    cost += rational(2084, 100)
                elif neutral is None:
                    cost += root_cross[ends]
                else:
                    charge = tuple(sorted(2 if p in neutral else 1 if p in starts else 0 for p in positions))
                    if rim_priced:
                        cost += rim_priced_quad[charge]
                    elif strict and length == 3 and charge == (1, 1):
                        cost += strict_quad
                    else:
                        cost += root_side[charge]
                cost += (length - 3) * (2 * a0 + joint_nonconnector)
            i += length
        return cost

    for length in range(2, 8):
        positive(ten_blocks[length] - length * (2 * a0 + joint_nonconnector), "nonpositive cap span bound")
    def valid_rim_charges(lengths, starts, neutral):
        if max(lengths) > 3:
            return False
        # Twice the fraction of the disk's rim deficit assigned to this end.
        charges = {}
        offset = 0
        size = sum(lengths)
        for length in lengths:
            if length == 3:
                for edge, cut in ((offset, (offset - 1) % size), (offset + 2, offset + 2)):
                    group = edge
                    while (group - 1) % size in starts:
                        group = (group - 1) % size
                    charges[group] = charges.get(group, 0) + (1 if cut in neutral else 2)
            offset += length
        return all(count <= 2 for count in charges.values())

    for degree in range(4, 9):
        minimum = None
        checked = 0
        for lengths in product(range(1, 12 - degree), repeat=degree):
            if tuple(sorted(lengths)) != lengths or sum(lengths) != 10:
                continue
            deficit = ten_budget - sum(ten_blocks[length] for length in lengths)
            positive(deficit, f"ten distinct connectors, lengths={lengths}")
            for repeats in range(1, 5):
                half_caps = min(lengths.count(2), 2 * repeats)
                positive(deficit + (4 + repeats) * mark_pair_loss - half_caps * cap_end_cost,
                         f"ten-edge ring, no longer block crossed, lengths={lengths}, repeats={repeats}")
            checked += 1
            if minimum is None or deficit.lo < minimum.lo:
                minimum = deficit
        print(f"ten distinct connectors, degree {degree}: {checked} partitions, deficit {display(minimum)}")

    gap_cap, root_cap = rational(953, 1000), rational(203, 100)
    ten_hard = []
    for degree in range(4, 9):
        checked = excluded = 0
        improved = [0, 0]
        for lengths in product(range(1, 12 - degree), repeat=degree):
            if sum(lengths) != 10 or lengths != min(lengths[i:] + lengths[:i] for i in range(degree)):
                continue
            if sum(min(length * gap_cap.hi, root_cap.hi) for length in lengths) < (2 * PI).lo:
                continue
            long = tuple(length >= 3 for length in lengths for _ in range(length))
            owner = tuple(i for i, length in enumerate(lengths) for _ in range(length))
            for repeats in range(1, 5):
                budget = ten_budget + (4 + repeats) * mark_pair_loss
                if repeats == 4:
                    budget += 2 * mark_pair_loss
                for positions in combinations(range(10), repeats):
                    starts = set(positions)
                    if any((p + 1) % 10 in starts and (repeats == 4 or (p + 2) % 10 in starts) for p in starts):
                        continue
                    neutral = {p for p in starts if owner[p] != owner[(p + 1) % 10] and long[p] and long[(p + 1) % 10]
                               and ((p - 1) % 10 not in starts or long[(p - 1) % 10])
                               and ((p + 1) % 10 not in starts or long[(p + 2) % 10])}
                    cost = shared_ten_cost(lengths, starts, neutral)
                    if cost is None:
                        continue
                    checked += 1
                    if (budget - cost).lo <= 0:
                        ten_hard.append((lengths, starts, neutral, budget))
                        cost = shared_ten_cost(lengths, starts, neutral, strict=True)
                        if (budget - cost).lo > 0:
                            improved[0] += 1
                        elif valid_rim_charges(lengths, starts, neutral):
                            cost = shared_ten_cost(lengths, starts, neutral, rim_priced=True) + 6 * (14 * rim_width - PI)
                            improved[1] += 1
                    positive(budget - cost, f"ten-edge ring, degree {degree}, lengths {lengths}, shares {positions}")
                    excluded += 1
        print(f"ten-edge ring with sharing, degree {degree}: {excluded}/{checked} excluded; "
              f"additional exclusions by strict shape and rim deficit {improved}")

    fat_budget = -common - ten_prices + 8 * joint_gain + joint_nonconnector - inactive_cost
    fat = rational(1471, 100)
    for label, repeats, ordinary_cost, fat_cost in (
        ("distinct", 0, 6 * ten_blocks[1], fat),
        ("ordinary repeat", 1, 4 * ten_blocks[1] + 2 * rational(54, 10), fat),
        ("endpoint repeat", 1, 5 * ten_blocks[1] + rational(54, 10), rational(1285, 100)),
        ("inside repeat", 1, 6 * ten_blocks[1], rational(1065, 100)),
    ):
        for inactive in (0, 1):
            deficit = (fat_budget - repeats * joint_nonconnector - ordinary_cost - fat_cost
                       - inactive * (inactive_cost - mark_loss))
            positive(deficit, f"adjacent two cores, degree 8, {label}, inactive={inactive}")
            print(f"adjacent two cores, degree 8, {label}, inactive={inactive}: {display(deficit)}")

    ten_omitted = {
        1: (ten_blocks[1], rational(567, 100)),
        2: (ten_blocks[2], rational(129, 10), rational(1133, 100)),
    }
    for length in range(3, 7):
        ten_omitted[length] = tuple(rational(v, 100) + (length - 3) * (2 * a0 + joint_nonconnector)
                                    for v in (2160, 2031, 1928, 1599))

    fat_omitted = (fat, rational(1295, 100), rational(112, 10))
    for degree in range(4, 9):
        octagon_cases = {(m, repeat): [0, 0] for m in (14, 15) for repeat in (False, True)}
        for rest in product(range(1, 10 - degree), repeat=degree - 2):
            if sum(rest) != 6:
                continue
            if sum(min(l * gap_cap.hi, root_cap.hi) for l in rest) + 2 * gap_cap.hi < (2 * PI).lo:
                continue
            lengths = (2,) + rest
            owner = tuple(i for i, length in enumerate(lengths) for _ in range(length))
            for shared in (-1, *range(8)):
                pair = () if shared < 0 else (shared, (shared + 1) % 8)
                if pair and owner[pair[0]] == owner[pair[1]] != 0 and lengths[owner[pair[0]]] == 2:
                    continue
                connectors = ([(e,) for e in range(8) if e not in pair] + ([pair] if pair else []))
                for m in (14, 15):
                    for inactive in ((), *connectors) if m == 14 else ((),):
                        budget = (fat_budget + mark_loss_15 if m == 15 else
                                  fat_budget - inactive_cost + mark_loss + (joint_nonconnector if not inactive else 0))
                        costs = []
                        if not pair or inactive == pair:
                            omissions = (inactive,)
                        else:
                            omissions = tuple(inactive + (e,) for e in pair)
                        for omit in omissions:
                            counts = [sum(owner[e] == j for e in omit) for j in range(len(lengths))]
                            cost = fat_omitted[counts[0]] + sum(ten_omitted[l][n] for l, n in zip(rest, counts[1:]))
                            if pair and inactive == pair:
                                a, b = (owner[e] for e in pair)
                                if a == b != 0 and lengths[a] == 3:
                                    cost += rational(171, 10) - ten_omitted[3][2]
                                elif a != b and lengths[a] == lengths[b] == 1:
                                    cost += 2 * rational(351, 100) + rational(5, 2) * 2 * asin(2 / center_min) - 2 * ten_omitted[1][1]
                            costs.append(cost + (joint_nonconnector if pair else 0))
                        if pair and inactive != pair:
                            # Split the score and charge the two endpoint phases.
                            # Keeping a distinct inactive score in a touched block is safe.
                            i = 2
                            if shared == 0:
                                cost = rational(1065, 100) + joint_nonconnector
                            elif shared in (1, 7):
                                cost = rational(1285, 100) + joint_nonconnector / 2
                            else:
                                cost = fat_omitted[sum(e < 2 for e in inactive)]
                            for j, length in enumerate(rest, 1):
                                ends = int(shared in ((i - 1) % 8, (i + length - 1) % 8))
                                if ends:
                                    cost += (rational(54, 10) + joint_nonconnector / 2 if length == 1 else
                                             rational(66, 5) + joint_nonconnector / 2 if length == 2 else root_side[0, 1])
                                elif owner[shared] == owner[(shared + 1) % 8] == j:
                                    cost += ten_blocks[length]
                                else:
                                    cost += ten_omitted[length][sum(owner[e] == j for e in inactive)]
                                i += length
                            costs.append(cost)
                        deficit = max((budget - cost for cost in costs), key=lambda d: d.lo)
                        tally = octagon_cases[m, bool(pair)]
                        tally[0] += 1
                        if deficit.lo > 0:
                            tally[1] += 1
                        positive(deficit, f"two-core octagon, length two, parts {rest}, shared {pair}, inactive {inactive}")
        print(f"two-core octagon, length two, degree {degree}, excluded by (m, sharing) "
              f"{[(k, x[1], x[0]) for k, x in octagon_cases.items()]}")

    budget_nine_15 = fat_budget + joint_nonconnector + 2 * a0
    outer_angle_price = rational(1, 2)
    marked_angle_cap = rational(16, 100000)
    effective_weight = weight - outer_angle_price / 2
    yc = (sqrt(33 + 32 * effective_weight) - 1) / 8
    xc = sqrt(1 - yc * yc)
    positive(marked_angle_cap - (xc * (1 + 2 * yc) - 2 * effective_weight * asin(xc) - outer_angle_price * PI),
             "acute mark endpoint with outer angle charge")
    positive(2 * weight + outer_angle_price - 1, "obtuse mark endpoint has nonpositive cost")
    ear = 2 - (weight + outer_angle_price) * PI
    for adjacent_face in (a0 - PI / 4, sqrt(3) / 2 - PI / 6):
        positive(2 * marked_angle_cap - ear - adjacent_face, "all-outer ear and its inner neighbor")
    seam_angle_area = rational(8224, 10000)
    cy = (sqrt(9 + 8 * outer_angle_price) - 1) / 4
    sy = sqrt(1 - cy * cy)
    positive(seam_angle_area - (sy * (1 + cy) - outer_angle_price * asin(sy)),
             "seam face area minus its outer angle charge")
    outer_angle_budget = budget_nine_15 + 15 * (m1 - marked_angle_cap) - 13 * PI * outer_angle_price
    weighted_mark14 = rational(-733, 50000)
    weighted_value = x14 * (1 + 2 * sqrt(1 - x14 * x14)) - 2 * effective_weight * asin(x14) - PI / 2
    root14 = sqrt(1 - radius_sq * u14 * u14)
    weighted_slope = (1 + 2 * (1 - 2 * x14 * x14 - effective_weight) / sqrt(1 - x14 * x14)) * (
        t14 * (radius * u14 * u14 / root14 + v14) / 2)
    positive(weighted_mark14 - weighted_value, "fourteen-arc weighted mark tangent at the mean")
    positive(x14 - xc, "fourteen-arc mean lies past the weighted maximum")
    positive(-weighted_slope, "weighted mark tangent slopes down")
    split_mark = rational(44, 100)
    sp, cp = sin_cos(split_mark / 2)
    split_half_chord = (radius * cp - sqrt(1 - radius_sq * sp * sp)) * sp
    weighted_mark_floor = weighted_value + weighted_slope * (2 * rim_width - 2 * PI / 14)
    positive(weighted_value + weighted_slope * (split_mark - 2 * PI / 14), "short weighted mark tangent is nonnegative")
    positive(weighted_mark_floor + (2 * weight + outer_angle_price - 1) * split_half_chord,
             "obtuse mark endpoint is below the fourteen-arc weighted tangent")
    outer_angle_budget14 = budget_nine_15 - inactive_cost + 14 * (m1 - weighted_mark14) - 6 * PI

    mark_flank = sqrt(rational(1, 2) - weight)
    mark_repair = mark_flank * sqrt(1 - mark_flank * mark_flank) - 2 * weight * asin(mark_flank)
    positive(2 * a0 + weighted_mark_floor - (4 - PI / 2 + mark_repair),
             "inactive degree-four star with two active outer vertices pays its omitted seam area")
    one_corner_quad = rational(13, 4)
    critical = rational(1, 8)
    for upper in (2 * sqrt(3) - PI / 6, 4 * sqrt(1 - critical * critical) - (PI / 2 - asin(critical)) / 2,
                  4 - PI / 4):
        positive(one_corner_quad - upper, "one-corner quadrilateral area charge")

    vertex_price = rational(-4, 25)
    star_unmarked, star_transition = rational(1472, 1000), rational(1012, 1000)
    positive(star_unmarked - fan_price_max(vertex_price), "unmarked face in the inactive pentagon")
    positive(star_unmarked + vertex_price * PI, "obtuse endpoint for the inactive pentagon")

    def closed_asin(x):
        if x.hi < 7 * SCALE // 10:
            return asin(x)
        return PI / 2 - asin(sqrt(1 - x * x))

    boxes = [(SCALE // 4, SCALE // 2), (SCALE // 2, SCALE)]
    while boxes:
        lo, hi = boxes.pop()
        x = Interval(lo, hi)
        h = sqrt(1 - x * x)
        alpha = closed_asin(x)
        z0 = 1 / (4 * x)
        z = Interval(z0.lo, min(SCALE, z0.hi))
        # At the maximum with a positive outer angle, alpha+2*gamma is
        # pi-asin(1/(4*sin(alpha))). The zero-angle endpoint has zero area.
        bound = rational(0)
        for angle, cosine in ((alpha, h), (PI - alpha, -h)):
            candidate = x * (cosine + sqrt(1 - z * z)) - (PI - closed_asin(z) - angle) / 4
            upper = Interval(0, max(0, candidate.hi)) - vertex_price * angle
            bound = max((bound, upper), key=lambda a: a.hi)
        if bound.hi < star_transition.lo:
            continue
        if hi - lo < SCALE // 2**22:
            raise ArithmeticError("inactive pentagon transition unresolved")
        mid = (lo + hi) // 2
        boxes.extend(((lo, mid), (mid, hi)))
    positive(star_transition + vertex_price * PI, "inactive pentagon transition with no stationary point")
    inactive_pair_quad = one_corner_quad - 2 * a0
    short_edge = rational(619, 500)
    positive(short_edge * short_edge - (2 - 2 / rational(213, 50)),
             "an inactive disk has an active outer neighbor within 1.238")
    corner_slope = (outer_angle_price - vertex_price) / 2
    transition_caps = (
        (850, 505), (950, 567), (1050, 643), (1150, 717), (1238, 780),
        (1320, 833), (1400, 881), (1480, 925), (1570, 966), (1660, 996),
    )
    for edge_cap, area_cap in transition_caps:
        short_half = rational(edge_cap, 2000)
        limit = rational(area_cap, 1000)
        angle_boxes = [(0, PI.hi)]
        while angle_boxes:
            lo, hi = angle_boxes.pop()
            angle = Interval(lo, hi)
            sin4, cos4 = sin_cos(angle / 4)
            sin2, cos2 = 2 * sin4 * cos4, 1 - 2 * sin4 * sin4
            sine, cosine = 2 * sin2 * cos2, 1 - 2 * sin2 * sin2
            if sine.hi <= short_half.lo:
                k = Interval(sine.hi, sine.hi)
            elif sine.lo >= short_half.hi:
                bound = short_half * short_half / Interval(sine.lo, sine.lo)
                k = Interval(bound.hi, bound.hi)
            else:
                k = Interval(short_half.hi, short_half.hi)
            if k.hi <= corner_slope.lo:
                continue
            if k.lo > corner_slope.hi:
                ratio = corner_slope / k
                bound = (sqrt(k * k - corner_slope * corner_slope) + corner_slope * closed_asin(ratio)
                         - k * cosine + (-vertex_price - outer_angle_price) * angle / 2)
                if bound.hi < limit.lo:
                    continue
            if hi - lo < SCALE // 2**22:
                raise ArithmeticError(f"short inactive pentagon transition unresolved at {edge_cap}")
            mid = (lo + hi) // 2
            angle_boxes.extend(((lo, mid), (mid, hi)))
        positive(limit + vertex_price * PI, "short inactive pentagon transition at a degenerate angle")
    pentagon_cost = 2 * PI * vertex_price + 2 * star_unmarked + rational(1795, 1000) - 2 * a0
    star_many_neighbors = 2 * seam_angle_area - rational(1, 2)
    positive(a0 - star_many_neighbors, "one inactive seam with at least three outer neighbors")
    inactive_pair_pentagon = max((pentagon_cost, star_many_neighbors), key=lambda x: x.hi)
    priced_normal = tuple(rational(x, 1000) for x in (6936, 6906, 7050))
    priced_tri = tuple(rational(x, 1000) for x in (13650, 13570, 13380))
    shared_priced_normal = (priced_normal[0], rational(496, 100) + joint_nonconnector / 2,
                            rational(315, 100) + joint_nonconnector)
    shared_priced_tri = (priced_tri[0], rational(1223, 100) + joint_nonconnector / 2,
                         rational(1055, 100) + joint_nonconnector)
    shared_priced_reverse = (rational(1145, 100), rational(1094, 100) + joint_nonconnector / 2,
                             rational(897, 100) + joint_nonconnector)
    shared_priced_quad = tuple(rational(v, 100) for v in (1999, 2098, 2202))
    weighted_quad_end_types = {
        (0, 0): shared_priced_quad[0], (0, 1): shared_priced_quad[1], (1, 1): shared_priced_quad[2],
        (0, 2): rational(2067, 100), (1, 2): rational(2173, 100), (2, 2): rational(2151, 100),
    }
    chord_normal = tuple(rational(v, 100) for v in (913, 875, 849))
    chord_tri = tuple(rational(v, 100) for v in (1688, 1697, 1680))
    chord_reverse = tuple(rational(v, 100) for v in (1360, 1513, 1482))
    chord_quad_end_types = {
        (0, 0): rational(2345, 100), (0, 1): rational(2437, 100), (1, 1): rational(2535, 100),
        (0, 2): rational(2424, 100), (1, 2): rational(2519, 100), (2, 2): rational(2508, 100),
    }
    chord_budget = outer_angle_budget + 2 * PI * rational(8, 3)
    seven_chord_cost = 4 * rational(860, 100) + 2 * (rational(6674, 1000) + joint_nonconnector / 2) + rational(2321, 100)
    seven_chord_deficit = outer_angle_budget + 4 * PI - seven_chord_cost
    positive(seven_chord_deficit, "seven neighbors with both ends of the quadrilateral shared")
    for bound, raw in ((chord_normal, (9130, 7104, 5198)),
                       (chord_tri, (16880, 15324, 13508)),
                       (chord_reverse, (13600, 13484, 11528))):
        for ends in range(3):
            # Check the raw certificate value plus the share compensation.
            discrepancy = bound[ends] - rational(raw[ends], 1000) - ends * joint_nonconnector / 2
            if discrepancy.lo > 0 or discrepancy.hi < 0:
                raise ArithmeticError("inconsistent chord price compensation")
    for ends, bound in enumerate(shared_priced_quad):
        positive(bound - 3 * (a0 + seam_angle_area + joint_nonconnector) - ends * end_phase,
                 "nonpositive span with priced outer angles")
    ten_weighted_budget = ten_budget - mark_loss + 14 * (m1 - weighted_mark14) - 6 * PI
    transferred_ten_quad = rational(2155, 100)
    transferred_ten_tri = (rational(1228, 100) + joint_nonconnector / 2,
                            rational(1065, 100) + joint_nonconnector)
    positive(transferred_ten_quad - 3 * (a0 + seam_angle_area + joint_nonconnector) - 2 * end_phase - 1,
             "ten-ring radius transfer with a nonpositive quadrilateral span")
    for ends in (1, 2):
        positive(transferred_ten_tri[ends - 1] - shared_priced_reverse[ends]
                 - rational(2, 5) * (rational(7, 4) - radius + 3),
                 "ten-ring radius transfer with a reversed triangular cap")
    ten_weighted_counts = [0, 0, 0]
    for lengths, starts, neutral, budget in ten_hard:
        if valid_rim_charges(lengths, starts, neutral):
            cost = shared_ten_cost(lengths, starts, neutral, rim_priced=True) + 6 * (14 * rim_width - PI)
            if (budget - cost).lo > 0:
                ten_weighted_counts[0] += 1
                continue
        offsets = [sum(lengths[:i]) for i in range(len(lengths))]
        ends = [sum(p in starts for p in ((i - 1) % 10, (i + length - 1) % 10))
                for i, length in zip(offsets, lengths)]
        costs = [
            shared_priced_normal[e] if length == 1 else shared_priced_tri[e] if length == 2 else
            shared_priced_quad[e] + (length - 3) * (a0 + seam_angle_area + joint_nonconnector)
            for length, e in zip(lengths, ends)
        ]
        total = sum(costs)
        if (ten_weighted_budget - total).lo > 0:
            ten_weighted_counts[1] += 1
            continue
        alternatives = []
        for i, length in enumerate(lengths):
            j, k = (i - 1) % len(lengths), (i + 1) % len(lengths)
            if length != 3 or ends[i] != 2 or max(lengths[j], lengths[k]) > 2:
                continue
            cost = total - costs[i] + transferred_ten_quad
            for neighbor in (j, k):
                if lengths[neighbor] == 2:
                    upper = transferred_ten_tri[ends[neighbor] - 1]
                elif ends[neighbor] == 1:
                    upper = rational(501, 100) + joint_nonconnector / 2
                else:
                    upper = costs[neighbor] + rational(2, 5) * (rational(7, 4) - radius + 3)
                cost += upper - costs[neighbor]
            alternatives.append(cost)
        if not alternatives:
            raise ArithmeticError(f"ten-edge weighted transfer unavailable for {lengths}, {starts}")
        cost = min(alternatives, key=lambda a: a.hi)
        positive(ten_weighted_budget - cost, f"ten-edge weighted transfer, lengths {lengths}, shares {starts}")
        ten_weighted_counts[2] += 1
    print(f"ten-edge alternatives without strict quadrilateral boxes: {ten_weighted_counts}")

    priced_one_cross = 5 * priced_normal[0] + priced_normal[1] + rational(506, 100) + rational(11925, 1000) + joint_nonconnector
    positive(outer_angle_budget - priced_one_cross, "one mixed shared group with a degree-eight core")
    twin_budget = outer_angle_budget + 2 * PI * rational(11, 10)
    twin_normal, twin_priced = rational(7803, 1000), rational(773, 100)
    twin_adjacent = 3 * twin_normal + 2 * twin_priced + 2 * rational(1329, 100) + joint_nonconnector
    twin_triple = 4 * twin_normal + 2 * rational(1342, 100) + rational(392, 100) + 2 * joint_nonconnector
    twin_two_pairs = (4 * twin_normal + rational(575, 100) + rational(1342, 100) + rational(117, 10)
                      + 2 * joint_nonconnector)
    positive(twin_budget - twin_adjacent, "two adjacent triangle blocks sharing one outer site")
    positive(twin_budget - twin_triple, "two triangle blocks sharing with the ordinary edge between them")
    positive(twin_budget - twin_two_pairs, "adjacent triangle blocks with another shared pair")

    def weighted_shared_cost(lengths, starts, reverse, transferred_quad=None, neutral=frozenset(), chord=False):
        offset, cost = 0, rational(0)
        quad_transfer = {}
        if transferred_quad is not None:
            begin = sum(lengths[:transferred_quad])
            left, right = (begin - 1) % 9, (begin + 2) % 9
            quad_transfer = {left: left, (right + 1) % 9: right}
        for i, length in enumerate(lengths):
            cuts = ((offset - 1) % 9, (offset + length - 1) % 9)
            ends = sum(cut in starts for cut in cuts)
            if length == 1:
                if chord:
                    cost += chord_normal[ends]
                elif offset not in quad_transfer:
                    cost += shared_priced_normal[ends]
                elif not ends:
                    cost += priced_normal[1]
                elif ends == 1 and quad_transfer[offset] in starts:
                    cost += rational(506, 100) + joint_nonconnector / 2
                else:
                    cost += shared_priced_normal[ends] + rational(4, 5) * (rational(7, 4) - radius + 3)
            elif length == 2:
                if len(lengths) == 8 and len(starts) == 1 and ends == 1 and reverse < 0:
                    return priced_one_cross
                if chord:
                    cost += (chord_reverse if i == reverse else chord_tri)[ends]
                else:
                    cost += (shared_priced_reverse if i == reverse else shared_priced_tri)[ends]
            else:
                if i == transferred_quad:
                    cost += rational((1944, 2033, 2128)[ends], 100)
                else:
                    charges = tuple(sorted(2 if cut in neutral else int(cut in starts) for cut in cuts))
                    caps = chord_quad_end_types if chord else weighted_quad_end_types
                    cost += caps[charges] + (length - 3) * (a0 + seam_angle_area + joint_nonconnector)
            offset += length
        return cost

    group_span_cap = 2 * asin(2 / center_min)

    def enough_span(lengths, starts, reverse):
        groups = []
        for edge in range(9):
            if (edge - 1) % 9 not in starts and edge in starts:
                group = {edge}
                end = edge
                while end in starts:
                    end = (end + 1) % 9
                    group.add(end)
                groups.append(group)
        blocks, offset = [], 0
        for length in lengths:
            blocks.append(set(range(offset, offset + length)))
            offset += length
        for negative in ({-1} if reverse < 0 else blocks[reverse]):
            for choices in product((False, True), repeat=len(groups)):
                covered = set().union(*(group for group, use in zip(groups, choices) if use))
                span = sum(choices) * group_span_cap.hi
                for block in blocks:
                    remaining = block - covered - {negative}
                    bound = len(remaining) * gap_cap.hi
                    # A block's omitted positive edges only reduce its remaining span.
                    span += bound if negative in block and negative in covered else min(bound, root_cap.hi)
                if span < (2 * PI).lo:
                    break
            else:
                return True
        return False

    for degree in range(4, 9):
        counts = {(back, repeat): [0, 0] for back in (False, True) for repeat in range(4)}
        inactive_nonconnector_cases = 0
        forward_distinct = 0
        min_distinct = None
        chord_closed = 0
        chord_gap = None
        seven_chord_closed = 0
        for lengths in product(range(1, 11 - degree), repeat=degree):
            if sum(lengths) != 9 or lengths != min(lengths[i:] + lengths[:i] for i in range(degree)):
                continue
            owner_length = tuple(length for length in lengths for _ in range(length))
            quad_transfers = [i for i, length in enumerate(lengths) if length == 3
                              and lengths[i - 1] == lengths[(i + 1) % degree] == 1]
            for backward in (-1, *(i for i, l in enumerate(lengths) if l >= 2)):
                if sum(min((l - int(i == backward)) * gap_cap.hi, root_cap.hi)
                       for i, l in enumerate(lengths)) < (2 * PI).lo:
                    continue
                if backward < 0:
                    cost = rational(0)
                    for i, length in enumerate(lengths):
                        neighbors = lengths[i - 1], lengths[(i + 1) % degree]
                        if length == 1:
                            cost += priced_normal[neighbors.count(2)]
                        elif length == 2:
                            cost += priced_tri[neighbors.count(1)]
                        else:
                            cost += ten_blocks[length] - length * (a0 - seam_angle_area)
                    deficit = outer_angle_budget - cost
                    positive(deficit, f"forward nine-edge ring, distinct, m=15, parts {lengths}")
                    forward_distinct += 1
                    if min_distinct is None or deficit.lo < min_distinct.lo:
                        min_distinct = deficit
                for repeat in range(3 if backward >= 0 else 4):
                    for positions in combinations(range(9), repeat):
                        starts = set(positions)
                        if repeat == 3 and any((p + 1) % 9 in starts for p in starts):
                            continue
                        cost = shared_ten_cost(lengths, starts, set(), backward)
                        if cost is None:
                            continue
                        deficit = budget_nine_15 + mark_loss_15 - cost
                        if repeat:
                            neutral = {p for p in starts if min(owner_length[p], owner_length[(p + 1) % 9]) >= 3
                                       and ((p - 1) % 9 not in starts or owner_length[(p - 1) % 9] >= 3)
                                       and ((p + 1) % 9 not in starts or owner_length[(p + 2) % 9] >= 3)}
                            weighted_cost = min((weighted_shared_cost(lengths, starts, backward, q, neutral)
                                                 for q in (None, *quad_transfers)), key=lambda value: value.hi)
                            weighted_deficit = outer_angle_budget - weighted_cost
                            deficit = max((deficit, weighted_deficit), key=lambda x: x.lo)
                            if degree == 7 and lengths.count(2) == 2 and backward < 0:
                                types = {(owner_length[p], owner_length[(p + 1) % 9]) for p in starts}
                                if repeat == 1 and (2, 2) in types:
                                    deficit = twin_budget - twin_adjacent
                                elif repeat == 2 and (2, 2) in types and types.intersection(((1, 2), (2, 1))):
                                    deficit = twin_budget - twin_two_pairs
                                elif repeat == 2 and any(
                                    (p + 1) % 9 in starts and tuple(owner_length[(p + i) % 9] for i in range(3)) == (2, 1, 2)
                                    for p in starts
                                ):
                                    deficit = twin_budget - twin_triple
                            if degree == 8:
                                positive(deficit, f"nine-edge ring, fifteen active sites, degree eight, {lengths}, shares {positions}")
                        tally = counts[backward >= 0, repeat]
                        tally[0] += 1
                        span_possible = deficit.lo <= 0 and enough_span(lengths, starts, backward)
                        if repeat and degree <= 6 and span_possible:
                            chord_deficit = chord_budget - weighted_shared_cost(lengths, starts, backward, neutral=neutral, chord=True)
                            positive(chord_deficit, f"nine-edge ring, chord price, {lengths}, shares {positions}, reverse {backward}")
                            chord_closed += 1
                            chord_gap = chord_deficit if chord_gap is None else min(chord_gap, chord_deficit, key=lambda x: x.lo)
                            deficit = chord_deficit
                        if (degree == 7 and span_possible and lengths == (1, 1, 1, 1, 1, 1, 3)
                                and positions == (5, 8)):
                            deficit = seven_chord_deficit
                            seven_chord_closed += 1
                        if deficit.lo > 0 or not span_possible:
                            tally[1] += 1
                        elif repeat and report_remaining:
                            print(f"remaining b=m=15, h=9, degree={degree}, lengths={lengths}, "
                                  f"reverse_block={backward}, share_starts={positions}")
                        if backward >= 0 and not repeat:
                            positive(deficit, f"reverse nine-edge ring, distinct, m=15, parts {lengths}")
                        if repeat <= 2 and (backward >= 0 or all((p + 1) % 9 not in starts for p in starts)):
                            budget14 = budget_nine_15 - inactive_cost + mark_loss + joint_nonconnector
                            best = shared_ten_cost(lengths, starts, set(), backward)
                            if valid_rim_charges(lengths, starts, set()):
                                priced = (shared_ten_cost(lengths, starts, set(), backward, rim_priced=True)
                                          + 6 * (14 * rim_width - PI))
                                best = min(best, priced, key=lambda c: c.hi)
                            weighted = outer_angle_budget14 + joint_nonconnector - weighted_shared_cost(lengths, starts, backward)
                            deficit14 = max((budget14 - best, weighted), key=lambda value: value.lo)
                            positive(deficit14, f"inactive nonconnector, nine-ring, {lengths}, {positions}")
                            inactive_nonconnector_cases += 1
                # With distinct connectors an inactive connector is exactly
                # one omitted score. An inactive nonconnector improves the budget.
                for inactive in range(-1, degree):
                    budget = budget_nine_15 - inactive_cost + mark_loss + (joint_nonconnector if inactive == -1 else 0)
                    cost = rational(0)
                    for i, l in enumerate(lengths):
                        if i != backward:
                            cost += ten_omitted[l][int(i == inactive)]
                        elif l == 2:
                            cost += reverse_short[0]
                        elif l == 3 and i != inactive:
                            cost += rational(2084, 100)
                        else:
                            cost += ten_omitted[l][int(i == inactive)]
                    positive(budget - cost, f"nine-edge ring, distinct, m=14, parts {lengths}, reverse {backward}, inactive {inactive}")
        if any(excluded != tested for (_, repeat), (tested, excluded) in counts.items() if repeat):
            raise ArithmeticError(f"degree-{degree} nine-ring with fifteen active sites remains")
        print(f"nine-edge ring, fifteen active outer sites, degree {degree}, excluded by (reverse, repeats) "
              f"{[(k, x[1], x[0]) for k, x in counts.items() if x[0]]}")
        if chord_gap is not None:
            print(f"nine-edge ring, chord transfer, degree {degree}: {chord_closed} additional exclusions, deficit {display(chord_gap)}")
        if seven_chord_closed:
            print(f"nine-edge ring, seven-neighbor chord transfer: {seven_chord_closed} excluded, deficit {display(seven_chord_deficit)}")
        print(f"nine-edge ring, inactive nonconnector, degree {degree}: {inactive_nonconnector_cases} excluded")
        if min_distinct is not None:
            print(f"forward nine-edge ring, distinct, m=15, degree {degree}: {forward_distinct} excluded, "
                  f"deficit {display(min_distinct)}")

    # In the fourteen-active-arc case every repeated group is a consecutive
    # pair, including when the inactive disk is one of the connectors.
    inactive_nine_budget = budget_nine_15 - inactive_cost + mark_loss
    pair_span = 2 * asin(2 / center_min)
    inactive_span_caps = (gap_cap, pair_span)
    span_allowance14 = SPAN_PRICE * (14 * rim_width - PI)

    def signed_group_span(pairs, inactive, backward):
        """Drop the reverse edge before pricing each outer disk's net span."""
        used = {e for pair in pairs for e in pair}
        groups = (*pairs, *((e,) for e in range(9) if e not in used))
        span = span_allowance14
        for group in groups:
            count = len(group) - int(backward in group)
            if count:
                caps = inactive_span_caps if group == inactive else ACTIVE_SPAN_CAPS
                span += caps[count - 1]
        return span

    inactive_chord_short = {
        (1,): (749, None), (3,): (667, 599),
        (0, 1): (1506, None), (1, 1): (1347, None),
        (0, 3): (1425, 1332), (1, 3): (1265, 1168),
    }
    inactive_chord_roots = (rational(1555, 100), rational(1732, 100),
                            chord_quad_end_types[0, 0] - seam_angle_area - joint_nonconnector)
    inactive_chord_budget = outer_angle_budget14 + 2 * PI * rational(8, 3)

    def inactive_chord_deficit(parts, repeats, others, inactive, backward, star_credit):
        """Retain one score per active pair and charge the inactive star once."""
        best = None
        for omitted in product(*others):
            for price in range(2 if len(inactive) == 2 and backward < 0 else 1):
                cost = repeats * joint_nonconnector + star_credit
                for part in parts:
                    types = tuple(3 if e in inactive else 1 if e in omitted else 0 for e in part)
                    length = len(part)
                    charged = price if 3 in types else 0
                    if length <= 2:
                        if backward in part:
                            break
                        if not any(types):
                            cost += chord_normal[0] if length == 1 else chord_tri[0]
                            continue
                        bound = inactive_chord_short.get(tuple(sorted(types)), (None, None))[charged]
                        if bound is None:
                            break
                        cost += rational(bound, 100)
                    elif charged:
                        if types not in ((3, 0, 0), (0, 0, 3)):
                            break
                        cost += rational(2161, 100)
                    else:
                        full_ends = int(types[0] == 0) + int(types[-1] == 0)
                        cost += inactive_chord_roots[full_ends] + (length - 3) * a0
                        cost += (types.count(1) + types[1:-1].count(0)) * seam_angle_area
                        cost += types[1:-1].count(0) * joint_nonconnector
                else:
                    deficit = inactive_chord_budget - cost
                    if best is None or deficit.lo > best.lo:
                        best = deficit
        return best

    inactive_normal_pair = 2 * rational(351, 100) + rational(5, 2) * pair_span
    # Type 0 keeps the active score, 1 omits it, 2 is inactive,
    # 3 moves the inactive face area to its outer star, and 4 is a half-score.
    inactive_triangles = {
        (0, 0): (13650, 11450, 11450),
        (0, 1): (11980, 8250, 9020),
        (1, 1): (10430, 6490, 6490),
        (0, 2): (12480, 8920, 9460),
        (1, 2): (10890, 7140, 6820),
        (0, 3): (11180, 7790, 8220),
        (1, 3): (9620, 5950, 5800),
        (0, 4): (12230, 10940, 10940),
        (1, 4): (10500, 6960, 8070),
        (2, 4): (10980, 7400, 8690),
        (3, 4): (9690, 6130, 7480),
        (4, 4): (11460, 11460, 11460),
    }
    inactive_triangles = {k: tuple(rational(x, 1000) for x in v) for k, v in inactive_triangles.items()}
    typed_quad = {
        (0, 0): rational(1208, 100), (0, 1): rational(1386, 100), (0, 2): rational(1496, 100),
        (1, 1): shared_priced_quad[0] - seam_angle_area - joint_nonconnector,
        (1, 2): shared_priced_quad[1] - seam_angle_area - joint_nonconnector,
        (2, 2): shared_priced_quad[2] - seam_angle_area - joint_nonconnector,
    }
    transferred_typed_quad = {
        (0, 0): rational(1118, 100), (0, 1): rational(1306, 100), (0, 2): rational(1412, 100),
        (1, 1): rational(1944, 100) - seam_angle_area - joint_nonconnector,
        (1, 2): rational(2033, 100) - seam_angle_area - joint_nonconnector,
        (2, 2): rational(2128, 100) - seam_angle_area - joint_nonconnector,
    }
    loose_radius_charge = rational(4, 5) * (rational(7, 4) - radius + 3)
    inactive_phase_normal = rational(357, 100)
    inactive_phase_quads = {(3, 0, 0): rational(1825, 100), (3, 0, 4): rational(1845, 100),
                            (3, 1, 0): rational(1495, 100)}
    narrow_triangles = {0: rational(924, 100), 1: rational(755, 100), 4: rational(755, 100)}
    narrow_normal = rational(362, 100)
    positive(rational(448, 100) - narrow_normal, "inactive pair span pays an ordinary edge")
    for active_type, upper in narrow_triangles.items():
        old = inactive_triangles[tuple(sorted((3, active_type)))][0]
        positive(rational(448, 100) + old - narrow_normal - upper - 3 * pair_span / 2,
                 "inactive pair span pays an ordinary edge and the triangular cap")
    for degree in range(4, 9):
        counts_inactive = {(back, size): [0, 0] for back in (False, True) for size in (1, 2)}
        span_exclusions = 0
        chord_exclusions = 0
        inactive_chord_gap = None
        for lengths in product(range(1, 11 - degree), repeat=degree):
            if sum(lengths) != 9 or lengths != min(lengths[i:] + lengths[:i] for i in range(degree)):
                continue
            parts = []
            offset = 0
            for length in lengths:
                parts.append(tuple(range(offset, offset + length)))
                offset += length
            owner = tuple(i for i, length in enumerate(lengths) for _ in range(length))
            for backward in (-1, *(e for e in range(9) if lengths[owner[e]] >= 2)):
                limits = [min((len(part) - int(backward in part)) * gap_cap.hi, root_cap.hi) for part in parts]
                if sum(limits) < (2 * PI).lo:
                    continue
                for repeats in (1, 2):
                    for starts in combinations(range(9), repeats):
                        pairs = tuple((a, (a + 1) % 9) for a in starts)
                        used = set(e for pair in pairs for e in pair)
                        if len(used) != 2 * repeats or any(owner[a] == owner[b] and lengths[owner[a]] == 2 for a, b in pairs):
                            continue
                        for pair in pairs:
                            paid = set(pair)
                            span = pair_span.hi + sum(limit if paid.isdisjoint(part)
                                else sum(e not in paid and e != backward for e in part) * gap_cap.hi
                                for part, limit in zip(parts, limits))
                            if span < (2 * PI).lo:
                                break
                        else:
                            if repeats == 2:
                                span = 2 * pair_span.hi + sum(limit if used.isdisjoint(part)
                                    else sum(e not in used and e != backward for e in part) * gap_cap.hi
                                    for part, limit in zip(parts, limits))
                                if span < (2 * PI).lo:
                                    continue
                            for inactive in (*pairs, *((e,) for e in range(9) if e not in used)):
                                tally = counts_inactive[backward >= 0, len(inactive)]
                                if signed_group_span(pairs, inactive, backward).hi < (2 * PI).lo:
                                    tally[0] += 1
                                    tally[1] += 1
                                    span_exclusions += 1
                                    continue
                                others = tuple(pair for pair in pairs if pair != inactive)
                                best = None
                                for choices in product(range(3), repeat=len(others)):
                                    skipped = set(inactive)
                                    charged = set()
                                    for pair, choice in zip(others, choices):
                                        if choice == 2:
                                            charged.add(pair[0])
                                        else:
                                            skipped.add(pair[choice])
                                    cost = (repeats - len(charged)) * joint_nonconnector
                                    for i, part in enumerate(parts):
                                        length = lengths[i]
                                        missed = sum(e in skipped for e in part)
                                        ends = sum(e in charged for e in ((part[0] - 1) % 9, part[-1]))
                                        inner_shared = any(e in charged for e in part[:-1])
                                        rev = backward in part
                                        if length == 1 and ends:
                                            cost += rational(54, 10) + joint_nonconnector / 2
                                        elif length == 2 and ends:
                                            cost += (reverse_short if rev else (
                                                ten_blocks[2], rational(66, 5) + joint_nonconnector / 2,
                                                rational(1146, 100) + joint_nonconnector))[ends]
                                        elif length >= 3 and (ends or inner_shared):
                                            root = root_side[((0, 0), (0, 1), (1, 1))[ends]]
                                            cost += root + (length - 3) * (2 * a0 + joint_nonconnector)
                                        elif length == 2 and rev:
                                            cost += reverse_short[0]
                                        elif length == 3 and rev and not missed:
                                            cost += rational(2084, 100)
                                        elif length == 3 and len(inactive) == 2 and all(e in part for e in inactive):
                                            cost += rational(171, 10) if missed == 2 else rational(1599, 100)
                                        else:
                                            cost += ten_omitted[length][missed]
                                    if len(inactive) == 2 and all(lengths[owner[e]] == 1 for e in inactive):
                                        cost += inactive_normal_pair - 2 * ten_omitted[1][1]
                                    if best is None or cost.hi < best.hi:
                                        best = cost
                                tally = counts_inactive[backward >= 0, len(inactive)]
                                tally[0] += 1
                                # Three or more active neighbors have at least
                                # two marked losses. Their weighted star costs
                                # are bounded by the corresponding two-neighbor case.
                                regimes = (2,) if len(inactive) == 1 else (1, 2)
                                proved = True
                                for outer_neighbors in regimes:
                                    if (inactive_nine_budget - best + (outer_neighbors - 1) * rational(47, 100)).lo > 0:
                                        continue
                                    star_credit = (rational(0) if len(inactive) == 1 else
                                                   inactive_pair_quad if outer_neighbors == 1 else inactive_pair_pentagon)
                                    credit = star_credit
                                    narrow = (len(inactive) == 2 and
                                              all(lengths[owner[e]] <= 2 for e in inactive) and
                                              any(lengths[owner[e]] == 1 for e in inactive) and
                                              (backward < 0 or all(lengths[owner[e]] == 1 for e in inactive)))
                                    phase_pair = (backward < 0 and len(inactive) == 2 and
                                                  all(lengths[owner[e]] == 2 for e in inactive))
                                    if narrow:
                                        credit += sum(lengths[owner[e]] == 2 for e in inactive) * 3 * pair_span / 2
                                    options = tuple(
                                        range(3) if owner[pair[0]] != owner[pair[1]]
                                        and all(lengths[owner[e]] <= 3 for e in pair) else range(2)
                                        for pair in others
                                    )
                                    for choices in product(*options):
                                        skipped = set(inactive)
                                        skipped.update(pair[i] for pair, i in zip(others, choices) if i < 2)
                                        half_starts = {pair[0] for pair, i in zip(others, choices) if i == 2}
                                        halves = {e for p in half_starts for e in (p, (p + 1) % 9)}
                                        transferred = set()
                                        if degree == 8 and backward < 0:
                                            triangle = next(part for part in parts if len(part) == 2)
                                            if (skipped | halves).isdisjoint(triangle):
                                                transferred = {(triangle[0] - 1) % 9, (triangle[-1] + 1) % 9} - skipped - halves
                                        cost = (repeats - len(halves) // 2) * joint_nonconnector + credit
                                        quad_adjustment = rational(0)
                                        phase_adjustment = rational(0)
                                        for part in parts:
                                            length = len(part)
                                            missed = sum(e in skipped for e in part)
                                            asleep = sum(e in inactive for e in part)
                                            if length == 1:
                                                if asleep:
                                                    cost += narrow_normal if narrow else rational(448, 100)
                                                elif part[0] in halves:
                                                    cost += shared_priced_normal[1]
                                                else:
                                                    cost += rational(528, 100) if missed else priced_normal[int(part[0] in transferred)]
                                            elif length == 2:
                                                left, right = (3 if e in inactive else
                                                               1 if e in skipped else 4 if e in halves else 0 for e in part)
                                                reverse = 1 + part.index(backward) if backward in part else 0
                                                if left > right:
                                                    left, right = right, left
                                                    reverse = 3 - reverse if reverse else 0
                                                if left == right == 0 and transferred:
                                                    cost += priced_tri[len(transferred)]
                                                elif phase_pair and asleep:
                                                    cost += (rational(925, 100) + joint_nonconnector / 2
                                                             if right == 4 else rational(109, 10))
                                                else:
                                                    upper = (narrow_triangles[right if left == 3 else left] if narrow and asleep else
                                                             inactive_triangles[left, right][reverse])
                                                    cost += upper + (int(left == 4) + int(right == 4)) * joint_nonconnector / 2
                                            elif length == 3:
                                                left, middle, right = (3 if e in inactive else
                                                                       1 if e in skipped else 4 if e in halves else 0 for e in part)
                                                endpoints = tuple(sorted(1 if t == 0 else 2 if t == 4 else 0
                                                                         for t in (left, right)))
                                                quad_cost = (typed_quad[endpoints]
                                                             + (int(left == 1) + int(right == 1) + int(middle != 3)) * seam_angle_area)
                                                if middle == 0:
                                                    quad_cost += joint_nonconnector
                                                cost += quad_cost
                                                before, after = (part[0] - 1) % 9, (part[-1] + 1) % 9
                                                if lengths[owner[before]] == lengths[owner[after]] == 1:
                                                    adjustment = transferred_typed_quad[endpoints] - typed_quad[endpoints]
                                                    for edge, cut in ((before, before), (after, part[-1])):
                                                        if edge not in skipped and edge not in halves:
                                                            adjustment += priced_normal[1] - priced_normal[0]
                                                        elif cut in half_starts:
                                                            adjustment += rational(506, 100) + joint_nonconnector / 2 - shared_priced_normal[1]
                                                        else:
                                                            adjustment += loose_radius_charge
                                                    quad_adjustment = min(quad_adjustment, adjustment, key=lambda x: x.hi)
                                                    for pattern, inactive_neighbor, other_neighbor, cut in (
                                                        ((left, middle, right), before, after, part[-1]),
                                                        ((right, middle, left), after, before, before),
                                                    ):
                                                        if (len(inactive) != 2 or inactive_neighbor not in inactive or
                                                                pattern not in inactive_phase_quads):
                                                            continue
                                                        adjustment = (inactive_phase_quads[pattern] - quad_cost
                                                                      + inactive_phase_normal - rational(448, 100))
                                                        if pattern[1] != 1:
                                                            if other_neighbor not in skipped and other_neighbor not in halves:
                                                                adjustment += priced_normal[1] - priced_normal[0]
                                                            elif cut in half_starts:
                                                                adjustment += rational(506, 100) + joint_nonconnector / 2 - shared_priced_normal[1]
                                                            else:
                                                                adjustment += loose_radius_charge
                                                        phase_adjustment = min(phase_adjustment, adjustment, key=lambda x: x.hi)
                                            else:
                                                base = ten_omitted[length][missed]
                                                cost += base - (length - asleep) * (a0 - seam_angle_area) - asleep * a0
                                        adjustment = min(quad_adjustment, phase_adjustment, key=lambda x: x.hi)
                                        if (outer_angle_budget14 - cost - adjustment).lo > 0:
                                            break
                                    else:
                                        fallback = inactive_chord_deficit(parts, repeats, others, inactive, backward, star_credit)
                                        if fallback is not None and fallback.lo > 0:
                                            chord_exclusions += 1
                                            if inactive_chord_gap is None or fallback.lo < inactive_chord_gap.lo:
                                                inactive_chord_gap = fallback
                                            continue
                                        proved = False
                                        if report_remaining:
                                            print(f"remaining b=15, m=14, h=9, degree={degree}, lengths={lengths}, "
                                                  f"reverse_edge={backward}, share_starts={starts}, "
                                                  f"inactive_edges={inactive}, active_neighbors={outer_neighbors}")
                                        else:
                                            break
                                if proved:
                                    tally[1] += 1
        if any(excluded != tested for tested, excluded in counts_inactive.values()):
            raise ArithmeticError(f"degree-{degree} nine-ring with inactive connector remains")
        print(f"nine-edge ring, inactive connector, degree {degree}, by (reverse, inactive edges) "
              f"{[(k, x[1], x[0]) for k, x in counts_inactive.items()]}")
        print(f"nine-edge ring, inactive connector, degree {degree}: {span_exclusions} signed span exclusions")
        if inactive_chord_gap is not None:
            print(f"nine-edge ring, inactive connector, degree {degree}: {chord_exclusions} chord exclusions by neighbor regime, "
                  f"deficit {display(inactive_chord_gap)}")

    def active_pair_bound(lengths, i, j, omitted):
        left, right = lengths[i], lengths[j]
        if i == j:
            return rational(inside_shared_cap[omitted[i]], 100) if left == 3 else None
        if left == right == 1:
            return projection_group
        if min(left, right) == 1 and max(left, right) in ordinary_shared_cap:
            cap_index = j if left == 1 else i
            return mixed_normal[0] + rational(ordinary_shared_cap[lengths[cap_index]][0][omitted[cap_index]], 100)
        if left in symmetric_shared_cap and right in symmetric_shared_cap:
            total = symmetric_shared_cap[left][0][omitted[i]] + symmetric_shared_cap[right][0][omitted[j]]
            return rational(total, 100)
        return None

    nine_budget = -common + 8 * joint_gain + 3 * joint_nonconnector - 2 * inactive_cost + 2 * a0 + mark_loss
    positive(nine_budget - ten_prices + 6 * mark_pair_loss - 5 * ten_blocks[1] - rational(3155, 100),
             "four-edge fat block with two triangular caps and an internal shared pair")
    positive(nine_budget - ten_prices + 6 * mark_pair_loss - rational(8, 5) * PI
             - rational(2995, 100) - 4 * rational(676, 100) - rational(634, 100),
             "four-edge fat block with two triangular caps and a crossed shared pair")
    positive(nine_budget - ten_prices + 5 * mark_pair_loss - 2 * PI
             - rational(2228, 100) - 4 * rational(6615, 1000) - 2 * rational(6585, 1000),
             "three-edge two-core ordinary fan with distinct seams")
    fan_normal, fan_anchor, fan_block = (rational(7142, 1000), rational(7101, 1000), rational(2355, 100))
    fan_cap, fan_cap_end = rational(14085, 1000), rational(2362, 100)
    fan_shift = -rational(3, 5) * PI
    nine_fan_budget = nine_budget - ten_prices + 5 * mark_pair_loss + fan_shift
    positive(nine_fan_budget - 4 * fan_normal - 2 * fan_anchor - fan_block,
             "nine-edge three-fan with the common block bound")
    positive(nine_fan_budget - 2 * fan_normal - 2 * fan_anchor - fan_cap - fan_block,
             "nine-edge three-fan with a nonterminal triangular cap")
    positive(nine_fan_budget - 3 * fan_normal - fan_anchor - fan_cap - fan_cap_end,
             "nine-edge three-fan with a terminal triangular cap")
    for ordinary_cost in (4 * fan_normal + 2 * fan_anchor,
                          2 * fan_normal + 2 * fan_anchor + fan_cap,
                          3 * fan_normal + fan_anchor + fan_cap):
        positive(nine_fan_budget + mark_pair_loss - fan_block - ordinary_cost,
                 "nine-edge three-fan with a shared pair wholly inside the block")
    fan_primary_pair = rational(1365, 100)
    for cost in (fan_block + fan_primary_pair + 3 * fan_normal + fan_anchor,
                 fan_cap_end + fan_primary_pair + 2 * fan_normal + fan_cap):
        positive(nine_fan_budget + mark_pair_loss - cost,
                 "nine-edge three-fan with two primary ordinary edges sharing")
    fan_crossed_block, fan_crossed_normal = rational(2372, 100), rational(696, 100)
    for ordinary_cost in (4 * fan_normal + fan_anchor,
                          2 * fan_normal + fan_anchor + fan_cap,
                          3 * fan_normal + fan_cap):
        positive(nine_fan_budget + mark_pair_loss - fan_crossed_block - fan_crossed_normal - ordinary_cost,
                 "nine-edge three-fan sharing at a bridge end with a primary ordinary edge")
    inactive_mark_run = rational(47, 100) + 5 * mark_pair_loss
    positive(rational(47, 100) - mark_pair_loss, "extra marks incident to the inactive site increase the run loss")
    octagon_fan_budget = fat_budget - inactive_cost + mark_loss + fan_shift + inactive_mark_run
    positive(octagon_fan_budget - 3 * fan_normal - 2 * fan_anchor - rational(2208, 100),
             "octagonal three-fan with the inactive site at a secondary bridge end")
    positive(octagon_fan_budget - 3 * fan_normal - fan_anchor - rational(553, 100) - fan_block,
             "octagonal three-fan with the inactive site at a primary bridge end")
    positive(octagon_fan_budget - 2 * fan_normal - 2 * fan_anchor - rational(53, 10) - fan_block,
             "octagonal three-fan with the inactive site away from both bridge ends on the primary side")

    wide_fat = rational(1495, 100)
    wide_normal, wide_triangle = rational(69, 10), rational(1425, 100)
    wide_quad = tuple(rational(x, 100) for x in (2160, 2230, 2330))
    positive(wide_normal - 5 - joint_nonconnector / 2, "wide ordinary half-score")
    positive(wide_triangle - rational(126, 10) - joint_nonconnector / 2, "wide triangular half-score")
    positive(wide_triangle - rational(1095, 100) - joint_nonconnector, "wide triangular two half-scores")
    for raw, share in ((1320, joint_nonconnector / 2), (1145, joint_nonconnector), (1160, joint_nonconnector)):
        positive(wide_fat - rational(raw, 100) - share, "wide fat-cap half-scores")
    for size in (8, 9):
        checked = 0
        minimum = None
        for degree in range(4, 9):
            for rest in product(range(1, size + 2 - degree), repeat=degree - 2):
                if sum(rest) != size - 2:
                    continue
                if sum(min(l * gap_cap.hi, root_cap.hi) for l in rest) + 2 * gap_cap.hi < (2 * PI).lo:
                    continue
                for repeats in range(size - 6):
                    budget = (fat_budget - inactive_cost + mark_loss if size == 8 else
                              nine_budget - ten_prices + (5 + repeats) * mark_pair_loss)
                    for positions in combinations(range(size), repeats):
                        starts = set(positions)
                        if any((p + 1) % size in starts for p in starts):
                            continue
                        cost, offset = wide_fat, 2
                        for length in rest:
                            if length == 2 and offset in starts:
                                break
                            ends = sum(p in starts for p in ((offset - 1) % size, (offset + length - 1) % size))
                            cost += (wide_normal if length == 1 else wide_triangle if length == 2 else
                                     wide_quad[ends] + (length - 3) * (2 * a0 + joint_nonconnector))
                            offset += length
                        else:
                            deficit = budget - cost
                            positive(deficit, f"wide two-core swap, ring {size}, lengths {rest}, shares {positions}")
                            checked += 1
                            if minimum is None or deficit.lo < minimum.lo:
                                minimum = deficit
        print(f"wide two-core swap, ring {size}: {checked} excluded, deficit {display(minimum)}")

    wide_three_normal = (rational(683, 100), rational(505, 100) + joint_nonconnector / 2)
    wide_three_triangle = (rational(1357, 100), rational(1225, 100) + joint_nonconnector / 2,
                           rational(1045, 100) + joint_nonconnector)
    wide_three_quad = tuple(rational(x, 100) for x in (2005, 2070, 2130))

    def four_neighbor_fat_cost(fat_length, rest, starts):
        lengths = (fat_length,) + rest
        owner = tuple(i for i, length in enumerate(lengths) for _ in range(length))
        neutral = {p for p in starts if owner[p] != owner[(p + 1) % 9]
                   and min(owner[p], owner[(p + 1) % 9]) > 0
                   and min(lengths[owner[p]], lengths[owner[(p + 1) % 9]]) >= 3}
        base = shared_ten_cost(lengths, starts, neutral, strict=True)
        if base is None:
            return None
        ends = int(8 in starts) + int(fat_length - 1 in starts)
        old = (strict_quad if ends == 2 and fat_length == 3 else root_side[((0, 0), (0, 1), (1, 1))[ends]])
        if fat_length == 3:
            return base - old + rational(241, 10)
        merged = rational(3060 if fat_length == 4 else 3855, 100)
        return base - old - (fat_length - 3) * (2 * a0 + joint_nonconnector) + merged

    four_neighbor_count, four_neighbor_margin = 0, None
    for size in (8, 9):
        checked, minimum = 0, None
        for degree in range(4, 9):
            for rest in product(range(1, size + 2 - degree), repeat=degree - 2):
                if sum(rest) != size - 3 or sum(min(l * gap_cap.hi, root_cap.hi) for l in rest) + 3 * gap_cap.hi < (2 * PI).lo:
                    continue
                for repeats in range(size - 6):
                    budget = (fat_budget - inactive_cost + mark_loss + joint_nonconnector if size == 8 else
                              nine_budget - ten_prices + (5 + repeats) * mark_pair_loss)
                    for positions in combinations(range(size), repeats):
                        starts = set(positions)
                        if any((p + 1) % size in starts for p in starts):
                            continue
                        cost, offset = rational(262, 10), 3
                        for length in rest:
                            if length == 2 and offset in starts:
                                break
                            ends = sum(p in starts for p in ((offset - 1) % size, (offset + length - 1) % size))
                            cost += (wide_three_normal[ends] if length == 1 else
                                     wide_three_triangle[ends] if length == 2 else
                                     wide_three_quad[ends] + (length - 3) * (2 * a0 + joint_nonconnector))
                            offset += length
                        else:
                            deficit = budget - cost
                            positive(deficit, f"three-edge two-core swap, ring {size}, lengths {rest}, shares {positions}")
                            checked += 1
                            if minimum is None or deficit.lo < minimum.lo:
                                minimum = deficit
                            if size == 9 and repeats <= 1 and max(rest) <= 2 and rest.count(2) <= 1:
                                degree_four_cost = four_neighbor_fat_cost(3, rest, starts)
                                if degree_four_cost is not None:
                                    deficit = budget - degree_four_cost
                                    positive(deficit, f"three-edge fat block with degree-four core, {rest}, {positions}")
                                    four_neighbor_count += 1
                                    if four_neighbor_margin is None or deficit.lo < four_neighbor_margin.lo:
                                        four_neighbor_margin = deficit
        print(f"three-edge two-core swap, ring {size}: {checked} excluded, deficit {display(minimum)}")
    print(f"three-edge fat block with degree-four core: {four_neighbor_count} excluded, "
          f"deficit {display(four_neighbor_margin)}")

    for fat_length in (4, 5):
        four_neighbor_count, four_neighbor_margin = 0, None
        for degree in range(4, 12 - fat_length):
            for rest in product(range(1, 10 - degree), repeat=degree - 2):
                if sum(rest) != 9 - fat_length:
                    continue
                span = sum(min(l * gap_cap.hi, root_cap.hi) for l in rest) + gap_cap.hi + root_cap.hi
                if span < (2 * PI).lo:
                    continue
                for repeats in range(3):
                    budget = nine_budget - ten_prices + (5 + repeats) * mark_pair_loss
                    for positions in combinations(range(9), repeats):
                        starts = set(positions)
                        if any((p + 1) % 9 in starts for p in starts):
                            continue
                        cost = four_neighbor_fat_cost(fat_length, rest, starts)
                        if cost is None:
                            continue
                        deficit = budget - cost
                        positive(deficit, f"{fat_length}-edge fat block with degree-four core, {rest}, {positions}")
                        four_neighbor_count += 1
                        if four_neighbor_margin is None or deficit.lo < four_neighbor_margin.lo:
                            four_neighbor_margin = deficit
        print(f"{fat_length}-edge fat block with degree-four core and one-edge side: "
              f"{four_neighbor_count} excluded, deficit {display(four_neighbor_margin)}")

    checked = [0, 0]
    minimum = [None, None]
    distinct_regular = (rational(0), rational(676, 100), rational(1351, 100), wide_three_quad[0])
    coarse_regular = (rational(0), wide_three_normal[0], wide_three_triangle[0], wide_three_quad[0])
    omitted_regular = (rational(0), rational(510, 100), rational(1230, 100), rational(1950, 100))
    positive(distinct_regular[1] - wide_three_normal[1], "two active ordinary blocks can share in the swapped octagon")
    for degree in range(4, 8):
        for rest in product(range(1, 10 - degree), repeat=degree - 2):
            if sum(rest) != 5 or sum(min(l * gap_cap.hi, root_cap.hi) for l in rest) + 3 * gap_cap.hi < (2 * PI).lo:
                continue
            if max(rest) > 3:
                raise ArithmeticError("unexpected long cap in three-edge octagon swap")
            coarse_sum = sum(coarse_regular[l] for l in rest)
            active_cost = rational(2543, 100) + sum(distinct_regular[l] for l in rest)
            if rest.count(1) >= 2:
                inactive_pair_cost = (active_cost - 2 * distinct_regular[1] + rational(63, 10)
                                      + rational(5, 2) * pair_span + joint_nonconnector)
                positive(fat_budget - inactive_cost + mark_loss - inactive_pair_cost,
                         f"two ordinary blocks with an inactive shared connector after swapping, lengths {rest}")
            omitted_costs = [rational(2462, 100) + coarse_sum]
            omitted_costs.extend(rational(2543, 100) + coarse_sum - coarse_regular[l] + omitted_regular[l]
                                 for l in rest)
            budgets = (fat_budget + mark_loss_15, fat_budget - inactive_cost + mark_loss)
            for inactive, costs in enumerate(((active_cost,), omitted_costs)):
                for cost in costs:
                    deficit = budgets[inactive] - cost
                    positive(deficit, f"three-edge two-core swap with distinct seams, lengths {rest}, inactive {inactive}")
                    checked[inactive] += 1
                    if minimum[inactive] is None or deficit.lo < minimum[inactive].lo:
                        minimum[inactive] = deficit
    for inactive, count in enumerate(checked):
        print(f"three-edge two-core swap with distinct seams, inactive {inactive}: "
              f"{count} excluded, deficit {display(minimum[inactive])}")

    fat_cross = (fat, rational(1285, 100) + joint_nonconnector / 2, rational(108, 10) + joint_nonconnector)
    tri_cross = (ten_blocks[2], rational(66, 5) + joint_nonconnector / 2, rational(1146, 100) + joint_nonconnector)
    for degree in range(4, 9):
        checked = 0
        minimum = None
        for rest in product(range(1, 11 - degree), repeat=degree - 2):
            if sum(rest) != 7 or sum(min(l * gap_cap.hi, root_cap.hi) for l in rest) + 2 * gap_cap.hi < (2 * PI).lo:
                continue
            lengths = (2,) + rest
            for repeats in (0, 1, 2):
                budget = nine_budget - ten_prices + (5 + repeats) * mark_pair_loss
                for positions in combinations(range(9), repeats):
                    starts = set(positions)
                    if any((p + 1) % 9 in starts for p in starts):
                        continue
                    cost = shared_ten_cost(lengths, starts - {0}, set())
                    if cost is None:
                        continue
                    ends = int(1 in starts) + int(8 in starts)
                    fat_cost = rational(1065, 100) + joint_nonconnector if 0 in starts else fat_cross[ends]
                    deficit = budget - cost + tri_cross[ends] - fat_cost
                    positive(deficit, f"two-core nine-edge ring, length two, parts {rest}, sharing {positions}")
                    checked += 1
                    if minimum is None or deficit.lo < minimum.lo:
                        minimum = deficit
        if minimum is not None:
            print(f"two-core nine-edge ring, length two, degree {degree}: {checked} excluded, deficit {display(minimum)}")

    for degree in range(4, 9):
        for repeats in (1, 2):
            tested = excluded = 0
            minimum = None
            for lengths in product(range(1, 11 - degree), repeat=degree):
                if sum(lengths) != 9 or lengths != min(lengths[i:] + lengths[:i] for i in range(degree)):
                    continue
                owner = tuple(i for i, length in enumerate(lengths) for _ in range(length))
                for starts in combinations(range(9), repeats):
                    pairs = tuple((a, (a + 1) % 9) for a in starts)
                    if len({edge for pair in pairs for edge in pair}) != 2 * repeats:
                        continue
                    if any(owner[a] == owner[b] and lengths[owner[a]] == 2 for a, b in pairs):
                        continue
                    for extra in (-1, *(i for i, length in enumerate(lengths) if length >= 3)):
                        chains = 9 - repeats + (2 if extra == -1 else 0)
                        budget = nine_budget - repeats * joint_nonconnector + (14 - chains) * mark_pair_loss
                        cost = shared_ten_cost(lengths, set(starts))
                        deficits = [budget - ten_prices + repeats * joint_nonconnector - cost]
                        for use in product(range(3), repeat=repeats):
                            omitted = [0] * degree
                            for pair, choice in zip(pairs, use):
                                if choice < 2:
                                    omitted[owner[pair[choice]]] += 1
                            if 2 not in use and (extra == -1 or lengths[extra] == 3):
                                cost = sum(ten_omitted[length][r] for length, r in zip(lengths, omitted))
                                deficits.append(budget - ten_prices - cost)
                            taken = set()
                            old_cost = rational(0)
                            for (a, b), choice in zip(pairs, use):
                                if choice != 2:
                                    continue
                                i, j = owner[a], owner[b]
                                if extra in (i, j) or i in taken or j in taken:
                                    break
                                pair_bound = active_pair_bound(lengths, i, j, omitted)
                                if pair_bound is None:
                                    break
                                old_cost += pair_bound
                                taken.update((i, j))
                            else:
                                old_cost += sum(cap_bounds[length][r] for i, (length, r) in
                                                enumerate(zip(lengths, omitted)) if i not in taken)
                                deficits.append(budget - old_cost)
                        if degree == 8 and repeats == 2 and all(any(lengths[owner[e]] == 2 for e in pair) for pair in pairs):
                            deficits.append(budget - (5 * ordinary + 2 * mixed_normal[0] + rational(307, 10)))
                        deficit = max(deficits, key=lambda x: x.lo)
                        if repeats == 1 or degree == 8:
                            positive(deficit, f"nine-edge shared case {lengths}, groups {pairs}, extra block {extra}")
                        tested += 1
                        if deficit.lo > 0:
                            excluded += 1
                        if minimum is None or deficit.lo < minimum.lo:
                            minimum = deficit
            print(f"nine-edge ring, fourteen outer sites, degree {degree}, repeats {repeats}: "
                  f"{excluded}/{tested} excluded, deficit {display(minimum)}")

    ordinary_saving = ordinary - ordinary_inactive
    for length in range(2, 6):
        positive(length * ordinary - cap_bounds[length][0], "remaining forward block at most ordinary cost")
        positive(length * ordinary - cap_bounds[length][1] - ordinary_saving,
                 "remaining inactive forward block at most inactive ordinary cost")
    for repeats in (0, 1):
        cost = (7 - 2 * repeats) * ordinary + repeats * unpriced_limit + 16
        deficit = (-common - cost + 8 * joint_gain + (2 - repeats) * joint_nonconnector
                   - inactive_cost + 2 * a0)
        positive(deficit, "nine edges with the backward edge in a triangular cap")
        for saving in (ordinary_saving, rational(3, 5)):
            positive(deficit + saving - inactive_cost, "one inactive connector in the backward triangular case")
        if repeats:
            positive(deficit + unpriced_limit - inactive_limit - inactive_cost,
                     "the repeated ordinary connector in the backward triangular case is inactive")
        print(f"backward triangular cap, ordinary repeats={repeats}: all-active joint deficit {display(deficit)}")


def check_local_optimality():
    """Certify the quadratic form used to exclude nearby asymmetric improvements."""
    root_two = sqrt(2)
    radius = sqrt(6) + sqrt(3)
    cosine = sqrt(2 + root_two) / 2
    sine = sqrt(2 - root_two) / 2
    ring = 2 * cosine
    side = 2 + root_two
    stress = 1 + root_two
    half_chord = root_two / 2
    move = rational(1, 100)

    def add(a, b):
        return a[0] + b[0], a[1] + b[1]

    def subtract(a, b):
        return a[0] - b[0], a[1] - b[1]

    def scale(k, a):
        return k * a[0], k * a[1]

    def rotate(a):
        return -a[1], a[0]

    def norm_squared(a):
        return a[0] * a[0] + a[1] * a[1]

    e = [(rational(1), rational(0))]
    for _ in range(7):
        e.append(scale(half_chord, add(e[-1], rotate(e[-1]))))
    h = [add(scale(cosine, a), scale(sine, rotate(a))) for a in e]
    points = [(rational(0), rational(0))]
    points.extend(scale(ring, a) for a in e)
    points.extend(scale(side, a) for a in h)
    points.extend(scale(2 * ring, a) for a in e)
    junctions = []

    def append(point, links, rim=False):
        junctions.append((len(points), links, rim))
        points.append(point)

    for k in range(8):
        j = (k + 1) % 8
        i, i_next, c, d, d_next = 1 + k, 1 + j, 9 + k, 17 + k, 17 + j
        append(h[k], [(0, root_two * stress), (i, stress), (i_next, stress)])
        append(scale(stress, h[k]), [(c, root_two * stress), (i, stress), (i_next, stress)])
        append(add(scale(3 * cosine, e[k]), scale(sine, rotate(e[k]))),
               [(i, root_two), (c, rational(1)), (d, rational(1))])
        append(add(scale(3 * cosine, e[j]), scale(-sine, rotate(e[j]))),
               [(i_next, root_two), (c, rational(1)), (d_next, rational(1))])
        normal = scale(side + half_chord, h[k])
        tangent = scale(half_chord, rotate(h[k]))
        append(subtract(normal, tangent), [(c, root_two * stress), (d, stress)], True)
        append(add(normal, tangent), [(c, root_two * stress), (d_next, stress)], True)

    interior_sigma_lower = (1 + root_two) / (root_two * ring) - 2 * root_two * move
    positive(interior_sigma_lower - rational(89, 100), "stability of all circumcenters")
    positive(4 * interior_sigma_lower - root_two * (2 + move), "circumcenter moves by at most 4e")
    positive(root_two * (side + half_chord) - (2 + root_two / 2) * radius * move - 5,
             "boundary bisector is transverse throughout the perturbation interval")
    positive(rational(5, 2) - (2 + move), "boundary root stays in [-e/2,e/2]")
    positive(6 - radius, "boundary transition moves by at most 3e")

    size = 2 * len(points)
    zero = rational(0)
    matrix = [[zero] * (i + 1) for i in range(size)]

    def outer_product(entries, weight):
        for j, (a, x) in enumerate(entries):
            for b, y in entries[:j + 1]:
                i, k = max(a, b), min(a, b)
                matrix[i][k] += weight * x * y

    for j, links, rim in junctions:
        incident = {i for i, _ in links}
        for i in range(25):
            if i not in incident:
                positive(norm_squared(subtract(points[i], points[j])) - rational(289, 100),
                         "nonincident center is farther than 1.7")
        if not rim:
            limit = radius - rational(1, 10)
            positive(limit * limit - norm_squared(points[j]), "interior junction stays in the target")
        else:
            matrix[2 * j][2 * j] -= 1
            matrix[2 * j + 1][2 * j + 1] -= 1
            outer_product(list(zip((2 * j, 2 * j + 1), points[j])), rational(5))
        for i, weight in links:
            dx, dy = subtract(points[i], points[j])
            for k in range(2):
                outer_product([(2 * i + k, rational(1)), (2 * j + k, rational(-1))], weight)
            outer_product([(2 * i, dx), (2 * i + 1, dy), (2 * j, -dx), (2 * j + 1, -dy)],
                          rational(5))

    rotation = [value for point in points for value in rotate(point)]
    rotation_norm_squared = sum((norm_squared(point) for point in points), zero)
    outer_product(list(enumerate(rotation)), 1 / rotation_norm_squared)
    for i in range(size):
        matrix[i][i] -= rational(1, 5)

    # Every pivot is enclosed as the exact symmetric Schur complement is formed.
    minimum_pivot = None
    for k in range(size):
        pivot = matrix[k][k]
        positive(pivot, f"local quadratic-form pivot {k + 1}/{size}")
        if minimum_pivot is None or pivot.lo < minimum_pivot.lo:
            minimum_pivot = pivot
        for i in range(k + 1, size):
            multiplier = matrix[i][k] / pivot
            for j in range(k + 1, i + 1):
                matrix[i][j] -= multiplier * matrix[j][k]

    positive(rational(2, 25) - 681 * move * move, "perturbation lies inside the certified neighborhood")
    print(f"local optimum verified: {size} positive pivots, smallest {display(minimum_pivot)}")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--remaining", action="store_true", help="list the unresolved discrete nine-ring cases")
    args = parser.parse_args()
    check_classification_and_symmetry()
    check_seven_inner_disks()
    check_repeat_area_losses()
    check_repeat_with_sixteen_active_arcs()
    check_degree_eight_seam_charges()
    check_core_requires_inner_exterior()
    check_wide_core_cone()
    check_inner_octagon_types()
    check_fourteen_outer_eight_inner()
    check_area_bounds()
    check_fourteen_mark_mean()
    check_rim_angle_stability()
    check_rim_angle_dual()
    check_outer_projection_clusters()
    check_core_degree()
    check_degree_eight_disjoint_clusters()
    check_fifteen_active_octagonal_star()
    check_inactive_connector_outer_triangles()
    check_sharp_octagonal_star(args.remaining)
    check_local_optimality()
