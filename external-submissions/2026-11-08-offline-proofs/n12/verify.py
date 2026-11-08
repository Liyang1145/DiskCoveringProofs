"""Strict offline certificates. Uses Python integers and the standard library."""

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt


SCALE = 1 << 144


@dataclass(frozen=True)
class Interval:
    """The interval [lo/SCALE, hi/SCALE]. All operations round outwards."""

    lo: int
    hi: int

    @staticmethod
    def point(value):
        f = Fraction(value)
        n = f.numerator * SCALE
        d = f.denominator
        return Interval(n // d, -(-n // d))

    @staticmethod
    def box(lo, hi):
        return Interval(Interval.point(lo).lo, Interval.point(hi).hi)

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Interval) else Interval.point(value)

    def __add__(self, other):
        other = self.coerce(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        products = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(products) // SCALE, -(-max(products) // SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ArithmeticError('reciprocal of an interval containing zero')
        return Interval(SCALE * SCALE // self.hi, -(-SCALE * SCALE // self.lo))

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.reciprocal()

    def square(self):
        hi = max(self.lo ** 2, self.hi ** 2)
        lo = 0 if self.lo <= 0 <= self.hi else min(self.lo ** 2, self.hi ** 2)
        return Interval(lo // SCALE, -(-hi // SCALE))

    def sqrt(self):
        if self.lo < 0:
            raise ArithmeticError('square root of a possibly negative value')
        lo = isqrt(self.lo * SCALE)
        hi = isqrt(self.hi * SCALE)
        if hi ** 2 < self.hi * SCALE:
            hi += 1
        return Interval(lo, hi)

    def nonnegative_part(self):
        return Interval(max(0, self.lo), max(0, self.hi))

    def split(self):
        mid = (self.lo + self.hi) // 2
        if not self.lo < mid < self.hi:
            raise ArithmeticError('box could not be subdivided further')
        return Interval(self.lo, mid), Interval(mid, self.hi)


def require(condition, claim):
    if not condition:
        raise ArithmeticError(claim)


@dataclass(frozen=True)
class Jet:
    """Interval value and interval bounds on derivatives r, s, ss."""

    value: Interval
    dr: Interval
    ds: Interval
    dss: Interval

    @staticmethod
    def constant(value):
        zero = Interval.point(0)
        return Jet(Interval.coerce(value), zero, zero, zero)

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Jet) else Jet.constant(value)

    def __add__(self, other):
        b = self.coerce(other)
        return Jet(self.value + b.value, self.dr + b.dr, self.ds + b.ds, self.dss + b.dss)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, -self.dr, -self.ds, -self.dss)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        a = self
        b = self.coerce(other)
        return Jet(a.value * b.value, a.dr * b.value + a.value * b.dr,
                   a.ds * b.value + a.value * b.ds,
                   a.dss * b.value + 2 * a.ds * b.ds + a.value * b.dss)

    __rmul__ = __mul__

    def reciprocal(self):
        v = self.value.reciprocal()
        dr = -self.dr * v.square()
        ds = -self.ds * v.square()
        dss = -(self.dss * v + 2 * self.ds * ds) * v
        return Jet(v, dr, ds, dss)

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def sqrt(self):
        v = self.value.sqrt()
        dr = self.dr / (2 * v)
        ds = self.ds / (2 * v)
        dss = (self.dss - 2 * ds.square()) / (2 * v)
        return Jet(v, dr, ds, dss)


R_LO = '0.36110296374450864411'
R_HI = '0.36110296374450864412'
S_LO = '0.278241660874427910'
S_HI = '0.278241660874427915'


def geometry(r, s, sqrt3):
    u = (1 + r + s) / 2
    v = (r * r - (1 - u) * (1 - u)).sqrt()
    d = r + s / 2 + (r * r - 3 * s * s / 4).sqrt()
    norm = u * u + v * v
    bx = (u * u - v * v) / norm
    by = 2 * u * v / norm
    cosine = (bx + sqrt3 * by) / 2
    g = 2 * d * cosine - d * d - 1 + r * r
    return u, v, d, bx, by, g


def residual(r, s):
    one, zero = Interval.point(1), Interval.point(0)
    r = Jet(r, one, zero, zero)
    s = Jet(s, zero, one, zero)
    return geometry(r, s, Jet.constant(3).sqrt())[-1]


def verify_root_box(r_lo, r_hi, s_lo, s_hi):
    r = Interval.box(r_lo, r_hi)
    s = Interval.box(s_lo, s_hi)
    g = residual(r, s)
    require(g.dr.lo > 0, 'G_r > 0')
    require(g.dss.hi < 0, 'G_ss < 0')
    require(residual(r, Interval.point(s_lo)).ds.lo > 0, 'G_s(r, s_lo) > 0')
    require(residual(r, Interval.point(s_hi)).ds.hi < 0, 'G_s(r, s_hi) < 0')

    mid = Interval.point((Fraction(s_lo) + Fraction(s_hi)) / 2)
    lower = residual(Interval.point(r_lo), mid).value + g.ds * (s - mid)
    upper = residual(Interval.point(r_hi), mid).value + g.ds * (s - mid)
    require(lower.hi < 0, 'G(r_lo, s) < 0')
    require(upper.lo > 0, 'G(r_hi, s) > 0')
    return r, s


def verify_upper():
    verify_root_box('0.36110', '0.36111', '0.278', '0.2785')
    r, s = verify_root_box(R_LO, R_HI, S_LO, S_HI)
    print('root: signs verified on both the coarse and refined isolation rectangles')

    sqrt3 = Interval.point(3).sqrt()
    u, v, d, bx, by, _ = geometry(r, s, sqrt3)
    require(s.lo > 0 and (r - s).lo > 0, '0 < s < r')
    require((1 - r - s).lo > 0 and (d - r).lo > 0 and (1 - d).lo > 0,
            'radial points are in the sector')
    require((d + r - 1).lo > 0, 'the disk at L contains E')
    require(u.lo > 0 and v.lo > 0 and (bx - Fraction(1, 2)).lo > 0 and by.lo > 0,
            '0 < arg(B) < pi/3')

    # X is the unique solution of the two perpendicular bisector equations.
    ax, ay = u - s, v
    ex, ey = d / 2 - s, sqrt3 * d / 2
    f = (u.square() + v.square() - s.square()) / 2
    h = (d.square() - s.square()) / 2
    det = ax * ey - ay * ex
    require(det.lo > 0, 'the bisectors are independent')
    x = (f * ey - ay * h) / det
    y = (ax * h - f * ex) / det
    require(x.lo > 0 and y.lo > 0 and (sqrt3 * x - y).lo > 0,
            'X is in the open angular sector')
    require((1 - x.square() - y.square()).lo > 0, 'X is inside the unit disk')
    require((r.square() - (x - s).square() - y.square()).lo > 0,
            'X is strictly inside each of the three disks')
    print('sector: all strict geometric inequalities verified')


def verify_local():
    r = Interval.box(R_LO, R_HI)
    s = Interval.box(S_LO, S_HI)
    sqrt3 = Interval.point(3).sqrt()
    u, v, d, _, _, _ = geometry(r, s, sqrt3)
    t = r + s
    require((t - r).lo > 0 and (1 - 2 * r.square() - t).lo > 0,
            'the high-pair angular bound is on its unsaturated branch')
    require(((1 - r.square()).sqrt() - d).lo > 0,
            'the low disk is on the increasing branch of the unit-circle half-angle')
    require((v - u / 100).lo > 0, 'exclusive endpoints of the two test arcs')

    zero = Interval.point(0)
    one = Interval.point(1)
    a = (s, zero)
    h_plus = (u, v)
    h_minus = (u, -v)
    low = (d / 2, d * sqrt3 / 2)

    def rotate(p):
        x, y = p
        return (-x - sqrt3 * y) / 2, (sqrt3 * x - y) / 2

    centers = [p for b in (a, h_plus, h_minus, low) for p in (b, rotate(b), rotate(rotate(b)))]

    def excludes(p, omit, extra):
        for index, (x, y) in enumerate(centers):
            if index in omit:
                continue
            gap = (p[0] - x).square() + (p[1] - y).square() - (r + extra).square()
            require(gap.lo > 0, f'point separated from disk {index}')

    margin = Fraction(1, 20)
    excludes((one, zero), (3, 6), margin)
    excludes((t, zero), (0, 3, 6), margin)
    excludes(((d - r) / 2, (d - r) * sqrt3 / 2), (0, 1, 9), 0)
    print('local geometry: strict separation of witness arcs and intersection points verified')

    def acos_second(c):
        sin_angle = (1 - c.value.square()).sqrt()
        return -(c.dss + c.value * c.ds.square() / sin_angle.square()) / sin_angle

    def second(direction):
        va, vb, vc = direction
        a = Jet(s, zero, Interval.point(va), zero)
        b = Jet(s, zero, Interval.point(vb), zero)
        c = Jet(Interval.point(Fraction(-1, 2)), zero, -sqrt3 * vc / 2,
                Interval.point(Fraction(vc * vc, 2)))
        rj = Jet.constant(r)
        ell2 = a * a + b * b - 2 * a * b * c
        h = (rj * rj - ell2 / 4).sqrt()
        si = (1 - c * c).sqrt()
        far = (rj * rj + a * b * c + 2 * h * a * b * si / ell2.sqrt()).sqrt()
        d = rj + far
        low_cosine = (d * d + 1 - rj * rj) / (2 * d)

        def high_cosine(x):
            return (1 + rj + x) / (2 * (rj + x + rj * rj).sqrt())

        return acos_second(high_cosine(a)) + acos_second(high_cosine(b)) + acos_second(low_cosine)

    aa = second((1, 0, 0))
    bb = second((0, 1, 0))
    cc = second((0, 0, 1))
    ab = (second((1, 1, 0)) - aa - bb) / 2
    ac = (second((1, 0, 1)) - aa - cc) / 2
    bc = (second((0, 1, 1)) - bb - cc) / 2
    minor2 = aa * bb - ab.square()
    det = aa * (bb * cc - bc.square()) - ab * (ab * cc - bc * ac) + ac * (ab * bc - bb * ac)
    require(aa.hi < 0 and minor2.lo > 0 and det.hi < 0, 'the local Hessian is negative definite')
    print('local lower bound: all three Hessian minor signs verified at the candidate')


def twice_tan_half_angle(cosine):
    return 2 * ((1 - cosine).nonnegative_part() / (1 + cosine)).sqrt()


def weighted_arc_boxes(radius, shift, weight, slope, cap, min_d, touches_unit_circle):
    require(weight >= slope * shift, 'the inner density is nonnegative')
    if touches_unit_circle:
        # If the inner circle is missed, only the outer arc contributes.
        cosine_min = Interval.point(1 - radius ** 2).sqrt()
        require(twice_tan_half_angle(cosine_min).hi < Interval.point(cap).lo,
                'bound on the unit-circle arc alone')

    # If the inner circle is met, e <= 2R and |d-e| <= shift.
    d_range = Interval.box(min_d, 2 * radius + shift)
    e_range = Interval.box(min_d - shift, 2 * radius)
    shift_upper = Interval.point(shift).hi
    cap_lower = Interval.point(cap).lo
    boxes = [(d_range, e_range)]
    accepted = 0
    excluded = 0
    while boxes:
        d, e = boxes.pop()
        if (d - e).lo > shift_upper or (e - d).lo > shift_upper:
            excluded += 1
            continue
        c = e / (2 * radius)
        beta = twice_tan_half_angle(c)
        sine = (1 - c.square()).nonnegative_part().sqrt()
        moment = slope * (e.square() - d.square() + shift ** 2) * sine / (2 * e)
        upper = weight * beta + moment
        if touches_unit_circle:
            upper += twice_tan_half_angle((d.square() + (1 - radius ** 2)) / (2 * d))
        if upper.hi < cap_lower:
            accepted += 1
            continue
        require(accepted + excluded + len(boxes) < 50000, 'box limit for displaced circle')
        if d.hi - d.lo >= e.hi - e.lo:
            boxes.extend((child, e) for child in d.split())
        else:
            boxes.extend((d, child) for child in e.split())
    return accepted, excluded


def verify_displaced():
    # Use R exactly. Smaller radii are treated in the proof by enlargement.
    radius = Fraction('0.362')
    weight = Fraction('0.45')
    total_lower = (1 + weight) * Fraction('3.14')
    cap = Fraction('0.41')
    require(11 * cap < total_lower, 'total measure contradiction for 11')
    accepted, excluded = weighted_arc_boxes(radius, 3 * radius - 1, weight, 5, cap, 1 - radius, True)
    print(f'11 boundary disks: verified {accepted} boxes; {excluded} outside |d-e| <= 0.086')

    shift = Fraction('0.12')
    far = Fraction('0.46')
    slope = Fraction(15, 4)
    cap, far_cap = Fraction('0.396'), Fraction('0.575')
    require((radius ** 2 - (1 - 2 * radius) ** 2) / far < shift, 'bound on closer center')
    require(10 * cap + far_cap < total_lower, 'total measure contradiction for 10 with far center')
    outer = weighted_arc_boxes(radius, shift, weight, slope, cap, 1 - radius, True)
    inner = weighted_arc_boxes(radius, shift, weight, slope, far_cap, far, False)
    print(f'10 boundary disks with far inner center: verified/pruned boxes {outer} outer, {inner} far')


def atan_small(x, terms):
    # Alternating series, with the first omitted term bounding the error.
    p = sum((-1) ** n * x ** (2 * n + 1) / (2 * n + 1) for n in range(terms))
    q = p + (-1) ** terms * x ** (2 * terms + 1) / (2 * terms + 1)
    return Interval.box(min(p, q), max(p, q))


PI = 16 * atan_small(Fraction(1, 5), 28) - 4 * atan_small(Fraction(1, 239), 12)
ASIN_TERMS = 18
ASIN_COEFF = [Fraction(1)]
for j in range(1, ASIN_TERMS):
    ASIN_COEFF.append(ASIN_COEFF[-1] * Fraction((2 * j - 1) ** 2, 2 * j * (2 * j + 1)))
ASIN_COEFF = [Interval.point(c) for c in ASIN_COEFF]


def acos_nonnegative(x):
    # For x in [0,1], acos(x) = 2 asin(sqrt(z)), z=(1-x)/2 <= 1/2.
    z = (1 - x) / 2
    poly = ASIN_COEFF[-1]
    for coefficient in reversed(ASIN_COEFF[:-1]):
        poly = coefficient + z * poly
    partial = 2 * z.sqrt() * poly
    # c_n <= 1. The remaining tail is at most 4 * z**ASIN_TERMS.
    tail = SCALE
    for _ in range(ASIN_TERMS):
        tail = -(-tail * z.hi // SCALE)
    return Interval(partial.lo, partial.hi + 4 * tail)


def acos_upper_from_lower_cosine(c):
    # c is an integer scaled by SCALE and is a lower bound on the cosine.
    if c >= SCALE:
        return 0
    if c <= -SCALE:
        return PI.hi
    if c >= 0:
        return acos_nonnegative(Interval(c, c)).hi
    return (PI - acos_nonnegative(Interval(-c, -c))).hi


def max_half_angle(radius):
    cosine = Interval.point(1 - radius * radius).sqrt()
    return Interval(0, acos_upper_from_lower_cosine(cosine.lo))


def verify_boundary():
    radius = Fraction('0.362')
    half = max_half_angle(radius)
    require((8 * half).hi < PI.lo, 'eight arcs do not cover the unit circle')
    require((6 * half + max_half_angle(2 * radius)).hi < PI.lo,
            'nine boundary disks have neither triple intersections nor nonadjacent overlaps')

    # If the inner disks miss the test circle up to zero-length arcs, both
    # circles must be covered in angle by only the m boundary disks.
    for m, t in ((9, Fraction('0.543')), (10, Fraction('0.45'))):
        require(radius < t < 1 - 2 * radius ** 2 and t > 1 - 2 * radius,
                'concave half-angle bound applies')
        d = Interval.point(t + radius ** 2).sqrt()
        cosine = (1 + t) / (2 * d)
        a = Interval(0, acos_upper_from_lower_cosine(cosine.lo))
        slope = t * (1 - t - 2 * radius ** 2) / (t + 2 * radius ** 2 - t * t)
        require((m * a).hi < PI.lo and (m * half).hi < ((1 + slope) * PI).lo,
                'two-circle angular budget')
    print('boundary: count, nine-disk ring and small-inner-center inequalities verified')


def verify_sharp_constants():
    scale = 1 << 40
    r10 = Fraction(397044643907, scale)
    r9 = Fraction(397036907462, scale)
    r_left = r9 - Fraction(1, scale)
    d9 = Fraction(739421569679, scale)
    s9 = Fraction(205388772068, scale)
    require(r_left < Fraction(R_LO) < Fraction(R_HI) < r9 < r10 < Fraction('0.362'),
            'radius order for enlargement')
    require(PI.lo * scale // SCALE == 3454217652357 and -(-PI.hi * scale // SCALE) == 3454217652358,
            'C++ pi enclosure')
    for endpoint, terms in ((Fraction(1,4),9), (Fraction(1,3)+Fraction(1,scale),12),
                            (Fraction(1,2)+Fraction(1,scale),15)):
        power = 2*terms+1
        require(endpoint**power/power < Fraction(17,scale), 'C++ atan remainder')
    require(1 - r9 < d9 < (1-r9*r9), 'the boundary cap is increasing up to d9')
    peak = max_half_angle(r9)
    c = Interval.point((1 + d9*d9 - r9*r9)/(2*d9))
    require(8 * peak.hi + acos_upper_from_lower_cosine(c.lo) < PI.lo,
            'all nine boundary center norms exceed d9')

    t = Fraction('0.548')
    require(s9 + r9 < t < 1 - 2*r9*r9 and t > max(r9,1-2*r9), 'nine-disk small-center test radius')
    d = Interval.point(t+r9*r9).sqrt()
    cosine = (1+t)/(2*d)
    a = acos_upper_from_lower_cosine(cosine.lo)
    weight = t*(1-t-2*r9*r9)/(t+2*r9*r9-t*t)
    require(9*a < PI.lo and 9*peak.hi < ((1+weight)*PI).lo,
            'at least one inner center norm exceeds s9')
    require(s9+d9-r9 > r9, 'that inner center misses the opposite central point')
    t_max = Fraction('0.431')
    require(t_max < d9 and (t_max+r9)**2 < 1-r9*r9, 'monotone witness angle caps')

    r = Interval.box(R_LO, R_HI)
    s = Interval.box(S_LO, S_HI)
    sqrt3 = Interval.point(3).sqrt()
    _, _, d, _, _, _ = geometry(r, s, sqrt3)
    h = (r.square()-3*s.square()/4).sqrt()
    cos_beta = (d.square()+1-r.square())/(2*d)
    sin_beta = (1-cos_beta.square()).sqrt()
    slope = (1-r.square()-d.square())/(2*d.square()*sin_beta)*(-sqrt3*s/4-sqrt3*s.square()/(8*h))
    require(slope.lo * scale // SCALE == -151041251349 and
            -(-slope.hi * scale // SCALE) == -151041251348, 'C++ tangent slope enclosure')
    require(s.lo*scale > 305113000000*SCALE and s.hi*scale < 306763000000*SCALE and
            -551955000000 < -scale//2 < -547557000000, 'tangent point in the local Hessian box')
    print('sharp certificates: dyadic constants, angle caps and tangent slope verified')


@dataclass(frozen=True)
class CircleWeight:
    t: Interval
    k: Interval
    critical: Interval | None
    weight: int

    @staticmethod
    def make(radius, thousandths, weight):
        t = Fraction(thousandths, 1000)
        k = t * t - radius * radius
        critical = Interval.point(k).sqrt() if k > 0 else None
        return CircleWeight(Interval.point(t), Interval.point(k), critical, weight)

    def angle_upper(self, d):
        # Minimize (d + k/d)/(2t). Its minimum for k>0 is at sqrt(k),
        # or at the nearer interval endpoint if sqrt(k) is outside.
        if self.critical is not None:
            if d.hi < self.critical.lo:
                b = d.hi
            elif d.lo > self.critical.hi:
                b = d.lo
            else:
                return acos_upper_from_lower_cosine((self.critical / self.t).lo)
        else:
            b = d.lo
            if b == 0:
                return PI.hi
        d0 = Interval(b, b)
        cosine = (d0 + self.k / d0) / (2 * self.t)
        return acos_upper_from_lower_cosine(cosine.lo)


# Entries are (1000*t, 1000000*w). Caps are for sums of *half* arc angles.
CIRCLE_TESTS = (
    ('0.3545', 9, '0.29450', '0.16363',
     ((1000, 812475), *zip(range(395, 581, 5),
       (9605, 9201, 8833, 8477, 8160, 7853, 7564, 7289, 7028, 6778,
        6540, 6310, 6090, 5875, 5671, 5464, 5273, 5081, 4893, 4708,
        4526, 4345, 4165, 3986, 3807, 3626, 3445, 3258, 3071, 2873,
        2682, 2449, 2267, 1942, 1821, 1244, 1283, 44)))),
    ('0.355', 10, '0.23660', '0.38600',
     ((1000, 650400),
      *[(t, 100 * w) for t, w in zip(range(320, 400, 10), (429, 321, 304, 168, 172, 326, 363, 250))],
      *[(t, 100 * w) for t, w in zip(range(420, 580, 10),
       (124, 116, 107, 100, 93, 87, 81, 74, 69, 62, 59, 49, 50, 30, 42, 19))])),
)


def verify_concentric():
    require(PI.lo > Interval.point('3.14').hi, 'pi > 3.14')
    for radius, m, outer_cap, inner_cap, weights in CIRCLE_TESTS:
        radius, outer_cap, inner_cap = map(Fraction, (radius, outer_cap, inner_cap))
        total = Fraction(sum(w for _, w in weights), 1000000)
        require(Interval.point(m * outer_cap + (12 - m) * inner_cap).hi < (total * PI).lo,
                'total angular measure contradiction')
        circles = [CircleWeight.make(radius, t, weight) for t, weight in weights]

        def check_range(domain, cap):
            stack = [domain]
            accepted = 0
            limit = Interval.point(1000000 * cap).lo
            while stack:
                d = stack.pop()
                upper = sum(circle.weight * circle.angle_upper(d) for circle in circles)
                if upper < limit:
                    accepted += 1
                    continue
                require(accepted + len(stack) < 20000, 'box limit for concentric test')
                stack.extend(d.split())
            return accepted

        outer = check_range(Interval.box(1 - radius, 1 + radius), outer_cap)
        inner = check_range(Interval.box(0, 1 - radius), inner_cap)
        print(f'{m} boundary disks at radius {radius}: verified {outer} outer and {inner} inner intervals')


if __name__ == '__main__':
    verify_upper()
    verify_local()
    verify_boundary()
    verify_sharp_constants()
    verify_displaced()
    verify_concentric()
