"""Integer/rational verifier. No binary floating point is used."""

import json
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from pathlib import Path


class I:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = self.lo if hi is None else Q(hi)
        assert self.lo <= self.hi

    @staticmethod
    def lift(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, rhs):
        y = I.lift(rhs)
        return I(self.lo + y.lo, self.hi + y.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, rhs):
        return self + (-I.lift(rhs))

    def __rsub__(self, lhs):
        return I.lift(lhs) + (-self)

    def __mul__(self, rhs):
        y = I.lift(rhs)
        ends = (self.lo * y.lo, self.lo * y.hi,
                self.hi * y.lo, self.hi * y.hi)
        return I(min(ends), max(ends))

    __rmul__ = __mul__

    def __truediv__(self, rhs):
        y = I.lift(rhs)
        assert y.lo > 0 or y.hi < 0
        return self * I(1 / y.hi, 1 / y.lo)

    def __rtruediv__(self, lhs):
        return I.lift(lhs) / self

    def sq(self):
        a, b = self.lo**2, self.hi**2
        return I(0 if self.lo <= 0 <= self.hi else min(a, b), max(a, b))

    def sqrt(self):
        assert self.lo >= 0
        d = 2**80

        def floor_scaled(q):
            return isqrt((q.numerator * d**2) // q.denominator)

        return I(Q(floor_scaled(self.lo), d), Q(floor_scaled(self.hi) + 1, d))


def setup(r, s):
    h = (r.sq() - 3 * s.sq() / 4).sqrt()
    return h, r + s / 2 + h, (r.sq() + r + s).sqrt()


def cs(r, d):
    c = (1 + d.sq() - r.sq()) / (2 * d)
    assert 0 < c.lo <= c.hi < 1
    return c, (1 - c.sq()).sqrt()


def alpha_d(r, d):
    return (1 - r.sq() - d.sq()) / (2 * d.sq() * cs(r, d)[1])


def slope(r, s):
    h, a, b = setup(r, s)
    return alpha_d(r, a) * (Q(1, 2) - 3 * s / (4 * h)) + alpha_d(r, b) / b


def cos_sum(r, s):
    _, a, b = setup(r, s)
    ca, sa = cs(r, a)
    cb, sb = cs(r, b)
    return ca * (cb.sq() - sb.sq()) - 2 * sa * cb * sb


def check_construction(data):
    r, s = I(*data["r"]), I(*data["s"])
    assert 0 < s.lo <= s.hi < r.lo <= r.hi < Q("0.362")
    h, a, b = setup(r, s)
    assert a.hi < b.lo
    assert (s + s/2 + h - r).lo > 0
    for d in (a, b):
        assert d.lo > 1 - r.lo
        assert (d.sq() + r.sq()).hi < 1
        assert cs(r, d)[0].lo > Q("0.9")

    s0, s1 = I(s.lo), I(s.hi)
    for z, sign in ((s0, 1), (s1, -1)):
        assert (sign * slope(r, z)).lo > 0

    sm = I((s.lo + s.hi) / 2)
    rl, rh = I(r.lo), I(r.hi)
    bound = Q(data["mid_slope_bound"])
    assert slope(rl, s0).hi < bound
    assert slope(rl, s1).lo > -bound
    assert cos_sum(rl, sm).lo > Q(1, 2) + bound * (s.hi - s.lo) / 2
    assert cos_sum(rh, sm).hi < Q(1, 2)

    cb, sb = cs(r, b)
    root3 = I(3).sqrt()
    cd, sd = (cb + root3 * sb) / 2, (root3 * cb - sb) / 2
    assert cd.lo > 0 and sd.lo > 0
    x, y = b * cd - a, b * sd
    u, v = s / 2 - a, root3 * s / 2
    cross = x * v - y * u
    squared_product = (x.sq() + y.sq()) * (u.sq() + v.sq()) * (
        (x - u).sq() + (y - v).sq())
    assert cross.lo > Q(data["construction"]["mixed_cross_lower"])
    assert (4 * r.sq() * cross.sq() - squared_product).lo > Q(
        data["construction"]["mixed_margin_lower"])
    print("PASS: isolated symmetric radius and exact twelve-disk construction")


def alpha_dd(r, d):
    c, s = cs(r, d)
    cp = (d.sq() - 1 + r.sq()) / (2 * d.sq())
    cpp = (1 - r.sq()) / (d * d.sq())
    return -cpp / s - c * cp.sq() / (s * s.sq())


def local_cos(r, s, t):
    c = (s.sq() + t.sq() - r.sq()) / (2*s*t)
    cp = (s.sq() - t.sq() + r.sq()) / (2*s.sq()*t)
    cq = (t.sq() - s.sq() + r.sq()) / (2*s*t.sq())
    return c, cp, cq


def lambda_enclosure(data):
    r, s0 = I(*data["r"]), I(*data["s"])
    h, a, _ = setup(r, s0)
    t0 = s0/2 + h
    c0, _, ct0 = local_cos(r, s0, t0)
    lam = alpha_d(r, a) * (1-c0.sq()).sqrt() / ct0
    assert lam.lo > 0
    return r, s0, t0, lam


def j_hessian(r, s, t, lam):
    b = (r.sq()+r+s).sqrt()
    c, p, q = local_cos(r, s, t)
    assert 0 < c.lo <= c.hi < 1
    sn = (1-c.sq()).sqrt()
    c_ss = (t.sq()-r.sq()) / (s.sq()*s*t)
    c_st = -(s.sq()+t.sq()+r.sq()) / (2*s.sq()*t.sq())
    c_tt = (s.sq()-r.sq()) / (s*t.sq()*t)
    h_ss = 2*(alpha_dd(r,b)/(4*b.sq())-alpha_d(r,b)/(4*b.sq()*b))
    h_ss -= lam*(c_ss/sn+c*p.sq()/(sn.sq()*sn))
    h_st = -lam*(c_st/sn+c*p*q/(sn.sq()*sn))
    h_tt = alpha_dd(r,r+t)-lam*(c_tt/sn+c*q.sq()/(sn.sq()*sn))
    return h_ss.hi < 0 and (h_ss*h_tt-h_st.sq()).lo > 0


def check_local(data):
    r, s0, t0, lam = lambda_enclosure(data)
    s, t = I(*data["local"]["s"]), I(*data["local"]["t"])
    assert s.lo < s0.lo <= s0.hi < s.hi
    assert t.lo < t0.lo <= t0.hi < t.hi
    b = (r.sq()+r+s).sqrt()
    assert (r+s).hi < 1
    assert (b.sq()-(r+s).sq()-r.sq()).lo > 0
    assert (b.sq()+r.sq()).hi < 1
    assert j_hessian(r, s, t, lam)
    print("PASS: strict local optimality inequality")


def atan_remainder_bounds(x, n):
    total = sum((-1)**k * x**(2*k+1) / (2*k+1) for k in range(n))
    next_total = total + (-1)**n * x**(2*n+1) / (2*n+1)
    return I(min(total, next_total), max(total, next_total))


PI = 16 * atan_remainder_bounds(Q(1, 5), 16) - 4 * atan_remainder_bounds(Q(1, 239), 6)
H = 16384


@lru_cache(maxsize=None)
def cos_upper(i, mesh=H):
    x2 = Q(i*i, mesh*mesh)
    term = total = Q(1)
    for k in range(1, 11):
        term *= -x2 / (2*k * (2*k-1))
        total += term
    return total


def angle_upper(cos_min, mesh=H):
    if cos_min >= 1:
        return 0
    low, high = 0, (PI.hi*mesh).__ceil__()
    while high-low > 1:
        mid = (high+low)//2
        if cos_upper(mid, mesh) <= cos_min:
            high = mid
        else:
            low = mid
    return high


def sin_lower(x):
    return sum((-1)**k * x**(2*k+1) / _fact(2*k+1) for k in range(6))


def _fact(n):
    z = 1
    for k in range(2, n+1):
        z *= k
    return z


def arc_units(r, t, lo, hi):
    if lo == 0 and t <= r:
        return (PI.hi*H).__ceil__()
    if lo > t+r or hi < t-r:
        return 0
    k = t*t-r*r
    if k <= lo*lo:
        cos_min = (lo+k/lo) / (2*t)
    elif k >= hi*hi:
        cos_min = (hi+k/hi) / (2*t)
    else:
        cos_min = I(k).sqrt().lo / t
    return angle_upper(cos_min)


def arc_max(r, circles, lo, hi, mesh):
    pieces = ((hi-lo)*mesh).__ceil__()
    prev, best = lo, 0
    for i in range(1, pieces+1):
        nxt = lo + (hi-lo)*Q(i, pieces)
        value = sum(w*arc_units(r, t, prev, nxt) for t, w in circles)
        best = max(best, value)
        prev = nxt
    return best


def check_arc_tests(data):
    r = Q(data["outer_cutoff"])
    assert r == Q("0.361103") and Q(data["r"][1]) < r
    alpha_upper = Q("0.3695")
    assert sin_lower(alpha_upper) > r
    assert 17*alpha_upper < 2*PI.lo
    assert sin_lower(Q("0.82")) > 2*r
    assert 12*alpha_upper + 2*Q("0.82") < 2*PI.lo
    assert 2*(r/(1-r))**2 < 1
    assert (1-2*r*r)**2 * (1-(r/(1-r))**2) > Q(1,4)
    assert 1 - 2*Q(data["r"][0])**2/(1-Q(data["r"][0])) < Q(2,3)
    assert Q("0.354") > 0 and 8*alpha_upper < PI.lo
    assert PI.hi < Q("3.142") and PI.lo > Q("3.14159")
    expected = [(Q("0.354"), 9), (Q("0.354"), 10), (r, 11)]
    for test, (r, m) in zip(data["arc_tests"], expected, strict=True):
        assert Q(test["r"]) == r and test["outer_count"] == m
        circles = [(Q(t), w) for t, w in test["weighted_circles"]]
        assert all(0 < t <= 1 and t != r and type(w) is int and w > 0
                   for t, w in circles)
        ao = arc_max(r, circles, 1-r, 1, test["grid"])
        ai = arc_max(r, circles, Q(0), 1-r, test["grid"])
        weight = sum(w for _, w in circles)
        assert Q(m*ao + (12-m)*ai, H) < PI.lo * weight
        print(f"PASS: r={r}, outer={m}, arc maxima <= ({ao}, {ai})/{H}")


def check_small_inner(data):
    r = Q(data["outer_cutoff"])
    inner_end = 1-Q(data["r"][0])
    for cfg, (m, endpoint) in zip(data["small_inner_tests"],
                                  [(9, Q("0.1")), (10, Q("0.05"))], strict=True):
        assert cfg["outer_count"] == m
        prev = Q(0)
        for lower, upper, radius, w in cfg["pieces"]:
            lo, hi, t = Q(lower), Q(upper), Q(radius)
            assert lo == prev and lo < hi < t-r and 0 < w and r < t < 1
            circles = ((Q(1), 100), (t, w))
            ao = arc_max(r, circles, 1-r, 1, cfg["grid"])
            ai = arc_max(r, circles, Q(0), inner_end, cfg["grid"])
            assert Q(m*ao + (11-m)*ai, H) < PI.lo*(100+w)
            prev = hi
        assert prev == endpoint
        print(f"PASS: r={r}, outer={m}, no inner center with norm <= {endpoint}")


def box_verify(box, test, max_depth):
    stack = [(tuple(box), 0)]
    leaves = 0
    while stack:
        b, depth = stack.pop()
        if test(b):
            leaves += 1
            continue
        assert depth < max_depth, ("unverified box", b)
        i = max(range(len(b)), key=lambda i: b[i][1]-b[i][0])
        l, u = b[i]
        m = (l+u)/2
        stack.extend(((b[:i]+(piece,)+b[i+1:], depth+1)
                      for piece in ((l, m), (m, u))))
    return leaves


def cmin_edge(r, fixed, lo, hi):
    k = fixed*fixed-r*r
    if lo == 0 and k <= 0:
        return Q(-1)
    if k <= lo*lo:
        return (lo+k/lo)/(2*fixed)
    if k >= hi*hi:
        return (hi+k/hi)/(2*fixed)
    return I(k).sqrt().lo/fixed


def check_balanced(data):
    r, s0, t0, lam = lambda_enclosure(data)
    cfg = data["balanced"]
    hs = tuple(map(Q, cfg["hessian_s"]))
    ht = tuple(map(Q, cfg["hessian_t"]))
    wlo, whi = map(Q, cfg["lambda"])
    assert 0 < wlo < lam.lo <= lam.hi < whi
    assert hs[0] < s0.lo <= s0.hi < hs[1]
    assert ht[0] < t0.lo <= t0.hi < ht[1]
    hsi, hti = I(*hs), I(*ht)
    assert (r + hti).lo > 1-r.lo
    assert (r + hti).sq().hi < 1-r.hi**2
    assert (2*r.sq() + r + hsi).hi < 1
    assert (hsi+hti).lo > r.hi and (hti-hsi).hi < r.lo

    def h_test(box):
        try:
            return j_hessian(r, I(*box[0]), I(*box[1]), lam)
        except AssertionError:
            return False

    depth = cfg["max_depth"]
    n_h = box_verify((hs, ht), h_test, depth)
    rplus, rminus = r.hi, r.lo
    rr = rplus**2
    smax = 1-rminus
    dmax2 = 1-rr
    target = (1+wlo)*PI.lo/3
    tmin = Q(cfg["t_min"])
    assert tmin == Q("0.311")
    amax_c = I(dmax2).sqrt().lo
    alpha_cap_c = (1+(rplus+tmin)**2-rr)/(2*(rplus+tmin))
    assert cos_upper(3030) < alpha_cap_c
    assert Q(3030, H) + 8*Q("0.3695") < PI.lo
    assert rplus+tmin < amax_c
    mesh = 2**18

    @lru_cache(maxsize=None)
    def a_u(t):
        d = min(1, rplus+t)
        c = amax_c if d*d >= dmax2 else (1+d*d-rr)/(2*d)
        return Q(angle_upper(c, mesh), mesh)

    @lru_cache(maxsize=None)
    def h_u(s):
        b2 = rr+rplus+s
        c = amax_c if b2 >= dmax2 else (1+rplus+s)/(2*I(b2).sqrt().hi)
        return Q(angle_upper(c, mesh), mesh)

    @lru_cache(maxsize=None)
    def g_u_below(s, l, u):
        if s == 0:
            return PI.hi
        return Q(angle_upper(cmin_edge(rplus, s, l, u), mesh), mesh)

    def below(box):
        ((sl, su), (ql, qu), (tl, tu)) = box
        if sl > qu:
            return True
        k = max(0, rminus*rminus-tu*tu)
        if su*qu < k:
            return True
        if k > 0:
            sl, ql = max(sl, k/qu), max(ql, k/su)
        if min(su,qu)+rplus < tl or max(sl,ql) > rplus+tu:
            return True
        g = min(PI.hi, g_u_below(sl, tl, tu)+g_u_below(ql, tl, tu))
        return a_u(tu)+whi*g/2+h_u(su)+h_u(qu) < target

    n_b = box_verify(((Q(0), smax), (Q(0), smax), (tmin, rplus)), below, depth)

    def above(box):
        ((sl, su), (tl, tu)) = box
        if rplus+su < tl or sl > rplus+tu:
            return True
        if hs[0] <= sl and su <= hs[1] and ht[0] <= tl and tu <= ht[1]:
            return True
        tu = min(tu, rplus+su)
        if sl == 0:
            g = PI.hi/2
        else:
            c = min(cmin_edge(rplus, fixed, low, high)
                    for fixed, low, high in (
                        (sl, tl, tu), (su, tl, tu), (tl, sl, su), (tu, sl, su)))
            g = min(PI.hi/2, Q(angle_upper(c, mesh), mesh))
        return a_u(tu)+whi*g+2*h_u(su) < target

    aboxes = [(x,y) for x,y in zip((Q(0),*hs),(*hs,smax),strict=True)]
    bbox = [(x,y) for x,y in zip((rminus,*ht),(*ht,Q(1)),strict=True)]
    n_a = sum(box_verify((si,ti), above, depth) for si in aboxes for ti in bbox)
    print(f"PASS: balanced inequality; leaves hessian={n_h}, low={n_b}, high={n_a}")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O.")
    certificate = json.loads(Path("certificate12.json").read_text(encoding="ascii"))
    check_construction(certificate)
    check_local(certificate)
    check_arc_tests(certificate)
    check_small_inner(certificate)
    check_balanced(certificate)
