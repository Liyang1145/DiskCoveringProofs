"""Certify the exclusion of 10 and 11 boundary disks at two test radii."""

from functools import lru_cache
from itertools import product

from interval import Interval as I, PI, SCALE, asin


def ends(box):
    return I.endpoints(box.lo, box.lo), I.endpoints(box.hi, box.hi)


def clamp(box, lo, hi):
    return I.endpoints(max(lo, min(hi, box.lo)), max(lo, min(hi, box.hi)))


def maximum(a, b):
    return I.endpoints(max(a.lo, b.lo), max(a.hi, b.hi))


@lru_cache(maxsize=16384)
def width_cached(slo, shi, dlo, dhi, rfixed):
    s, d, r = I.endpoints(slo, shi), I.endpoints(dlo, dhi), I.endpoints(rfixed, rfixed)
    overlap = r.square() - (s-d).square()
    if overlap.hi <= 0 or d.hi == 0:
        return I(0)
    assert s.lo > r.hi and d.lo > 0
    x2 = clamp(clamp(overlap, 0, overlap.hi) / (4*s*d), 0, SCALE)
    return 2 * asin(x2.sqrt())


def width(s, d, r):
    return width_cached(s.lo, s.hi, d.lo, d.hi, r.lo)


def radial_max(s, d, r):
    mode = (s.square() - r.square()).sqrt()
    return width(s, clamp(mode, d.lo, d.hi), r)


def tail_max(s, d, r):
    # max_{rho >= s, p in d} w(rho, p), with s fixed and s > r.
    mode = (s.square() - r.square()).sqrt()
    p = clamp(mode, d.lo, d.hi)
    mode_rho2 = p.square() - r.square()
    rho = maximum(s, clamp(mode_rho2, 0, max(0, mode_rho2.hi)).sqrt())
    return width(rho, p, r)


@lru_cache(maxsize=16384)
def gap_cached(sfixed, rfixed):
    return 2 * asin(I.endpoints(rfixed, rfixed) / I.endpoints(sfixed, sfixed))


def gap(s, r):
    assert s.lo == s.hi
    return gap_cached(s.lo, r.lo)


def gap_range(s, r):
    left, right = ends(s)
    return I.endpoints(gap(right, r).lo, gap(left, r).hi)


def verify_boxes(bounds, upper, domain):
    """Bisect closed boxes until an upper bound covers each one."""
    todo = [(tuple(domain), 0)]
    visited = 0
    while todo:
        box, depth = todo.pop()
        visited += 1
        value = upper(*box)
        if value is None or value.hi <= bounds.lo:
            continue
        assert depth < 60, (box, value, bounds)
        k = max(range(len(box)), key=lambda j: box[j].hi - box[j].lo)
        lo, hi = box[k].lo, box[k].hi
        mid = (lo + hi) // 2
        assert lo < mid < hi
        for part in (I.endpoints(lo, mid), I.endpoints(mid, hi)):
            todo.append((box[:k] + (part,) + box[k+1:], depth+1))
    return visited


def outer_domain(r):
    return I.endpoints((1-r).lo, (1-r.square()).sqrt().hi)


def gap_budget(n, marked, r, cutoff, weight, bound):
    ds = outer_domain(r)
    lam = asin(r)
    assert (9 * lam - PI).hi < 0
    assert r.hi * 3 < SCALE
    assert ((n-marked)*lam+marked*bound - (PI+weight*(2*PI-cutoff))).hi < 0
    return verify_boxes(bound, lambda d: radial_max(I(1), d, r) + weight*gap(ends(d-r)[0], r), [ds])


def ten_arcs_three_marks(r):
    return gap_budget(10, 3, r, I(0), I(".206"), I(".633"))


def arc_partials(s, d, r):
    """Partial derivative enclosures on boxes away from disk tangencies."""
    c = (s.square()+d.square()-r.square())/(2*s*d)
    sine2 = 1-c.square()
    if sine2.lo <= 0:
        return None
    sine = sine2.sqrt()
    ds = (d.square()-s.square()-r.square())/(2*s.square()*d*sine)
    dd = (s.square()-d.square()-r.square())/(2*s*d.square()*sine)
    return ds, dd


def sector_bound(r, sbox, dbox, a, b, c, limit):
    def one_var(d):
        return a*radial_max(I(1), d, r) + c*gap(ends(d-r)[0], r)

    if b.hi == 0:
        if c.hi < 0:
            assert (a*asin(r) + c*gap(ends(sbox)[1], r)).hi < limit.lo
            return 1
        # s >= d-r, and the coefficient of 2 asin(r/s) is positive.
        return verify_boxes(limit, one_var, [dbox])

    assert c.lo >= 0

    def two_vars(s, d):
        if d.lo > (s+r).hi:
            return None
        d = I.endpoints(d.lo, min(d.hi, (s+r).hi))
        s = I.endpoints(max(s.lo, (d-r).lo), s.hi)
        left = ends(d)[0]
        # Here s < d, so w(s,d) is nonincreasing in d.
        bound = a*radial_max(I(1), d, r) + b*radial_max(left, s, r) + c*gap(ends(s)[0], r)
        if bound.hi <= limit.lo:
            return bound

        outer = arc_partials(I(1), d, r)
        inner = arc_partials(s, d, r)
        if outer is None or inner is None:
            return bound
        derivative_s = b*inner[0] - c*2*r/(s*(s.square()-r.square()).sqrt())
        derivative_d = a*outer[1] + b*inner[1]
        sm, dm = s.midpoint(), d.midpoint()
        value = a*width(I(1), dm, r) + b*width(sm, dm, r) + c*gap(sm, r)
        taylor = value + derivative_s*(s-sm) + derivative_d*(d-dm)
        return I.endpoints(min(bound.lo, taylor.lo), min(bound.hi, taylor.hi))

    return verify_boxes(limit, two_vars, [sbox, dbox])


def sector_support(r, sbox, dbox, alpha, tau, limits):
    count = 0
    checked = set()
    for j, p in enumerate(alpha):
        q = alpha[j-1]
        a = p+q
        b = maximum(p-q, q-p)
        c = tau-a/2
        bound = limits[j]
        key = a.lo, b.lo, c.lo, bound.lo
        if key not in checked:
            count += sector_bound(r, sbox, dbox, a, b, c, bound)
            checked.add(key)
    return count


def sector_slack(r, alpha, tau, limits, k, ell=None, cutoff=None):
    slack = sum(limits) + 2*asin(r)*sum(kj*aj for kj, aj in zip(k, alpha)) - 2*PI*tau
    if ell is not None:
        slack += cutoff * sum(lj*maximum(I(0), tau-aj) for lj, aj in zip(ell, alpha))
    return slack


def ten():
    r = I(".3291")
    dbox = outer_domain(r)
    dstar = (1-r.square()).sqrt()
    assert gap(ends(dstar-r)[0], r).hi < I("1.13").lo
    assert I("1.13").lo > (PI/3).hi
    count = gap_budget(10, 3, r, I("1.13"), I(".19"), I(".590"))
    print("10 boundary disks: small gap excluded,", count, "boxes", flush=True)

    sbox = I.endpoints((1-r*2).lo, I(".616").hi)
    assert (dstar-r).hi < sbox.hi < dbox.lo
    cases = [
        # Rotate a largest k to the last slot when max(k) >= 3.
        ("max(k) >= 3", [0, 0, 3, 3], ["1", "1", "1", "0"], ".936",
         ["1.276", ".601", ".601", "1.276"]),
        ("(0,2,2,2)", [0, 2, 2, 2], ["1", ".707", ".820", ".707"], "1.090",
         [".911", ".911", ".971", ".971"]),
        ("(1,1,2,2)", [1, 1, 2, 2], ["1", "1", ".843127", ".843127"], "1.217151",
         ["1.00725", ".93565", "1.00725", "1.09310"]),
        ("(1,2,1,2)", [1, 2, 1, 2], ["1", ".729", "1", ".729"], "1.190",
         ["1.038"]*4),
    ]
    for name, k, alpha, tau, limits in cases:
        alpha, tau, limits = list(map(I, alpha)), I(tau), list(map(I, limits))
        assert sector_slack(r, alpha, tau, limits, k).hi < 0, name
        count = sector_support(r, sbox, dbox, alpha, tau, limits)
        print("10 boundary disks:", name, "excluded,", count, "boxes", flush=True)


def paired_budget(r, circles, weight, buffer, pmax, lost_gap, regular, edges):
    """Regular is (count, bound). Each edge is (inner degree, count, bound)."""
    dbox = outer_domain(r)
    circles = [(I(s), I(z)) for s, z in circles]
    weight = I(weight)
    reg_count, reg_bound = regular
    upper = reg_count*I(reg_bound) + sum(count*I(bound) for _, count, bound in edges)
    required = PI*sum(z for s, z in circles) + weight*(2*PI-lost_gap)
    assert (upper-required).hi < 0

    def circle_score(d):
        return sum(z*radial_max(s, d, r) for s, z in circles)

    count = verify_boxes(I(reg_bound), circle_score, [dbox])
    for degree, _, bound in edges:
        def pair_score(p, d):
            s = ends(d-r)[0]
            return circle_score(p)/degree + circle_score(d)/2 + weight*maximum(buffer, tail_max(s, p, r))

        count += verify_boxes(I(bound), pair_score, [I.endpoints(0, pmax.hi), dbox])
    return count


def eleven():
    r = I(".3295")
    count = gap_budget(11, 2, r, PI/3, I(1), I("2.633"))
    print("11 boundary disks: small gap excluded,", count, "boxes", flush=True)
    count = paired_budget(r, [(".51", ".059"), (".55", ".042"), (".59", ".022"), (1, 1)],
                          ".337", PI/6, 1-r, I(0), (8, ".33642"), [(2, 6, ".49195")])
    print("11 boundary disks: coupled inner and marked disks certified,", count, "boxes", flush=True)


def orientations(ell, k):
    for a, b in ((ell, k), (ell[::-1], k[::-1])):
        for i in range(len(a)):
            yield a[i:]+a[:i], b[i:]+b[:i]


def high_classification():
    """Uniform geometric pruning above the lower bound and below the construction."""
    r = I(".331733")
    low = I(".3291")
    ds = outer_domain(r)
    ss = I.endpoints((1-2*r).lo, I(".621").hi)
    assert (low/r-I(".99")).lo > 0
    assert (1-2*low.square()).hi < I(".81").lo
    assert 3*r.hi < SCALE and (9*asin(r)-PI).hi < 0
    dlow = (1-low.square()).sqrt()
    assert ((r/low)*dlow-r).hi < ss.hi < ds.lo
    assert (gap(ends(dlow-low)[1], low)-PI/3).lo > 0
    dstar = (1-r.square()).sqrt()
    small = gap_range(dstar-r, r)
    biggest = gap(1-2*r, r)
    assert (3*small+biggest-2*PI).hi < 0

    for k, alpha, tau, limits in [
        ([0, 0, 3, 3], ["1", "1", "1", "0"], ".936", ["1.316", ".605", ".605", "1.316"]),
        ([0, 2, 2, 2], ["1", ".7085", ".8193", ".7085"], "1.0656",
         [".8897", ".8897", ".9439", ".9439"]),
    ]:
        alpha, tau, limits = list(map(I, alpha)), I(tau), list(map(I, limits))
        assert sector_slack(r, alpha, tau, limits, k).hi < 0
        sector_support(r, ss, ds, alpha, tau, limits)
    print("Near the upper bound, 10 outer disks and 4 large gaps:",
          "(1,1,2,2) or (1,2,1,2) up to dihedral order.", flush=True)

    short_cases = [
        (2, ["1", ".7596"], "1.2461", ["1.1319", "1.1319"],
         {((1, 1), (4, 4))}),
        (3, ["1", ".472", ".8693"], "1.0421", [".7795", "1.0119", "1.0978"],
         {((0, 0, 1), (1, 2, 4)), ((0, 0, 1), (2, 2, 3))}),
    ]
    for q, alpha, tau, limits, allowed in short_cases:
        alpha, tau, limits = list(map(I, alpha)), I(tau), list(map(I, limits))
        sector_support(r, ss, ds, alpha, tau, limits)
        remaining = set()
        for ell in product(range(5-q), repeat=q):
            if sum(ell) != 4-q:
                continue
            for k in product(range(11-q), repeat=q):
                if sum(k) != 10-q:
                    continue
                orbit = set(orientations(ell, k))
                if all(sector_slack(r, alpha, tau, limits, b, a, small).hi >= 0 for a, b in orbit):
                    remaining.add(min(orbit))
        assert remaining == allowed, remaining
        print("Near the upper bound, 10 outer disks and", q,
              "large gaps, remaining (ell, k):", sorted(remaining), flush=True)

    gap_budget(10, 2, r, PI/3+small, I(".203"), I(".627"))
    count = paired_budget(r, [(".54", ".048"), (".58", ".020"), (".63", ".006"), (1, 1)],
                          ".298", PI/6, 1-low, 2*small, (8, ".3394"), [(1, 4, ".451")])
    print("Near the upper bound, 10 outer disks and 2 large gaps excluded,", count, "boxes", flush=True)

    gap_budget(11, 2, r, I(".8"), I(".382"), I("1.092"))
    buffer = I(".61")
    assert (buffer-PI/6).lo > 0
    assert (I(".8")+buffer-biggest/2).lo > 0
    assert (2*PI-biggest-small-2*buffer).lo > 0
    count = paired_budget(r, [(".54", ".101"), (1, 1)], ".356", buffer,
                          1-low, small, (9, ".3403"), [(1, 2, ".537"), (2, 2, ".537")])
    print("Near the upper bound, 11 outer disks and 2 large gaps excluded,", count, "boxes", flush=True)


if __name__ == "__main__":
    ten()
    eleven()
    high_classification()
    print("All lower-bound and classification checks passed.")
