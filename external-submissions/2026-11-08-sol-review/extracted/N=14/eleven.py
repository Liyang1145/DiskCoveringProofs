"""Prune the remaining 11-boundary-disk cases near the construction."""

from interval import Interval as I, PI, asin
from lower import ends, gap, maximum, outer_domain, radial_max, tail_max, ten_arcs_three_marks, verify_boxes


TRIAL = I(".331733")
PMAX = I(".6709")
BUFFER = PI/6


def supremum_upper(f, domain, tol):
    """Upper bound within tol of an attained lower bound, by subdivision."""
    def sample(box):
        return f(box.midpoint()).lo

    lower = sample(domain)
    todo = [domain]
    while todo:
        box = todo.pop()
        upper = f(box).hi
        if upper <= lower + tol:
            continue
        lower = max(lower, sample(box))
        if upper <= lower + tol:
            continue
        mid = box.midpoint().lo
        assert box.lo < mid < box.hi
        todo.append(I.endpoints(box.lo, mid))
        todo.append(I.endpoints(mid, box.hi))
    return I.endpoints(lower+tol, lower+tol)


def score(r, circles, p):
    return sum(weight*radial_max(s, p, r) for s, weight in circles)


def ring_weights(rows):
    return [(I(s), I(w)) for s, w in rows]


def sector_certificate():
    r = TRIAL
    alpha = [1, 1, 0]
    tau = I("1.273")
    circles = ring_weights([(".48", ".14"), (".525", ".008"), (".55", ".028"),
                            (".575", ".018"), (".60", ".006"), (1, 1)])
    regular = I(".3395")
    caps = [I("2.39"), I("1.535"), I("2.39")]
    # Rotate any largest component of k to the last sector. If max(k) >= 4,
    # the first two components sum to at most 4.
    required = 2*PI*tau + PI*sum(weight for s, weight in circles)
    assert (8*regular + sum(caps) + 8*asin(r) - required).hi < 0
    outer = outer_domain(r)
    verify_boxes(regular, lambda p: score(r, circles, p), [outer])

    inner = I.endpoints(0, PMAX.hi)
    s_min = (1-2*r).lo
    s_max = I(".616").hi
    assert (1-I(".3291").square()).sqrt().hi-I(".3291").lo < s_max < outer.lo
    step = I(".001").lo
    tol = I(".002").lo
    checked = 0
    for low in range(s_min, s_max, step):
        high = min(low+step, s_max)
        s = I.endpoints(low, high)
        a = ends(s)[0]
        d = I.endpoints(outer.lo, min(outer.hi, (s+r).hi))

        def end_score(p, coefficient):
            return score(r, circles, p)/2 + coefficient*maximum(BUFFER, tail_max(a, p, r))

        p0 = supremum_upper(lambda p: end_score(p, tau), inner, tol)
        p1 = supremum_upper(lambda p: end_score(p, tau-1), inner, tol)
        for i, (left, right, bound) in enumerate(zip(alpha[-1:]+alpha[:-1], alpha, caps)):
            if i == 2:
                continue  # Same coefficients in reversed order as sector 0.
            a1, a2 = (p1 if left else p0), (p1 if right else p0)
            d1, d2 = left+right, abs(left-right)

            def middle_score(radial):
                value = score(r, circles, radial) + d1*radial_max(I(1), radial, r)
                if d2:
                    value += d2*radial_max(ends(radial)[0], s, r)
                return value

            checked += verify_boxes(bound-a1-a2, middle_score, [d])
    print("11 boundary arcs all essential: max(k) >= 4 excluded,", checked, "boxes.", flush=True)


def redundant_unmarked():
    count = ten_arcs_three_marks(TRIAL)
    print("11 boundary disks: redundant unmarked disk excluded,", count, "boxes.", flush=True)


def redundant_marked():
    r = TRIAL
    omega = I(".20780")
    inner_rings = ring_weights([(".40", ".01716"), (".48", ".05312"), (".51", ".04474"),
                                (".54", ".03063"), (".57", ".02897"), (".60", ".00578")])
    circles = inner_rings + [(I(1), I(1))]
    regular, omitted, kept = I(".33835"), I(".33845"), I(".4059")
    required = PI*sum(weight for s, weight in circles) + 2*PI*omega
    assert (8*regular + 2*omitted + 4*kept - required).hi < 0
    outer = outer_domain(r)
    inner = I.endpoints(0, PMAX.hi)
    count = verify_boxes(regular, lambda d: score(r, circles, d), [outer])
    for bound, marked_rings in [(omitted, inner_rings), (kept, circles)]:
        def pair(p, d):
            return ((score(r, inner_rings, p)+score(r, marked_rings, d))/2
                    + omega*maximum(BUFFER, tail_max(ends(d-r)[0], p, r)))

        count += verify_boxes(bound, pair, [inner, outer])
    print("11 boundary disks: redundant marked disk excluded,", count, "boxes.", flush=True)


def ear_certificate():
    """Combine disjoint two-step ear spans with the three marked gaps."""
    r = TRIAL
    marked = {0, 3, 7}
    types = [(e, a, m) for e, a in [(0, 0), (0, 1), (0, 2), (1, 0)] for m in (0, 1)]
    cases = {}
    for mask in range(1, 1 << 11):
        if mask & (mask << 1) or (mask & 1 and (mask >> 10) & 1):
            continue
        ears = {j for j in range(11) if (mask >> j) & 1}
        cases[mask] = [(int(j in ears), int((j-1) % 11 in ears)+int((j+1) % 11 in ears),
                        int(j in marked)) for j in range(11)]
    for weight, gap_weight, bounds in [
        (".7", ".24", [".677", ".979", ".702", "1.105", ".797", "1.411", ".204", ".685"]),
        (".9", ".28", [".677", "1.037", ".717", "1.287", ".942", "1.722", ".069", ".787"]),
        ("1", ".356", [".677", "1.159", ".726", "1.539", "1.04", "2.038", ".001", ".999"]),
        (".947", ".027", [".67636", ".70758", ".72006", ".76045", ".98565", "1.06072", ".03592", ".07948"]),
    ]:
        t, omega = I(weight), I(gap_weight)
        limits = dict(zip(types, map(I, bounds)))
        for (ear, adjacent, mark), bound in limits.items():
            a = 2-t*(2*ear+adjacent)
            b = t*adjacent
            c = omega*mark
            assert min(a.lo, b.lo, c.lo) >= 0

            def sup(d):
                low = ends(d)[0]
                return a*radial_max(I(1), d, r) + b*asin(r/low) + c*gap(low-r, r)

            verify_boxes(bound, sup, [outer_domain(r)])
        cases = {mask: row for mask, row in cases.items()
                 if (sum(limits[k] for k in row)-2*PI*(1+omega)).hi >= 0}
    two = sorted(mask for mask in cases if mask.bit_count() == 2)
    assert all(mask.bit_count() <= 2 for mask in cases)
    assert two == [5, 10], two
    print("11 boundary disks: at most two ears.")
    print("With marks at 0,3,7, surviving nonempty ear masks:", sorted(cases), flush=True)


if __name__ == "__main__":
    assert __debug__
    redundant_unmarked()
    redundant_marked()
    sector_certificate()
    ear_certificate()
