"""Enumerate the surviving outer-chord sets for b=15,16,17."""

from collections import Counter
from fractions import Fraction as Q
import argparse
import json
from pathlib import Path

from rational_trig import cos_lower, cos_upper, pi_bounds, sin_lower, sin_upper
from verify_belt_pruning import SCALE
from verify_cycles14 import bits
from verify_fan import c_bounds, fan_line, require
from verify_patch14 import ARC_CAP, RADIUS
from verify_seam import seam_upper


ARC_LIMITS = (ARC_CAP, Q(".978"), Q("1.56232"), Q("2.44"))


def crosses(edge, other, n):
    i, j = edge
    u, v = other
    if len({i, j, u, v}) < 4:
        return False
    return (0 < (u - i) % n < (j - i) % n) != (0 < (v - i) % n < (j - i) % n)


def closure_add(dist, i, j, weight):
    if dist[j][i] + weight > 0:
        return None
    if dist[i][j] >= weight:
        return dist
    return [[max(x, row[i] + weight + y) for x, y in zip(row, dist[j])] for row in dist]


def path_constraints(adj, dist, total):
    n = len(adj)
    reach = [adj]
    for _ in range(2):
        prev = reach[-1]
        layer = []
        for row in prev:
            to = 0
            for i in bits(row):
                to |= adj[i]
            layer.append(to)
        reach.append(layer)
    for i in range(n):
        a = (i - 1) % n
        for s in range(2, n // 2 + 1):
            j = (i + s) % n
            target = (1 << j) | (1 << ((j - 1) % n))
            for k, paths in enumerate(reach, start=1):
                if (paths[i] | paths[a]) & target:
                    deficit = int(SCALE * (s * ARC_CAP - ARC_LIMITS[k]))
                    if deficit > 0:
                        dist = closure_add(dist, i, j, deficit - (total if i + s >= n else 0))
                        if dist is None:
                            return None
                    break
    return dist


def canonical(edges, n):
    return min(tuple(sorted(
        tuple(sorted(((a + t * i) % n, (a + t * j) % n))) for i, j in edges
    )) for a in range(n) for t in (1, -1))


def enumerate_chords(n, total, max_span=None, representatives=False):
    span = n - 13 if max_span is None else max_span
    candidates = [(i, (i + d) % n) for d in range(span, 1, -1) for i in range(n)]
    adj = [(1 << i) | (1 << ((i - 1) % n)) | (1 << ((i + 1) % n)) for i in range(n)]
    dist = [[0 if i <= j else -total for j in range(n)] for i in range(n)]
    paths = []
    rooted, classes = Counter(), set()

    def visit(start, d):
        rooted[len(paths)] += 1
        classes.add(canonical(paths, n))
        for k in range(start, len(candidates)):
            u, v = candidates[k]
            if any(crosses((u, v), p, n) for p in paths):
                continue
            # Cheap single-chord test before computing all graph shortcuts.
            s = (v - u) % n + 1
            weight = int(SCALE * (s * ARC_CAP - ARC_LIMITS[1]))
            end = (u + s) % n
            updated = closure_add(d, u, end, weight - (total if u + s >= n else 0))
            if updated is None:
                continue
            adj[u] |= 1 << v
            adj[v] |= 1 << u
            checked = path_constraints(adj, updated, total)
            if checked is not None:
                paths.append((u, v))
                visit(k + 1, checked)
                paths.pop()
            adj[u] ^= 1 << v
            adj[v] ^= 1 << u

    visit(0, dist)
    return rooted, sorted(classes) if representatives else Counter(map(len, classes))


def verify_seventeen_neighbor_span():
    # Seven arcs between two exterior neighbors of the same interior site
    # have half-angle sum at most asin(3R). The ten other arcs are nearly full.
    pi0, _ = pi_bounds()
    lam, tau = Q(".2604"), Q(".1246")
    block_sum = Q(".7811592")
    require(sin_lower(block_sum) > 3 * RADIUS and 2 * pi0 - 7 * ARC_CAP > 2 * block_sum,
            "Invalid seven-arc angle reduction")
    lo, hi = c_bounds(lam)
    _, arc_hi = c_bounds(lam - tau)
    offset = 2 * arc_hi + seam_upper(lam, tau, 2) - 4 * lo
    a, c, d = Q("-.23051941"), Q("13.30748856"), Q("-59.502711")
    first, _ = fan_line(RADIUS, lam - tau, a, Q(0), offset=offset)
    second, _ = fan_line(RADIUS, lam - tau, c, d, offset=offset)
    require(52 * lam - 2 * tau + d < 0, "Wrong sign for pi enclosure")
    area = RADIUS**2 * (
        (52 * lam - 2 * tau + d) * pi0 + 150 * hi + 7 * a + 10 * c - d * block_sum
    )
    require(area < pi0, "The seven-arc shortcut was not excluded")
    print(f"PASS b=17, shared interior neighbor across six steps: "
          f"area <= {float(area):.12f}, boxes={[first, second]}")


def verify_tight_neighbor_spans():
    # Both edges to the shared site are long. None is an exterior seam edge.
    pi0, pi1 = pi_bounds()
    half, wedge = Q(".7811592"), Q(".46027")
    h = sin_lower(pi0 - 5*ARC_CAP) / RADIUS - 2
    require(h > cos_upper(wedge/2), "The ordinary straight wedges are not short")
    require(sin_lower(half) > 3*RADIUS and 2*pi0 - 6*ARC_CAP > 2*half,
            "Invalid shared-neighbor half-angle upper bound")
    for b, lam, tau, a, d, c, e in (
        (15, Q(".2535"), Q(".05"), Q("-.07754809"), Q("-.728986"),
         Q("14.80653953"), Q("-66.124509")),
        (16, Q(".258"), Q(".104"), Q("-.21999959"), Q(0),
         Q("13.71020331"), Q("-61.28273")),
    ):
        require(cos_lower(wedge) > 2*lam and d > e, "Invalid straight-wedge maximizer")
        lo, hi = c_bounds(lam)
        _, arc_hi = c_bounds(lam - tau)
        offset = 2*arc_hi + seam_upper(lam, tau, 2) - 4*lo
        x, _ = fan_line(RADIUS, lam-tau, a, d, offset=offset)
        y, _ = fan_line(RADIUS, lam-tau, c, e, offset=offset)
        loss = lo - (sin_upper(wedge)/2 - lam*wedge)
        require(loss > 0, "No loss on the ordinary wedges")
        p = 52*lam - 2*tau + e
        area = RADIUS**2 * (p * (pi0 if p <= 0 else pi1) + 150*hi
                            + (b-10)*a + 10*c + (d-e)*half - 4*loss)
        require(area < pi0, "The 26-disk shortcut was not excluded")
        print(f"PASS n=26 b={b}, shared interior neighbor across {b-11} steps: "
              f"area <= {float(area):.12f}, boxes={[x, y]}")


def verify_reduced_neighbor_spans():
    # With 25 disks the analogous raw fan estimate already suffices.
    pi0, _ = pi_bounds()
    lam, block_sum = Q(".25"), Q(".7811592")
    require(sin_lower(block_sum) > 3 * RADIUS and 2 * pi0 - 6 * ARC_CAP > 2 * block_sum,
            "Invalid half-angle bound on a shared-neighbor interval")
    a, b = Q("15.83838823"), Q("-70.67307")
    long_boxes, c = fan_line(RADIUS, lam, a, b)
    for m, a0, b0 in ((5, Q(".03312049"), Q("-1.25182")),
                      (6, Q("-.14793622"), Q(0))):
        boxes, _ = fan_line(RADIUS, lam, a0, b0)
        require(50 * lam + b < 0 and b0 > b, "Invalid signs for the area substitution")
        area = RADIUS**2 * (
            (50 * lam + b) * pi0 + 144 * c + m * a0 + 10 * a + (b0 - b) * block_sum
        )
        require(area < pi0, "The 25-disk shortcut was not excluded")
        print(f"PASS n=25 b={m+10}, shared interior neighbor across {m-1} steps: "
              f"area <= {float(area):.12f}, boxes={[boxes, long_boxes]}")


def verify_reduced_chords():
    pi0, pi1 = pi_bounds()
    half = Q(".4888")
    require(sin_lower(half) > 2 * RADIUS, "Invalid chord half-angle upper bound")
    # At most two chords for b=15. If there are two, their three-arc
    # windows overlap on exactly one arc. For b=16 test a three-step chord.
    for b, lam, tau, small, large, short_count, long_count, shared in (
        (16, Q(".2495"), Q(".172"), (Q("-.25274371"), Q(0)),
         (Q("1.52390532"), Q("-8.753276")), 4, 12, None),
        (15, Q(".2591"), Q(".1597"), (Q(".75109415"), Q("-5.219109")),
         (Q("1.92544515"), Q("-10.620135")), 4, 10, Q("-.27651426")),
    ):
        lo, hi = c_bounds(lam)
        _, arc_hi = c_bounds(lam - tau)
        offset = 2 * arc_hi + seam_upper(lam, tau, 2) - 4 * lo
        a, d = small
        c, e = large
        counts = [fan_line(RADIUS, lam - tau, z, q, offset=offset)[0]
                  for z, q in (small, large)]
        require(d > e, "Invalid chord area signs")
        extra = (d - e) * half
        if shared is not None:
            # Other four arcs have sum <= 2*(half-shared_angle).
            extra = 2 * extra + shared
            counts.append(fan_line(RADIUS, lam - tau, shared, 2 * d - e, offset=offset)[0])
        p = 50 * lam - 2 * tau + e
        area = RADIUS**2 * (
            p * (pi0 if p <= 0 else pi1) + 144 * hi
            + short_count * a + long_count * c + extra
        )
        require(area < pi0, "The 25-disk chord pattern was not excluded")
        print(f"PASS n=25 b={b}, {'two chords' if shared is not None else 'three-step chord'}: "
              f"area <= {float(area):.12f}, boxes={counts}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--classes", type=Path)
    args = parser.parse_args()
    pi0, _ = pi_bounds()
    require(int(2 * pi0 * SCALE) == 6283185, "C++ angular budget uses an incorrect pi enclosure")
    require(2 * pi0 - 8 * ARC_CAP > ARC_LIMITS[-1], "The complementary arc can be short")
    require(sin_lower(pi0 - 11 * ARC_CAP / 2) > 2 * RADIUS,
            "Long boundary chords not excluded")
    for k, c in enumerate(ARC_LIMITS, start=1):
        require(c < pi0 and sin_lower(c / 2) > k * RADIUS, "Invalid path-angle cap")
        require((c * SCALE).denominator == 1, "A path-angle cap would be rounded")
    domains = []
    for b in (15, 16, 17):
        s = (b * ARC_CAP - 2 * pi0) * SCALE
        total = -((-s.numerator) // s.denominator)
        roots, reps = enumerate_chords(b, total, representatives=True)
        classes = Counter(map(len, reps))
        domains.append({"n": 26, "b": b, "classes": reps})
        print(f"PASS b={b} rooted={sum(roots.values())} dihedral_classes={sum(classes.values())}")
        print("chords/rooted/classes", [(k, roots[k], classes[k]) for k in sorted(roots)])
    verify_seventeen_neighbor_span()
    verify_tight_neighbor_spans()
    verify_reduced_neighbor_spans()
    verify_reduced_chords()
    s = (16 * ARC_CAP - 2 * pi0) * SCALE
    roots, reps = enumerate_chords(16, -((-s.numerator) // s.denominator), 2, True)
    print(f"PASS n=25 b=16 with two-step chords only, rooted={sum(roots.values())}, "
          f"dihedral_classes={len(reps)}")
    domains.extend([{"n": 25, "b": 15, "classes": [[], [[0, 2]]]},
                    {"n": 25, "b": 16, "classes": reps}])
    if args.classes:
        args.classes.write_text(json.dumps(domains, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
