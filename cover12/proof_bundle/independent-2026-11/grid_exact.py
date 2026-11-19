"""Finite integer terms of the exact radius series and optimal-center limit."""
from fractions import Fraction
from functools import lru_cache
from math import isqrt, prod
import argparse


def lattice(m):
    centers = [(x, y) for x in range(-m, m) for y in range(-m, m)]
    witnesses = [
        (x, y)
        for x in range(-m, m+1)
        for y in range(-isqrt(m*m-x*x), isqrt(m*m-x*x)+1)
    ]
    return centers, witnesses


def inclusion_exclusion(centers, witnesses, j):
    """Collect the signed terms by the union of forbidden center indices."""
    total = {0: 1}
    for x, y in witnesses:
        mask = 0
        for i, (a, b) in enumerate(centers):
            if (a-x)**2+(b-y)**2 <= j*j:
                mask |= 1 << i
        if not mask:
            return {}
        updated = total.copy()
        for forbidden, coefficient in total.items():
            merged = forbidden | mask
            updated[merged] = updated.get(merged, 0) - coefficient
        total = {mask: weight for mask, weight in updated.items() if weight}
    return total


def count_covers(terms, allowed):
    return sum(
        coefficient * prod((mask & ~forbidden).bit_count() for mask in allowed)
        for forbidden, coefficient in terms.items()
    )


def grid_cover_exists(centers, witnesses, j):
    """Decide positivity of the count by branching on an uncovered point."""
    count = len(witnesses)
    full = (1 << count)-1
    masks = {
        sum(
            1 << i for i, (x, y) in enumerate(witnesses)
            if (a-x)**2+(b-y)**2 <= j*j
        )
        for a, b in centers
    } - {0}
    if not masks or 12*max(mask.bit_count() for mask in masks) < count:
        return False
    choices = [
        tuple(mask for mask in masks if mask & (1 << i))
        for i in range(count)
    ]
    if not all(choices):
        return False
    order = sorted(range(count), key=lambda i: len(choices[i]))

    greedy = full
    for _ in range(12):
        greedy &= ~max(masks, key=lambda mask: (mask & greedy).bit_count())
        if not greedy:
            return True

    @lru_cache(maxsize=100_000)
    def search(remaining, disks):
        if not remaining:
            return True
        if not disks:
            return False
        if disks*max((mask & remaining).bit_count() for mask in masks) < remaining.bit_count():
            return False
        i = next(i for i in order if remaining & (1 << i))
        branches = {mask & remaining for mask in choices[i]}
        return any(
            search(remaining ^ mask, disks-1)
            for mask in sorted(branches, key=int.bit_count, reverse=True)
        )

    return search(full, 12)


def series_term(k):
    m = 1 << k
    centers, witnesses = lattice(m)
    for j in range(m):
        if grid_cover_exists(centers, witnesses, j):
            return j
    return m


def center_key(k, j):
    m = 1 << k
    centers, witnesses = lattice(m)
    terms = inclusion_exclusion(centers, witnesses, j+4)
    allowed = [(1 << len(centers)) - 1]*12
    key_numerator = 0
    for bit in range(k, -1, -1):
        zero_masks = []
        for axis in (0, 1):
            zero_masks.append(sum(
                1 << i for i, center in enumerate(centers)
                if not ((center[axis]+m) & (1 << bit))
            ))
        for center_slot in range(12):
            for zero_mask in zero_masks:
                initial = allowed[center_slot]
                allowed[center_slot] = initial & zero_mask
                key_numerator *= 3
                if not allowed[center_slot] or not count_covers(terms, allowed):
                    allowed[center_slot] = initial & ~zero_mask
                    key_numerator += 2
    assert all(mask.bit_count() == 1 for mask in allowed)
    assert count_covers(terms, allowed) == 1
    return Fraction(key_numerator, 3**(24*(k+1)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k", type=int)
    parser.add_argument("--centers", action="store_true")
    args = parser.parse_args()
    if args.k < 0:
        parser.error('k must be nonnegative')
    j = series_term(args.k)
    print(f"J_{args.k} = {j}")
    if args.centers:
        print(f"kappa_{args.k} = {center_key(args.k, j)}")

