"""Exact rejection of exterior-count branches using weighted circle coverage."""

import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from math import acos, pi, sqrt
from pathlib import Path

from rational_trig import cos_upper, pi_bounds


ANGLES = 1 << 22
COS_SCALE = 10**15
PI_LOW = Q("3.141592653589793238462643")


@lru_cache(maxsize=None)
def cos_ceil(j):
    value = cos_upper(PI_LOW * j / ANGLES) * COS_SCALE
    return -((-value.numerator) // value.denominator)


def cos_min(s, r, lo, hi):
    """Return u or u^2, with a flag for the nonnegative square-root case."""
    if lo == 0 and s <= r:
        return Q(-1), False
    if hi == 0:
        return Q(1), False
    d = s * s - r * r
    if lo * lo >= d:
        t = lo
    elif hi * hi <= d:
        t = hi
    else:
        return d / (s * s), True
    return (t * t + d) / (2 * s * t), False


def angular_units(value, radical):
    if not radical and value >= 1:
        return 0
    if value <= -1:
        return ANGLES
    # Floating point only suggests an index. A rational comparison checks it.
    hint = sqrt(float(value)) if radical else float(value)
    j = min(ANGLES, 1 + int(ANGLES * acos(max(-1, min(1, hint))) / pi))
    while j < ANGLES:
        c = cos_ceil(j)
        if radical:
            good = c <= 0 or value.numerator * COS_SCALE**2 >= c * c * value.denominator
        else:
            good = value.numerator * COS_SCALE >= c * value.denominator
        if good:
            return j
        j += 1
    return ANGLES


def bound(s, r, lo, hi):
    return angular_units(*cos_min(s, r, lo, hi))


def verify_group(weights, r, lo, hi, budget):
    cap = budget * ANGLES * sum(w for _, w in weights)
    passed = 0
    pending = [(lo, hi, 0)]
    while pending:
        a, b, depth = pending.pop()
        if sum(w * bound(s, r, a, b) for s, w in weights) <= cap:
            passed += 1
            continue
        if depth >= 22:
            raise ValueError(f"Budget not verified on [{float(a):.9f}, {float(b):.9f}]")
        mid = (a + b) / 2
        pending.extend(((a, mid, depth + 1), (mid, b, depth + 1)))
    return passed


def verify(data):
    k = data["k"]
    rmin, rmax = Q(data["r_min"]), Q(data["r_max"])
    weights = [(Q(s), w) for s, w in data["weights"]]
    budgets = list(map(Q, data["caps"]))
    counts = [1, 25 - k, k]
    if not (0 <= k < 26 and 0 < rmin <= rmax < Q(1, 2)):
        raise ValueError("Invalid branch")
    if not (weights and all(0 < s <= 1 and isinstance(w, int) and w > 0 for s, w in weights)):
        raise ValueError("Expected positive integer weights on positive circle radii")
    if len(budgets) != 3 or not all(0 <= b <= 1 for b in budgets):
        raise ValueError("Expected three normalized budgets")
    total = sum(c * b for c, b in zip(counts, budgets))
    if total >= 1:
        raise ValueError("The combined budget must be strictly smaller than 1")
    intervals = [(Q(0), rmax), (Q(0), 1 - rmin), (1 - rmax, Q(1))]
    boxes = [verify_group(weights, rmax, a, b, cap)
             for (a, b), cap in zip(intervals, budgets)]
    print(f"PASS k={k}, r in [{float(rmin):.10g}, {float(rmax):.10g}], "
          f"weighted sum <= {float(total):.12f}, boxes={boxes}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    if not 0 < PI_LOW <= pi_bounds()[0]:
        raise ValueError("The lower bound for pi failed")
    for item in json.loads(args.certificate.read_text(encoding="utf-8")):
        verify(item)


if __name__ == "__main__":
    main()
