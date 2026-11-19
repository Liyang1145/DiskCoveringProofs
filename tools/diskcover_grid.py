# SPDX-License-Identifier: MIT
"""Certified finite-grid enclosures for equal-circle covering of the closed unit disk.

G = {(x/k,y/k): integer x,y, x*x+y*y<=k*k}. Rounding both coordinates
toward zero keeps each point of D in D and moves it by at most sqrt(2)/k.
Let q be the finite n-center optimum with both customers and centers in G.
For any continuous cover, radially project exterior centers to D (which
does not increase distance to any x in D), then round them to G. This
proves q <= r_D(n)+sqrt(2)/k. Rounding a customer in D to G proves the
reverse inequality r_D(n) <= q+sqrt(2)/k for any optimal grid witness.
No floating-point arithmetic is used. Brackets remain valid if interrupted
by the search-node limit. Finer grids converge only if finite search completes.
"""
from fractions import Fraction
from math import isqrt


def _sqrt_bounds(x, digits=10**9):
    """Directed rational bounds on sqrt(x), for a nonnegative Fraction."""
    x = Fraction(x)
    a = isqrt(x.numerator * digits * digits // x.denominator)
    lo = Fraction(a, digits)
    return lo, lo if lo * lo == x else Fraction(a + 1, digits)


def _decide(d2, radius2, n, budget):
    """Return (witness or None, complete, nodes); None/complete means infeasible."""
    m = len(d2)
    masks = [sum(1 << j for j, d in enumerate(row) if d <= radius2) for row in d2]
    options = [[i for i, d in enumerate(row) if d <= radius2] for row in d2]
    order = sorted(range(m), key=lambda j: len(options[j]))
    full = (1 << m) - 1
    unseen, greedy = full, []
    for _ in range(n):
        i = max(range(m), key=lambda i: (masks[i] & unseen).bit_count())
        greedy.append(i)
        unseen &= ~masks[i]
        if not unseen:
            return greedy, True, 0

    failed = {}
    nodes = 0

    def search(u, k):
        nonlocal nodes
        if not u:
            return [], True
        if not k or failed.get(u, -1) >= k:
            return None, True
        if nodes >= budget:
            return None, False
        nodes += 1
        cov = [mask & u for mask in masks]
        if u.bit_count() > k * max(c.bit_count() for c in cov):
            return None, True
        # Every cover must include one of these choices for the selected point.
        # Equal gains are equivalent; strict subsets need not be eliminated.
        j = next(j for j in order if u & (1 << j))
        gains = {cov[i]: i for i in options[j]}
        for gain in sorted(gains, key=lambda g: (g.bit_count(), g), reverse=True):
            tail, complete = search(u ^ gain, k - 1)
            if tail is not None:
                return [gains[gain], *tail], True
            if not complete:
                return None, False
        failed[u] = k
        return None, True

    witness, complete = search(full, n)
    return witness, complete, nodes


def solve_grid(n: int, grid: int = 5, max_nodes: int = 20_000) -> dict:
    """Return a JSON-ready global radius bracket and covering witness.

    `grid` is the denominator of lattice coordinates; only 1..16 are
    accepted to cap the O(grid^4) distance table. A solution for at most
    n centers is a solution for n by repeating centers. Radius endpoints
    and witness coordinates are strings encoding exact rational numbers.
    """
    if not isinstance(n, int) or not 1 <= n <= 22:
        raise ValueError("n must be an integer in 1..22")
    if not isinstance(grid, int) or not 1 <= grid <= 16:
        raise ValueError("grid must be an integer in 1..16")
    if not isinstance(max_nodes, int) or max_nodes < 0:
        raise ValueError("max_nodes must be a nonnegative integer")

    k = grid
    g = [(x, y) for x in range(-k, k + 1) for y in range(-k, k + 1)
         if x * x + y * y <= k * k]
    d2 = [[(x - u)**2 + (y - v)**2 for u, v in g] for x, y in g]
    radii = sorted({d for row in d2 for d in row if d <= k*k})
    lo, hi = 0, len(radii) - 1
    origin = g.index((0, 0))
    witness, nodes = [origin], 0
    while lo < hi:
        mid = (lo + hi) // 2
        ws, complete, used = _decide(d2, radii[mid], n, max_nodes - nodes)
        nodes += used
        if not complete:
            break
        if ws is None:
            lo = mid + 1
        else:
            hi, witness = mid, ws

    den = k * k
    dlo, dhi = Fraction(radii[lo], den), Fraction(radii[hi], den)
    delta = _sqrt_bounds(Fraction(2, den))[1]
    area = _sqrt_bounds(Fraction(1, n))[0]
    lower = max(area, _sqrt_bounds(dlo)[0] - delta)
    upper = _sqrt_bounds(dhi)[1] + delta
    continuum_witness = witness
    if upper >= 1:
        upper, continuum_witness = Fraction(1), [origin]
    return {
        "n": n, "grid": grid, "grid_points": len(g), "nodes": nodes,
        "lower": str(lower), "upper": str(upper), "net_radius_upper": str(delta),
        "discrete_lower_squared": str(dlo), "discrete_upper_squared": str(dhi),
        "discrete_centers": [[str(Fraction(v, k)) for v in g[i]] for i in witness],
        "discrete_exact": lo == hi,
        "centers": [[str(Fraction(v, k)) for v in g[i]] for i in continuum_witness],
    }
