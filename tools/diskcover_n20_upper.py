# SPDX-License-Identifier: MIT
"""Exact rational n=20 upper certificate, with no optimality claim.

Use 20 fixed rational centers, interpreting the cited appendix's decimals
as exact rationals rather than as isolating intervals for the algebraic
candidate. Scale the unit disk to radius S and start with [-S,S]^2.
For a closed box disjoint from the disk, the exact minimum squared distance
from the origin to that box exceeds S^2. For a box whose furthest corner
from one fixed center is within radius R, the whole box is covered:
the pointwise squared distance in each axis is bounded by its furthest
endpoint value. All other boxes are split into four closed boxes whose
union equals the parent. No intersecting box is silently dropped.
"""
import json
from fractions import Fraction

_SOURCE_COMMIT = "089584973f41e6374ce110f6e5b5ee456df19352"
_SOURCE_SHA256 = "ec4225ed1673e442f6b5d0557ea8a1d346c1aba684e5a34d05a636fe85f27139"
_SOURCE_URL = (
    "https://github.com/VonEquinox/DiskCoveringSolve/blob/"
    f"{_SOURCE_COMMIT}/cover20/docs/r20_proof_zh.md"
)
_DECIMAL_SCALE = 10**16
_RADIUS_NUMERATOR = 2708481784399775
_DYADIC_SCALE = 2**60
_MAX_DEPTH = 58

# Signed appendix x/y numerators, in the source order, over 10**16.
_CENTER_NUMERATORS = (
    (7617842894801921, -1288875906586701),
    (8597634862054800, 2317163264921426),
    (6268784050608806, 6323837232594942),
    (2650464092341124, 7257256476635929),
    (-851044631734972, 9358949632083522),
    (-4529558377051876, 6816250964920982),
    (-8420364265321713, 4465315502693057),
    (-8311389636759451, -161521704539399),
    (-8255206229377350, -4798280040015983),
    (-4254017535328534, -7142032047266874),
    (-287578225179790, -9526745281768598),
    (3680937514274170, -7309505819405040),
    (7711008550466241, -5371644284175724),
    (-114040206443583, -66285060740247),
    (-173693563056216, -4792793404476318),
    (3886656761197333, -2509268941973634),
    (3879117347632483, 2254709431217756),
    (-256692069398766, 4619160160031496),
    (-4250547586098002, 2221234631945781),
    (-4175088493320303, -2426740559370644),
)


def _axis_min_sq(lo, hi):
    return 0 if lo <= 0 <= hi else min(lo*lo, hi*hi)


def _outside(box, target_sq):
    xlo, xhi, ylo, yhi = box
    return _axis_min_sq(xlo, xhi) + _axis_min_sq(ylo, yhi) > target_sq


def _covered(box, centers, radius_sq):
    xlo, xhi, ylo, yhi = box
    for x, y in centers:
        if (max((xlo-x)**2, (xhi-x)**2)
                + max((ylo-y)**2, (yhi-y)**2) <= radius_sq):
            return True
    return False


def _replay(centers, target, radius, max_depth):
    """Run exact integer-only checks; a depth-limit hit is a hard failure."""
    if target <= 0 or radius < 0 or max_depth < 0:
        raise ValueError("target, radius or depth outside supported range")
    target_sq, radius_sq = target**2, radius**2
    stack = [((-target, target, -target, target), 0)]
    counts = dict(visited=0, outside=0, covered=0, split=0, max_depth=0)
    while stack:
        box, depth = stack.pop()
        counts["visited"] += 1
        counts["max_depth"] = max(counts["max_depth"], depth)
        if _outside(box, target_sq):
            counts["outside"] += 1
            continue
        if _covered(box, centers, radius_sq):
            counts["covered"] += 1
            continue
        if depth >= max_depth:
            raise ArithmeticError(f"unresolved target box at depth {depth}: {box}")
        xlo, xhi, ylo, yhi = box
        if (xlo + xhi) % 2 or (ylo + yhi) % 2:
            raise ArithmeticError(f"nonintegral quadtree midpoint: {box}")
        xmid, ymid = (xlo + xhi)//2, (ylo + yhi)//2
        if not (xlo < xmid < xhi and ylo < ymid < yhi):
            raise ArithmeticError(f"degenerate quadtree split: {box}")
        counts["split"] += 1
        for a, b in ((xlo, xmid), (xmid, xhi)):
            for c, d in ((ylo, ymid), (ymid, yhi)):
                stack.append(((a, b, c, d), depth + 1))
    return counts


def check_n20_upper():
    """Replay the rational upper bound from scratch without network access."""
    if len(_CENTER_NUMERATORS) != 20 or len(set(_CENTER_NUMERATORS)) != 20:
        raise ArithmeticError("expected twenty distinct centers")
    centers = [(x*_DYADIC_SCALE, y*_DYADIC_SCALE) for x, y in _CENTER_NUMERATORS]
    checked = _replay(
        centers, _DECIMAL_SCALE*_DYADIC_SCALE,
        _RADIUS_NUMERATOR*_DYADIC_SCALE, _MAX_DEPTH,
    )
    upper = Fraction(_RADIUS_NUMERATOR, _DECIMAL_SCALE)
    return {
        "n": 20,
        "status": "certified_upper_only",
        "upper_exact": "0.2708481784399775",
        "upper_rational": str(upper),
        "upper_squared": str(upper**2),
        "center_numerators": [list(p) for p in _CENTER_NUMERATORS],
        "center_denominator": _DECIMAL_SCALE,
        "source": {
            "url": _SOURCE_URL,
            "commit": _SOURCE_COMMIT,
            "sha256": _SOURCE_SHA256,
            "role": "display decimals only, reinterpreted as exact rationals",
        },
        "checked": checked,
    }


if __name__ == "__main__":
    print(json.dumps(check_n20_upper(), indent=2))
