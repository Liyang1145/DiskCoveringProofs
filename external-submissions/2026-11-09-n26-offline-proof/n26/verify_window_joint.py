"""Exact fan-area and radial certificates for a forced short outer window."""

import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

from rational_trig import cos_lower, cos_upper, pi_bounds, sin_lower, sqrt_bounds
from verify_fan import c_bounds, require
from verify_joint import ArcEnvelope, group_caps
from verify_patch14 import ARC_CAP, RADIUS
from verify_radial import cos_min
from verify_seam import seam_upper


HALF = Q(".7811592")
SHARED_MIN, SHARED_MAX = Q(".6169"), Q(".8094")
LONG_MIN = Q(".9116")


@lru_cache(maxsize=1)
def geometry():
    r = RADIUS
    pi0, _ = pi_bounds()
    low = pi0 - 5 * ARC_CAP
    require(0 < low < HALF < pi0 / 2 and sin_lower(HALF) > 3*r,
            "Invalid angular range for the shared neighbor")
    require(2*pi0 - 6*ARC_CAP > 2*HALF, "The complementary interval can be short")
    _, root = sqrt_bounds(9*r*r - sin_lower(low)**2)
    require(cos_lower(HALF) - root > SHARED_MIN and cos_upper(low) + root < SHARED_MAX,
            "Unverified shared-neighbor norms")
    alpha = pi0 - HALF - Q(9, 2)*ARC_CAP
    require(0 < alpha < ARC_CAP/2, "Invalid long-arc half-angle")
    _, root = sqrt_bounds(r*r - sin_lower(alpha)**2)
    require(cos_lower(alpha) - root > LONG_MIN, "Unverified long-arc norm")


def groups(b, k, outside):
    """(number, lower norm, upper norm, arc type) for each nonempty group."""
    geometry()
    r = RADIUS
    require(b in (15, 16) and b <= k <= 17 and type(outside) is bool and (not outside or k > b),
            "Invalid branch")
    return [row for row in (
        (1, Q(0), r, None),
        (25-k-int(not outside), Q(0), 1-r, None),
        (k-b-int(outside), 1-r, Q(1), None),
        (1, 1-r if outside else SHARED_MIN, SHARED_MAX if outside else 1-r, None),
        (b-10, 1-r, Q(1), 0),
        (10, LONG_MIN, Q(1), 1),
    ) if row[0]]


class MandatoryArc(ArcEnvelope):
    """An arc is assigned even if its length tends to zero."""

    def maximum(self, lo, hi):
        cosine, squared = cos_min(Q(1), self.r, lo, hi)
        if not squared:
            require(cosine > 0, "Unexpected exterior cosine")
            if cosine >= 1:
                return self.short_cap(Q(0))
            cosine *= cosine
        x2 = min(Q(1), (1 - cosine) / self.r**2)
        _, x = sqrt_bounds(x2)
        if x <= Q(1, 2):
            return self.short_cap(x)
        long = self.long_cap(x, x) if x <= self.peak_lo else self.peak_cap
        return max(self.short_max, long)


def verify(entry):
    b, k, outside = entry["b"], entry["k"], entry["outside"]
    domains = groups(b, k, outside)
    r = RADIUS
    pi0, pi1 = pi_bounds()
    lam, tau = Q(entry["lambda"]), Q(entry["tau"])
    s, t = map(Q, entry["slopes"])
    require(0 <= tau < lam < Q(1, 2) and t <= s <= 0, "Invalid dual parameters")
    lo, hi = c_bounds(lam)
    short = -lo
    long = -2 * lo
    if tau:
        long = seam_upper(lam, tau, 2) - 4 * lo
        short = long + c_bounds(lam - tau)[1]
    envs = [MandatoryArc(r, lam-tau, slope, short, long, pi0) for slope in (s, t)]
    caps = list(map(Q, entry["caps"]))
    require(len(caps) == len(domains), "Incorrect group caps")
    weights = [(Q(radius), Q(w)) for radius, w in entry["weights"]]
    counts = [(Q(radius), m, Q(w)) for radius, m, w in entry["count_weights"]]
    require(all(0 < radius <= 1 and w >= 0 for radius, w in weights), "Invalid circle weights")
    for radius, m, w in counts:
        require(r < radius <= 1 and type(m) is int and m >= 3 and w >= 0
                and r / radius < sin_lower(pi0 / (m-1)), "Invalid circle count weight")
    coeff = 52*lam - 2*tau + t
    area = r*r * (coeff * (pi1 if coeff > 0 else pi0) + 150*hi
                  + (s-t)*HALF + sum(d[0]*c for d, c in zip(domains, caps))
                  - sum(w for _, w in weights) - sum(w for _, _, w in counts))
    require(area < pi0, "Area bound is insufficient")
    boxes = [group_caps(weights, counts, r, a, b1, cap, None if j is None else envs[j])
             for (_, a, b1, j), cap in zip(domains, caps)]
    print(f"PASS short window b={b} k={k} outside={outside}, "
          f"area <= {float(area):.12f}, boxes={boxes}", flush=True)


def branches(b):
    return [(k, outside) for k in range(b, 18) for outside in (False, True) if not outside or k > b]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--boundary", type=int, nargs="+")
    args = parser.parse_args()
    payload = json.loads(args.certificate.read_text(encoding="utf-8"))
    if args.boundary:
        expected = [(b, k, out) for b in args.boundary for k, out in branches(b)]
        require(sorted((e["b"], e["k"], e["outside"]) for e in payload) == sorted(expected),
                "Incomplete branch list")
    for entry in payload:
        verify(entry)


if __name__ == "__main__":
    main()
