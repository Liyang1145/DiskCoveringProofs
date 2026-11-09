"""Exact certificates combining fan area, radial angles and circle counts."""

import argparse
import json
from fractions import Fraction as Q
from math import asin
from pathlib import Path

from rational_trig import pi_bounds, sin_lower, sin_upper, sqrt_bounds
from verify_fan import asin_upper, c_bounds, cap_upper, fan_line, require
from verify_radial import ANGLES, PI_LOW, bound, cos_min
from verify_seam import NO_REPEAT_RADIUS, no_repeat_bound, seam_upper


def asin_lower(x, pi0):
    scale = 10**11
    j = int(scale * asin(float(x)))
    while j > 0:
        angle = Q(j, scale)
        if angle < pi0 / 2 and sin_upper(angle) <= x:
            return angle
        j -= 1
    return Q(0)


class ArcEnvelope:
    def __init__(self, r, lam, slope, short_offset, long_offset, pi0):
        self.r, self.lam, self.slope, self.pi0 = r, lam, slope, pi0
        self.short_offset, self.long_offset = short_offset, long_offset
        lo, hi = Q(1, 2), Q(1)
        require(self.derivative(lo, False) > 0 and self.derivative(hi, True) < 0,
                "Expected an interior maximum on the long-arc branch")
        # Strict concavity in theta=asin(x) means a single maximum.
        for _ in range(28):
            mid = (lo + hi) / 2
            if self.derivative(mid, False) > 0:
                lo = mid
            elif self.derivative(mid, True) < 0:
                hi = mid
            else:
                break
        self.peak_lo = lo
        self.peak_cap = self.long_cap(lo, hi)
        self.short_max = self.short_cap(Q(1, 2))

    def derivative(self, x, upper):
        a = sqrt_bounds(1 - x * x)
        b = sqrt_bounds(1 - (self.r * x) ** 2)
        return (1 - 2 * x * x - 2 * self.lam
                + (2 * x * x - self.slope) * self.r * a[upper] / b[not upper])

    def cap_and_line(self, x):
        z = self.r * x
        # Round only upward before the positive power series.
        den = 10**13
        z = Q(-((-z.numerator * den) // z.denominator), den)
        alpha = asin_upper(z)
        a, _ = sqrt_bounds(1 - z * z)
        return (alpha - z * a) / self.r**2 - self.slope * alpha

    def short_cap(self, x):
        return self.cap_and_line(x) + self.short_offset

    def long_cap(self, lo, hi):
        _, h = sqrt_bounds(1 - lo * lo)
        return (hi * h - 2 * self.lam * asin_lower(lo, self.pi0)
                + self.cap_and_line(hi) + self.long_offset)

    def maximum(self, lo, hi):
        cosine, squared = cos_min(Q(1), self.r, lo, hi)
        if not squared:
            require(cosine > 0, "Unexpected sign of exterior cosine")
            if cosine >= 1:
                return Q(0)
            cosine *= cosine
        x2 = min(Q(1), (1 - cosine) / self.r**2)
        _, x = sqrt_bounds(x2)
        if x <= Q(1, 2):
            return max(Q(0), self.short_cap(x))
        long = self.long_cap(x, x) if x <= self.peak_lo else self.peak_cap
        return max(Q(0), self.short_max, long)


def integer_fan_loss(n, lam):
    pi0, pi1 = pi_bounds()
    clo, _ = c_bounds(lam)
    upper = max(
        m * (sin_upper(2*pi0/m) + 2*(pi1-pi0)/m) / 2 - m*clo
        for m in range(3, n)
    )
    return max(Q(0), 2*pi0*lam - upper)


def central_cap(r, low):
    s = 1-4*r
    require(0 < s < r and low in (0,1), "Invalid central disk grouping")
    if low == 0:
        return r-s
    return sqrt_bounds(r*r-s*s)[1]


def group_caps(weights, count_weights, r, lo, hi, limit, envelope):
    cuts = sorted({lo, hi, *(t for s, _, _ in count_weights for t in (s-r, s+r) if lo < t < hi)})
    pending = [(a, b, 0) for a, b in zip(cuts, cuts[1:])]
    if not pending:
        pending = [(lo, hi, 0)]
    passed = 0
    while pending:
        a, b, depth = pending.pop()
        total = sum(w * bound(s, r, a, b) / ANGLES for s, w in weights)
        total += sum(w / m for s, m, w in count_weights if a < s + r and b > s - r)
        if envelope:
            total += envelope.maximum(a, b)
        if total <= limit:
            passed += 1
            continue
        if depth >= 25:
            raise ValueError(f"Budget fails near t={float(a):.12f}: "
                             f"need {float(total):.12f}, cap={float(limit):.12f}")
        mid = (a + b) / 2
        pending.extend(((a, mid, depth+1), (mid, b, depth+1)))
    return passed


def verify(entry):
    pi0, pi1 = pi_bounds()
    require(0 < PI_LOW <= pi0, "The lower bound for pi failed")
    k = entry["k"]
    n = entry.get("disks", 26)
    rmin, r = Q(entry["r_min"]), Q(entry["r_max"])
    lam, slope, delta = (Q(entry[x]) for x in ("lambda", "slope", "repeat_penalty"))
    tau = Q(entry.get("tau", "0"))
    require(n in (25, 26) and 14 <= k <= n-9 and 0 < rmin <= r <= Q(".235"),
            "Invalid radius or exterior count")
    require(0 <= tau < lam < Q(1, 2) and slope <= 0 and delta >= 0, "Invalid dual parameters")
    if delta == 0 and k != 14:
        require(r <= NO_REPEAT_RADIUS[n], "The no-repeat reduction is unavailable at this radius")
        no_repeat_bound(n)
    require(not tau or not delta, "Seam coupling requires a no-repeat certificate")
    weights = [(Q(s), Q(w)) for s, w in entry["weights"]]
    count_weights = [(Q(s), m, Q(w)) for s, m, w in entry.get("count_weights", [])]
    require(all(0 < s <= 1 and w >= 0 for s, w in weights), "Invalid angular weights")
    for s, m, w in count_weights:
        require(r < s <= 1 and m >= 3 and w >= 0, "Invalid count weight")
        require(r / s < sin_lower(pi0 / (m-1)), "Unverified circle count")
    clo, chi = c_bounds(lam)
    long_offset = -2 * clo
    short_offset = -clo
    if tau:
        _, arc_chi = c_bounds(lam - tau)
        long_offset = seam_upper(lam, tau, 2) - 4 * clo
        short_offset = long_offset + arc_chi
    if delta:
        require(delta <= pi0 * lam + min(clo, 2*clo - cap_upper(asin_upper(r)) / r**2),
                "Unverified repeated-arc area penalty")
        theta = Q(".53")
        u, _ = sqrt_bounds(1 - r*r)
        require(sin_lower(theta)**2 >= 1 / (2 * (1+u)), "Short-arc test range too short")
        fan_line(r, lam, delta, slope, theta)

    low = entry.get("low")
    cap = min(r,central_cap(r,low)) if entry.get("core_caps",False) else r
    intervals = [(Q(0), cap)]
    counts = [1]
    if low is None:
        intervals += [(Q(0), 1 - rmin)]
        counts += [n - 1 - k]
    else:
        m = entry.get("participants", 8)
        require(m >= 3 and 2*r < 1-2*r and r / (1-2*r) < sin_lower(pi0 / (m-1)),
                "Unverified required participants at 1-2r")
        require(0 <= low <= n-1-k-m, "Invalid low count")
        intervals += [(Q(0), 1-3*r), (1-3*r, 1-rmin)]
        counts += [low, n-1-k-low]
        if "middle_split" in entry:
            threshold, left = entry["middle_split"]
            a,b = intervals.pop()
            count = counts.pop()
            q = Q(threshold)
            require(a < q < b and type(left) is int and 0 <= left <= count,"Invalid middle split")
            intervals += [(a,q),(q,b)]
            counts += [left,count-left]
    require(low is not None or "middle_split" not in entry,"Missing middle population")
    intervals += [(1-r, Q(1))]
    counts += [k]
    caps = list(map(Q, entry["caps"]))
    require(len(caps) == len(counts) and all(c >= 0 for c in caps), "Invalid group caps")
    area = r*r * (
        n*2*pi1*lam + (6*n-6)*chi + (slope - 2*tau)*pi0
        + sum(a*b for a, b in zip(counts, caps))
        - sum(w for _, w in weights) - sum(w for _, _, w in count_weights)
    )
    if entry.get("integer_fans", False):
        area -= r*r * (n-k) * integer_fan_loss(n, lam)
    require(area < pi0, "Area upper bound must be strictly smaller than pi")
    envelope = ArcEnvelope(r, lam - tau, slope, short_offset, long_offset, pi0)
    boxes = [
        group_caps(weights, count_weights, r, a, b, cap, envelope if i == len(counts)-1 else None)
        if n else 0
        for i, ((a, b), cap, n) in enumerate(zip(intervals, caps, counts))
    ]
    print(f"PASS n={n}, k={k}, low={low}, r in [{float(rmin):.10g}, {float(r):.10g}], "
          f"area <= {float(area):.12f}, boxes={boxes}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    for entry in json.loads(args.certificate.read_text(encoding="utf-8")):
        verify(entry)


if __name__ == "__main__":
    main()
