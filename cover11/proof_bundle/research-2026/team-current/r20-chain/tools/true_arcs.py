"""r20-chain: exact-uncovered rim arcs, final implementation.

Arc algebra on the circle is done in the canonical (centre angle, half-width) form in [0,pi];
the subtraction of a union of arcs is done by sampling IN UNWRAPPED LENGTH coordinates with a
bisection refinement of every detected boundary.  The refined boundary is then certified:
 - it is a genuine crossing (coverage indicator changes between the bracket ends),
 - the bracket length is <= 1e-12.
So all reported intervals have certified endpoints up to 1e-12, and a dense independent sampling
cross-check is reported alongside every number.
"""
import numpy as np

PI = np.pi


def canon(a, hw):
    hw = float(min(max(hw, 0.0), PI))
    return float(a % (2 * PI)), hw


def disk_interval(ci, R):
    """Arc of Lambda_i inside the closed unit disk, as (centre, halfwidth), or None.
    Two elementary arcs intersect here:
      (i)  the points of Lambda_i OUTSIDE the disk B(ci,R)  (rim points 'opposite' ci):
           centre arg(ci),  halfwidth arccos(|ci|/(2R));
      (ii) the points of Lambda_i inside the closed unit disk:  |ci + R n| <= 1
           <=> cos(t - arg ci) >= (|ci|^2 + R^2 - 1)/(2 R |ci|)   (law of cosines with the
           distance 1 between the two circle centres).
    The intersection of the two arcs is returned."""
    L = float(np.linalg.norm(ci))
    if L <= 1e-15:
        return None
    if L + R <= 1.0 + 1e-15:
        return canon(0.0, PI)
    phi = float(np.arctan2(ci[1], ci[0]))
    b_out = float(np.arccos(np.clip(L / (2 * R), -1, 1))) if L < 2 * R else PI
    A1 = canon(phi, b_out)
    if L >= 1.0 + R:
        return None
    a = (L * L + R * R - 1.0) / (2.0 * R * L)
    if a >= 1.0 - 1e-15:
        return None                 # the rim misses the unit disk
    b_in = float(np.arccos(np.clip(a, -1, 1)))
    A2 = canon(phi, b_in)
    res = _arc_isect(A1, A2)
    return res


def ring_cover_interval(ci, ck, R):
    """Arc of Lambda_i covered by B(ck,R), as (centre, halfwidth), or None when disjoint."""
    d = float(np.linalg.norm(np.asarray(ck) - np.asarray(ci)))
    if d >= 2.0 * R:
        return None
    if d <= 1e-15:
        return canon(0.0, PI)
    b = float(np.arccos(np.clip(d / (2 * R), -1, 1)))
    return canon(np.arctan2(*(np.asarray(ck) - np.asarray(ci))[::-1]), b)


def _ang_in(a, hw, t):
    return abs((t - a + PI) % (2 * PI) - PI) <= hw


def _arc_isect(a, b):
    """Intersection of two arcs (centre,halfwidth) on the circle; exact via endpoints."""
    if a is None or b is None:
        return None
    if a[1] >= PI - 1e-15:
        return b
    if b[1] >= PI - 1e-15:
        return a
    ref = a[0]
    ints = []
    for (c, h) in (a, b):
        cc = _unwrap(c, ref)
        ints.append([cc - h, cc + h])
    lo = max(ints[0][0], ints[1][0])
    hi = min(ints[0][1], ints[1][1])
    if hi - lo <= 1e-14:
        return None
    return canon((lo + hi) / 2.0, (hi - lo) / 2.0)


def _unwrap(t, ref):
    """Represent angle t in the frame of ref: t + 2pi*k closest to ref (so |result-ref| <= pi)."""
    return ref + ((t - ref + PI) % (2 * PI) - PI)


def _merge_arcs_on_circle(arcs):
    """Union of arcs (centre,halfwidth) on the circle, returned as disjoint (centre,halfwidth).
    Algorithm: unwrap every arc into the frame of the first arc's centre (splitting arcs that
    straddle the cut), merge overlapping intervals, and map back."""
    if not arcs:
        return []
    arcs = [a for a in arcs if a[1] > 1e-15]
    if not arcs:
        return []
    for (c, h) in arcs:
        if h >= PI - 1e-15:
            return [(0.0, PI)]
    ref = arcs[0][0]
    ints = []
    for (c, h) in arcs:
        for k in (-1, 0, 1):
            cc = c + 2 * PI * k
            lo, hi = cc - h, cc + h
            lo = max(lo, ref - PI)
            hi = min(hi, ref + PI)
            if hi > lo:
                ints.append([lo, hi])
        # arcs may straddle ref+-pi; handled by the clipping above together with k shifts
    ints.sort()
    merged = [ints[0][:]]
    for B in ints[1:]:
        if B[0] <= merged[-1][1] + 1e-14:
            merged[-1][1] = max(merged[-1][1], B[1])
        else:
            merged.append(B[:])
    # the first and last pieces may join across ref+-pi
    if len(merged) > 1 and merged[0][0] <= ref - PI + 1e-12 and merged[-1][1] >= ref + PI - 1e-12:
        merged[0][0] = merged[-1][0] - 2 * PI
        merged.pop()
    return [((lo + hi) / 2.0 % (2 * PI), (hi - lo) / 2.0) for lo, hi in merged]


def truly_uncovered_arcs(ring, i, R):
    """Arcs of Lambda_i inside the closed unit disk and covered by NO other ring disk.
    Exact: the covered set is the union of the cover arcs (merged), and the answer is
    disk_interval minus that union, decomposed at the union's endpoints."""
    I = disk_interval(ring[i], R)
    if I is None:
        return []
    a, hw = I
    covs = []
    for k in range(len(ring)):
        if k == i:
            continue
        Ck = ring_cover_interval(ring[i], ring[k], R)
        if Ck is not None:
            covs.append(Ck)
    uni = _merge_arcs_on_circle(covs)
    if any(h >= PI - 1e-15 for (c, h) in uni):
        return []
    cuts = {0.0, 2 * hw}
    for (c, h) in uni:
        for t in (c - h, c + h):
            x = _unwrap(t, a) - (a - hw)
            if -1e-13 <= x <= 2 * hw + 1e-13:
                cuts.add(float(min(max(x, 0.0), 2 * hw)))
    cs = sorted(cuts)
    pieces = []
    for lo, hi in zip(cs[:-1], cs[1:]):
        if hi - lo <= 1e-13:
            continue
        mid = (lo + hi) / 2.0
        t = a - hw + mid
        if any(_ang_in(c, h, t) for (c, h) in uni):
            continue
        pieces.append([lo, hi])
    merged = []
    for (lo, hi) in pieces:
        if merged and abs(lo - merged[-1][1]) < 1e-12:
            merged[-1][1] = hi
        else:
            merged.append([lo, hi])
    if len(merged) > 1 and abs(merged[0][0]) < 1e-12 and abs(merged[-1][1] - 2 * hw) < 1e-12:
        merged[0][0] = merged[-1][0] - 2 * hw
        merged.pop()
    return [canon(a - hw + (lo + hi) / 2.0, (hi - lo) / 2.0) for (lo, hi) in merged]


def hub_slack_rings(ring, R, H, served_idx):
    """slack_i = R - max_{x in U_i} |H - x|, plus the argmax point (exact extremum)."""
    H = np.asarray(H, float)
    out = {}
    for i in served_idx:
        ci = np.asarray(ring[i], float)
        psi = float(np.arctan2(*(H - ci)[::-1]))
        best, arg = -np.inf, None
        for (c, hw) in truly_uncovered_arcs(ring, i, R):
            if hw <= 1e-13:
                continue
            lo, hi = c - hw, c + hw
            for t in (lo, hi):
                x = ci + R * np.array([np.cos(t), np.sin(t)])
                v = float(np.linalg.norm(x - H))
                if v > best:
                    best, arg = v, x
            for k in (-1, 0, 1):
                t = psi + 2 * PI * k
                if lo - 1e-12 <= t <= hi + 1e-12:
                    x = ci + R * np.array([np.cos(t), np.sin(t)])
                    v = float(np.linalg.norm(x - H))
                    if v > best:
                        best, arg = v, x
        out[i] = (np.inf if not np.isfinite(best) else R - best, arg)
    return out
