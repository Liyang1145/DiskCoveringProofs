"""r20-chain: EXACT gap-arc object for the two-hub chain reduction.

Definitions (no symmetry premise; c_i, c_{i+1} two ring centres of the SAME chain, R the common
radius, D the closed unit disk).

  Lambda_i := Cc(c_i, R).  The part of Lambda_i covered by the partner ring disk B(c_{i+1},R) is the
  arc centred on the direction u := (c_{i+1}-c_i)/|c_{i+1}-c_i| with half-width
        beta_i = arccos(d/(2R)),   d = |c_i - c_{i+1}|        (valid iff d < 2R),
  because for a point x = c_i + R n,   |x - c_{i+1}|^2 = d^2 + R^2 - 2dR cos(angle(n,u)).
  Hence the part of Lambda_i UNCOVERED by the partner is the complementary arc
        U_i = { t : beta_i <= |t| <= 2pi - beta_i }   (t = angle from u about c_i).

  The part of Lambda_i that also lies in D is the interval
        I_i = { x = c_i + R n : |x|^2 <= 1 } = { t : cos(t - phi_i) >= a_i },
        a_i = (1 - R^2 - |c_i|^2)/(2 R |c_i|),   phi_i = arg c_i,
  so the rim piece that the hub MUST cover for this gap is
        J_i := U_i ∩ I_i    (a union of at most two arcs; usually the one near the pole).

  The gap's outer boundary piece on Lambda_i is exactly J_i.  (Interior gap points lie inside the
  convex hull of the junction points and are handled by the convexity of the hub disk; the pole
  P_i = (c_i/|c_i|)(|c_i|-R) ∈ B(0,1) always lies in U_i because beta_i < pi for d>0, and P_i is
  the closest point of Lambda_i to the origin so it is the extremal point in the direction -H.)

  NECESSARY CONDITION:   if H serves this gap, then  max_{x in J_i} |H - x| <= R  for both i and i+1.

Everything below is computed exactly (interval arithmetic on angles), not by grids.  The dense
sampling is kept only as an independent cross-check of the interval construction.
"""
import numpy as np

PI = np.pi


def beta_of(d, R):
    return np.arccos(np.clip(d / (2.0 * R), -1.0, 1.0))


def angle_intervals(ci, R):
    """I_i as an angular interval (about c_i, absolute angle convention) or None when Lambda_i
    lies entirely inside D.  Returns a list of (lo, hi) intervals (mod 2pi, lo<hi, possibly
    length > pi)."""
    L = np.linalg.norm(ci)
    if L + R <= 1.0 + 1e-15:
        return [(0.0, 2 * PI)]
    a = (1.0 - R * R - L * L) / (2.0 * R * L)
    a = float(np.clip(a, -1.0, 1.0))
    phi = np.arctan2(ci[1], ci[0])
    ac = np.arccos(a)                      # |t-phi| <= ac
    return [((phi - ac) % (2 * PI), (phi - ac) % (2 * PI) + 2 * ac)]


def uncovered_intervals(ci, cj, R):
    """U_i as a list of angular intervals (absolute angle about c_i)."""
    d = np.linalg.norm(np.asarray(cj) - np.asarray(ci))
    u = np.arctan2(*(np.asarray(cj) - np.asarray(ci))[::-1])
    if d >= 2.0 * R:
        return [(u + PI, u + PI + 2 * PI)]
    b = beta_of(d, R)
    lo, hi = u + b, u + (2 * PI - b)       # covers 2pi-2b > pi length
    return [(lo, hi)]


def isect(iv, jv):
    """Intersection of two intervals given as (lo,hi); result may need wrapping; returns list."""
    a0, a1 = iv
    b0, b1 = jv
    # bring both to a common unwrapped frame with lengths preserved
    res = []
    for k in (-1, 0, 1):
        lo = max(a0, b0 + 2 * PI * k)
        hi = min(a1, b1 + 2 * PI * k)
        if hi > lo + 1e-15:
            res.append((lo, hi))
    return res


def _arc_intersect(a, b, tiny=1e-15):
    """Intersection of two arcs given as (centre_angle, half_width), 0 <= hw <= pi.
    Returns (centre, half_width) or None.  Exact, no wrap ambiguity: the two arc centres lie on a
    circle, so the intersection (when nonempty) is a single arc centred on the segment between them
    at fraction  a_hw/(a_hw+b_hw)  from a's centre, with half-width (a_hw+b_hw-delta)/2."""
    ahw, bhw = a[1], b[1]
    if ahw >= PI - tiny:
        return b
    if bhw >= PI - tiny:
        return a
    delta = abs((a[0] - b[0] + PI) % (2 * PI) - PI)
    hw = (ahw + bhw - delta) / 2.0
    if hw < 0:
        return None
    s = ahw + bhw
    if s <= tiny:
        return (a[0] % (2 * PI), 0.0)
    # move from a's centre toward b's centre by ahw - hw
    d = (b[0] - a[0] + PI) % (2 * PI) - PI
    step = ahw - hw
    c = a[0] + d * (step / delta) if delta > 1e-14 else a[0]
    return (c % (2 * PI), float(hw))


def arc_hw(lo, hi):
    """Convert an interval (lo,hi) with length <= 2pi to (centre, half_width)."""
    L = hi - lo
    return ((lo + hi) / 2.0, L / 2.0)


def gap_arcs(ci, cj, R):
    """The arc J_i = U_i ∩ I_i (the rim piece the hub must cover for this gap), as [(lo,hi)]."""
    out = []
    for U in uncovered_intervals(ci, cj, R):
        for I in angle_intervals(ci, R):
            res = _arc_intersect(arc_hw(*U), arc_hw(*I))
            if res is not None:
                c, hw = res
                lo = (c - hw) % (2 * PI)
                out.append((lo, lo + 2 * hw))
    return out


def arc_points(ci, R, iv, n=4001):
    t = np.linspace(iv[0], iv[1], n)
    return np.asarray(ci) + R * np.stack([np.cos(t), np.sin(t)], 1), t


def cover_slack(H, R, ci, cj, n=4001):
    """EXACT necessary-condition slack for the gap arc on Lambda_i (partner c_j):
       slack = R - max_{x in J_i} |H - x| ;  >= 0  <=>  the whole gap arc is covered.
       max |H-x| over J_i is attained at an endpoint of J_i or at the point where the arc
       direction is -(H) (i.e. the point of the arc farthest from H, only present if that phase
       belongs to the arc).  Both are computed exactly."""
    arcs = gap_arcs(ci, cj, R)
    if not arcs:
        return np.inf, None, 0.0
    ci = np.asarray(ci, float)
    H = np.asarray(H, float)
    # extremal phase: |c + R n - H|^2 = R^2 + |c-H|^2 + 2R|c-H| cos(t - psi) with psi = arg(H-c);
    # maximum at t = psi (when present in the arc).
    psi = np.arctan2(*(H - ci)[::-1])
    best = -np.inf
    arg = None
    ext = 0.0
    for (lo, hi) in arcs:
        for t in (lo, hi):
            x = ci + R * np.array([np.cos(t), np.sin(t)])
            v = np.linalg.norm(x - H)
            if v > best:
                best, arg = v, x
        for k in (-2, -1, 0, 1, 2):
            t = psi + 2 * PI * k
            if lo - 1e-15 <= t <= hi + 1e-15:
                x = ci + R * np.array([np.cos(t), np.sin(t)])
                v = np.linalg.norm(x - H)
                if v > best:
                    best, arg = v, x
        pts, _ = arc_points(ci, R, (lo, hi), n)
        vv = np.max(np.linalg.norm(pts - H, axis=1))
        if vv > best + 1e-9:
            raise AssertionError("analytic max below sampled max: %.3e" % (vv - best))
        ext += (hi - lo)
    return R - best, arg, ext
