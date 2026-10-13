"""r20-chain: exact arc machinery (final).

Convention throughout: an ARC of a circle is given as (centre_angle, half_width) with
0 <= half_width <= pi.  All set operations are done in the "wedge" representation
    t is in the arc  <=>  |t - centre| <= half_width   (angles on the circle, mod 2pi),
and subtraction of a union of arcs from one arc is computed EXACTLY by:
    1. the answer is a finite union of arcs whose endpoints are endpoints of the original arc
       or endpoints where a cover arc crosses the original arc's boundary (i.e. t = cover_centre
       +- cover_halfwidth) that lie strictly inside the original arc;
    2. between consecutive such cut points the covered/uncovered status is constant (each cover
       arc's indicator is a step function of t), so the midpoint decides;
    3. adjacent surviving wedges whose angular gap is zero are merged.
Every cover arc is handled in its wedge representation, so no unwrapping error can occur.
"""
import numpy as np

PI = np.pi


def canon(c, hw):
    """Canonicalise an arc: hw clipped to [0,pi], centre taken mod 2pi."""
    return (float(c % (2 * PI)), float(min(max(hw, 0.0), PI)))


def in_arc(arc, t):
    c, hw = arc
    return abs((t - c + PI) % (2 * PI) - PI) <= hw + 1e-14


def arc_isect(a, b):
    """Intersection of two arcs (wedge form).  Returns arc or None.  Exact: an intersection
    is nonempty iff neither centre lies outside the other's wedge beyond the sum of the
    half-widths, and the result is centred at the point midway between the two 'inner ends'."""
    if a is None or b is None:
        return None
    if a[1] >= PI - 1e-15:
        return b
    if b[1] >= PI - 1e-15:
        return a
    d = (b[0] - a[0] + PI) % (2 * PI) - PI        # signed distance a->b, in (-pi,pi]
    if abs(d) > a[1] + b[1] + 1e-15:
        return None
    hw = (a[1] + b[1] - abs(d)) / 2.0
    if hw <= 1e-15:
        return None
    sgn = 1.0 if d >= 0 else -1.0
    c = a[0] + sgn * (a[1] - hw)
    return canon(c, hw)


def arc_minus_union(arc, covs):
    """arc minus the union of the cover arcs.  Returns a list of arcs (wedge form)."""
    c, hw = arc
    if hw <= 1e-15:
        return []
    for (cc, ch) in covs:
        if ch >= PI - 1e-15:
            return []
    if c - hw < -PI or c + hw > PI:
        ref = (c + PI) % (2 * PI)           # avoid branch-cut issues: shift the arc wholly
    else:
        ref = 0.0
    lo, hi = c - hw, c + hw
    cuts = [lo, hi]
    for (cc, ch) in covs:
        for t in (cc - ch, cc + ch):
            for k in (-2, -1, 0, 1, 2):
                x = t + 2 * PI * k
                if lo + 1e-14 < x < hi - 1e-14:
                    cuts.append(x)
    cuts = sorted(set(np.round(cuts, 14)))
    out = []
    for a, b in zip(cuts[:-1], cuts[1:]):
        if b - a <= 1e-14:
            continue
        mid = (a + b) / 2.0
        if any(in_arc(cv, mid) for cv in covs):
            continue
        out.append([a, b])
    # merge adjacent pieces (they share an endpoint)
    merged = []
    for a, b in out:
        if merged and abs(a - merged[-1][1]) < 1e-12:
            merged[-1][1] = b
        else:
            merged.append([a, b])
    if len(merged) > 1 and abs(merged[0][0] - lo) < 1e-12 and abs(merged[-1][1] - hi) < 1e-12:
        merged[0][0] = merged[-1][0] - (hi - lo)
        merged[-1][0] = merged[-1][1] - (hi - lo)   # keep it simple: merge below instead
        merged.pop()
        merged[0][0] = merged[0][1] - (merged[0][1] - merged[0][0])
    res = []
    for a, b in merged:
        res.append(canon((a + b) / 2.0 + (ref if False else 0.0), (b - a) / 2.0))
    return res


def disk_interval(ci, R, n_chk=4001):
    """Arc of Lambda_i = Cc(ci,R) inside the closed unit disk.

    With the parametrisation  x(t) = ci + R (cos t, sin t)  the norm is
        |x(t)|^2 = L^2 + R^2 + 2RL cos(t - phi),   L=|ci|, phi=arg ci,
    so  |x(t)| <= 1  <=>  cos(t-phi) <= a  with  a = (1-L^2-R^2)/(2RL)  < 1.
    Three cases: a <= -1 (whole circle inside D), a >= 1 (circle misses D),
    else  |t - (phi+pi)| <= pi - arccos(a).  The result is verified numerically."""
    L = float(np.linalg.norm(ci))
    if L <= 1e-15:
        return None
    if L + R <= 1.0 + 1e-15:
        return canon(0.0, PI)
    if L >= 1.0 + R:
        return None
    a = (1.0 - L * L - R * R) / (2.0 * R * L)
    if a >= 1.0 - 1e-15:
        return None                       # rim misses D entirely
    phi = float(np.arctan2(ci[1], ci[0]))
    if a <= -1.0 + 1e-15:
        # whole rim inside D
        ts = np.linspace(0, 2 * PI, n_chk, endpoint=False)
        if np.max(np.linalg.norm(np.asarray(ci) + R * np.stack([np.cos(ts), np.sin(ts)], 1),
                                 axis=1)) <= 1.0 + 1e-12:
            return canon(0.0, PI)
        return None
    ac = float(np.arccos(a))
    hw = PI - ac
    cand = canon(phi + PI, hw)
    # verification (cheap): the centre must satisfy the inequality, the anti-centre must not
    xm = np.asarray(ci) + R * np.array([np.cos(cand[0]), np.sin(cand[0])])
    xa = np.asarray(ci) + R * np.array([np.cos(cand[0] + PI), np.sin(cand[0] + PI)])
    if np.linalg.norm(xm) > 1.0 + 1e-12:
        raise AssertionError("disk_interval centre is outside D")
    if np.linalg.norm(xa) < 1.0 - 1e-12:
        raise AssertionError("disk_interval anti-centre is inside D (arc is wrong)")
    return cand


def ring_cover_interval(ci, ck, R):
    """Arc of Lambda_i covered by B(ck,R)."""
    d = float(np.linalg.norm(np.asarray(ck) - np.asarray(ci)))
    if d >= 2.0 * R or d <= 1e-15:
        return None if d >= 2.0 * R else canon(0.0, PI)
    b = float(np.arccos(np.clip(d / (2.0 * R), -1, 1)))
    psi = float(np.arctan2(*(np.asarray(ck) - np.asarray(ci))[::-1]))
    return canon(psi, b)


def truly_uncovered_arcs(ring, i, R):
    """Arcs of Lambda_i inside the closed unit disk and covered by no other ring disk."""
    I = disk_interval(ring[i], R)
    if I is None:
        return []
    covs = []
    for k in range(len(ring)):
        if k == i:
            continue
        Ck = ring_cover_interval(ring[i], ring[k], R)
        if Ck is not None:
            covs.append(Ck)
    return arc_minus_union(I, covs)


def hub_slack_rings(ring, R, H, served_idx):
    """slack_i = R - max_{x in U_i} |H-x| and the argmax point (exact extremum at an endpoint
    or at the phase of H-c_i when present in the arc)."""
    H = np.asarray(H, float)
    out = {}
    for i in served_idx:
        ci = np.asarray(ring[i], float)
        psi = float(np.arctan2(*(H - ci)[::-1]))
        best, arg = -np.inf, None
        for (c, hw) in truly_uncovered_arcs(ring, i, R):
            if hw <= 1e-13:
                continue
            for t in (c - hw, c + hw):
                x = ci + R * np.array([np.cos(t), np.sin(t)])
                v = float(np.linalg.norm(x - H))
                if v > best:
                    best, arg = v, x
            for k in (-1, 0, 1):
                t = psi + 2 * PI * k
                if c - hw - 1e-12 <= t <= c + hw + 1e-12:
                    x = ci + R * np.array([np.cos(t), np.sin(t)])
                    v = float(np.linalg.norm(x - H))
                    if v > best:
                        best, arg = v, x
        out[i] = (np.inf if not np.isfinite(best) else R - best, arg)
    return out
