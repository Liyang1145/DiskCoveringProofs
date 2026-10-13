"""r20 canonical-domain (C464) tight-boundary discrimination — ANALYTIC, no sampling.

Read-only outside r20-chain; writes ../out/r20_canonical_tight_boundary.txt.

LEGALDOMAIN (C464): any equal-disk cover of the unit disk can be replaced, per ring, by the inward
radial root of the same actual boundary arc, so the representative satisfies
     1-r <= |c_i| <= L*,   L* := sqrt(1-r^2)   (inward-root / canonical domain).
The earlier r20_fixed_endpoint_variation experiment used |c_L| = |c_R| = 1 > L* and is therefore
OUTSIDE this domain; and the "inner-pin branch" |H-p_in| <= r (a hub-side, per-edge condition) is a
DIFFERENT condition from the ring's radial inward root |c_i| <= L*.

Analytic facts used (all closed-form):
  (i) arc half-width of a radius-r disk centred at c with |c|=L:  beta(L) = arccos((1+L^2-r^2)/(2L)),
      strictly increasing on [1-r, L*] with beta(L*) = asin r  (so inside the canonical domain the
      coverage functional has NO interior stationary ridge: its extremum sits on |c| = L*).
  (ii) tight set of one edge (pair (X,H), variable ring c): rho(X,c,H) = r  <=>  c on the two circles
      of radius r about q_+^{X}, q_-^{X}, the two radius-r circle centres through (X,H).
  (iii) fan region {rho(X,c,H) <= r} = (B(q_+,r) ∪ B(q_-,r)) minus the interior of the intersection.
Everything below is evaluated on the canonical circle |c| = L* (the coverage-optimal radius), where
each constraint becomes a CLOSED-FORM set of azimuths (arcs), intersected exactly.
"""
import math
import numpy as np
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []
TWO_PI = 2 * math.pi


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


# ---------------------------------------------------------------- arc-set algebra on a circle
def norm_iv(x):
    """normalise a list of (lo,hi) intervals modulo 2pi, merge overlaps."""
    iv = []
    for (a, b) in x:
        if b - a >= TWO_PI - 1e-15:
            return [(0.0, TWO_PI)]
        a0 = a % TWO_PI
        L = b - a
        if L < 0:
            continue
        iv.append((a0, a0 + L))
    iv.sort()
    out = []
    for (a, b) in iv:
        if out and a <= out[-1][1] + 1e-15:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    # wrap-merge
    if len(out) > 1 and out[-1][1] > TWO_PI and out[0][0] < 1e-12:
        out[0] = (0.0, out[-1][1] - TWO_PI)
        out.pop()
    return out


def isect(A, B):
    out = []
    for (a1, b1) in A:
        for (a2, b2) in B:
            lo, hi = max(a1, a2), min(b1, b2)
            if hi > lo + 1e-15:
                out.append((lo, hi))
    return norm_iv(out)


def union(A, B):
    return norm_iv(list(A) + list(B))


def complement(A):
    if not A:
        return [(0.0, TWO_PI)]
    out = []
    cur = 0.0
    for (a, b) in A:
        if a > cur + 1e-15:
            out.append((cur, a))
        cur = max(cur, b)
    if cur < TWO_PI - 1e-15:
        out.append((cur, TWO_PI))
    return out


def pt_in(A, t):
    t = t % TWO_PI
    return any(a - 1e-12 <= t <= b + 1e-12 for (a, b) in A)


def disk_iv(cen, R0, A, r):
    """azimuths t with |cen + R0 u(t) - A| <= r."""
    d = float(np.linalg.norm(np.asarray(A) - np.asarray(cen)))
    if d <= 1e-15:
        return [(0.0, TWO_PI)] if R0 <= r else []
    if d > R0 + r + 1e-15:
        return []
    cosv = (d * d + R0 * R0 - r * r) / (2 * d * R0)
    v = np.asarray(A) - np.asarray(cen)
    psi = math.atan2(v[1], v[0])
    if cosv <= -1.0:
        return [(0.0, TWO_PI)]
    if cosv >= 1.0:
        return norm_iv([(psi, psi)])
    half = math.acos(cosv)
    return norm_iv([(psi - half, psi + half)])


def annulus_iv(cen, R0, lo, hi):
    """azimuths t with lo <= |cen + R0 u(t)| <= hi."""
    Lc = float(np.linalg.norm(cen))
    if Lc <= 1e-15:
        return [(0.0, TWO_PI)] if lo <= R0 <= hi else []
    # |.|^2 = Lc^2 + R0^2 + 2 R0 Lc cos(t - arg cen)
    f = lambda t: Lc * Lc + R0 * R0 + 2 * R0 * Lc * math.cos(t - math.atan2(cen[1], cen[0]))
    # sample-free bisection on the two thresholds
    lo2, hi2 = lo * lo, hi * hi
    n = 4096
    mask = []
    for k in range(n):
        t = TWO_PI * k / n
        v = f(t)
        mask.append(lo2 <= v <= hi2)
    # exact-ish intervals: the set {cos(t-psi) in [c1,c2]} -> closed form
    c1 = (lo2 - Lc * Lc - R0 * R0) / (2 * R0 * Lc)
    c2 = (hi2 - Lc * Lc - R0 * R0) / (2 * R0 * Lc)
    c1, c2 = min(c1, c2), max(c1, c2)
    if c2 < -1:
        return []
    if c1 > 1:
        return []
    psi = math.atan2(cen[1], cen[0])
    lo_ang = math.acos(min(1, max(-1, c2)))      # cos >= c2 -> |t-psi| <= acos(c2)
    hi_ang = math.pi if c1 <= -1 else math.acos(min(1, max(-1, c1)))   # cos <= c1 -> |t-psi| >= acos(c1)
    A = norm_iv([(psi - lo_ang, psi + lo_ang)])
    if hi_ang >= math.pi - 1e-15:
        return A
    B = norm_iv([(psi + hi_ang, psi - hi_ang + TWO_PI)])               # |t-psi| >= hi_ang
    return isect(A, B)


def fan_iv(cen, R0, X, H, r):
    """azimuths t of c = cen + R0 u(t) satisfying rho(X,c,H) <= r  (fan region of the pair (X,H)).
    Region = (B(q_+,r) u B(q_-,r)) minus int(B(q_+) ^ B(q_-)); q_+-, the radius-r circle centres
    through (X,H)."""
    X = np.asarray(X, float); H = np.asarray(H, float)
    M = (X + H) / 2
    d = float(np.linalg.norm(H - X))
    if d > 2 * r:
        return []
    k = math.sqrt(max(r * r - d * d / 4, 0.0))
    e = (H - X) / d
    n = np.array([-e[1], e[0]])
    qp, qm = M + k * n, M - k * n
    ip, im = disk_iv(cen, R0, qp, r), disk_iv(cen, R0, qm, r)
    both = isect(ip, im)
    return complement(both) if False else isect(union(ip, im), complement(both))


def isect_all(sets):
    out = sets[0]
    for S in sets[1:]:
        out = isect(out, S)
        if not out:
            return []
    return out


def report(name, iv):
    P("     %-28s %s" % (name, "  ".join("[%.6f,%.6f]" % (a, b) for (a, b) in iv) if iv else "EMPTY"))


def run_case(r, h, adeg, Lfac=1.0):
    Ls = math.sqrt(1 - r * r)
    L = Lfac * Ls             # internal ring radius on the canonical scale (Lfac<=1)
    a = math.radians(adeg)
    cL = Ls * np.array([math.cos(a), math.sin(a)])
    cR = Ls * np.array([math.cos(a), -math.sin(a)])
    H = np.array([h, 0.0])
    beta = lambda LL: math.acos((1 + LL * LL - r * r) / (2 * LL))
    bL = beta(Ls)
    gam = a - bL                                     # gap half-width (azimuth)
    P("")
    P("   --- case r=%.3f h=%.2f alpha=%.1f deg ; endpoints |c|=L*=%.9f ; internal |c|=%.9f"
      % (r, h, adeg, Ls, L))
    if gam <= 0:
        P("     no gap (endpoint arcs already meet): coverage is free; canonical tight test = fans only")
    A = np.array([math.cos(gam), -math.sin(gam)])
    B = np.array([math.cos(gam), math.sin(gam)])
    P("     gap endpoints A'=(%.9f,%.9f) B'=(%.9f,%.9f)  (gap half-angle %.6f rad = %.3f deg)"
      % (A[0], A[1], B[0], B[1], gam, math.degrees(gam)))
    cen = np.zeros(2)
    covA = disk_iv(cen, L, A, r)
    covB = disk_iv(cen, L, B, r)
    cov = isect(covA, covB)
    f1 = fan_iv(cen, L, cL, H, r)
    f2 = fan_iv(cen, L, cR, H, r)
    band = annulus_iv(cen, L, 1 - r, math.sqrt(1 - r * r))
    F = isect_all([cov, f1, f2, band])
    report("coverage (gap) arcs", cov)
    report("fan (cL,c) arcs", f1)
    report("fan (c,cR) arcs", f2)
    report("F = cov ^ f1 ^ f2", F)
    # tight hits: boundary points of the fan sets that lie in F
    hits = []
    for (S, nm) in ((f1, "edge1 tight"), (f2, "edge2 tight")):
        for (x, y) in S:
            for t in (x, y):
                if pt_in(F, t):
                    hits.append((nm, t))
    P("     analytic tight-hit: %s"
      % ("NONE" if not hits else " ; ".join("%s at phi=%.9f" % (nm, t) for (nm, t) in hits)))
    # also: is any tight hit interior to the other fan (i.e. exactly one active pin)?
    return hits


def main():
    P("=" * 100)
    P("CANONICAL DOMAIN (C464 inward-root) TIGHT-BOUNDARY DISCRIMINATION — closed-form arcs only")
    P("  domain: 1-r <= |c_i| <= L* = sqrt(1-r^2);  beta(L) increasing on [1-r,L*], max = asin r at L*")
    P("  => inside the canonical domain the coverage functional has no interior ridge; its extremum")
    P("     sits at |c| = L* (so the earlier |c|=1 / annulus[1-r,1] experiment is outside the domain).")
    r, h = 0.38, 0.5
    P("  r = %.3f, H = (%.2f,0), L* = %.9f, asin r = %.9f (max arc half-width)" % (r, h, math.sqrt(1 - r * r), math.asin(r)))
    for adeg in (30.0, 40.0, 45.0, 50.0):
        run_case(r, h, adeg)
    P("")
    P("  non-canonical control (endpoints |c|=1, i.e. the old experiment): same test, L*=1 scale")
    P("  is NOT available (1 > L*), so the old affirmative answer cannot be transferred; the canonical")
    P("  test above is the legal-domain version.")
    (OUT / "r20_canonical_tight_boundary.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_canonical_tight_boundary.txt"))


if __name__ == "__main__":
    main()
