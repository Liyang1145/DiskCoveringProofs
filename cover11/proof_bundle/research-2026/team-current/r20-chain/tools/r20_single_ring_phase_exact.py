"""Fixed-H SINGLE-RING exact phase optimisation (lead's new small obligation).

Writes ../out/r20_single_ring_phase_exact.txt.  Read-only outside r20-chain.  No chain claims, no
tightening claims: one ring, fixed hub, exact max/min of the spoke angle over the admissible phases,
plus the rigorous phase interval(s) for the two-endpoint (gap) constraint.

SETTING.  Unit boundary circle; radius r; a FIXED strict hub H with |H| < 1-r; a ring centre c with
FIXED inward radius rho = |c| in [1-r, L*], L* = sqrt(1-r^2); the ring must COVER a prescribed boundary
arc, given either as one arc of half-width a, or (the usable case) as the GAP between two already
covered boundary points U_1, U_2 with azimuths v_1 <= v_2.

SPOKE ANGLE.  s(c) = arccos( |H - c| / (2r) ), defined only for |H - c| <= 2r.

(P1) COVERING A GAP = COVERING ITS ENDPOINTS — only for the SHORT gap (lead's correction).
     Hypothesis needed: the required arc is the SHORT one between U_1, U_2, of width v_2 - v_1 <= pi.
     Without it the equivalence is FALSE: with the same two endpoints the LONG arc (width > pi) is not
     covered by a disk that covers both endpoints (a disk covers at most an arc of width 2a <= pi).
     Under the hypothesis, x -> |c-x| along the required arc is maximal at an endpoint UNLESS the
     antipode of c's direction lies inside the arc; there max = |c| + 1 > r because |c| >= 1-r, so such
     c cannot cover the arc anyway.  Hence for admissible c:
         the ring covers the whole (short) gap  <=>  |c - U_1| <= r and |c - U_2| <= r.
(P2) PHASE INTERVAL.  With c = rho (cos phi, sin phi) and a := arccos((1 + rho^2 - r^2)/(2 rho))
     (the ring's own boundary half-width, so a = beta(rho)):
         |c - U_j| <= r   <=>   cos(phi - v_j) >= cos a   <=>   phi in [v_j - a, v_j + a].
     Hence the admissible phase set is EXACTLY the interval
         Phi(rho; v_1, v_2) = [v_2 - a, v_1 + a]        (mod 2 pi),
     nonempty  <=>  the gap width v_2 - v_1 <= 2a  <=>  rho >= the minimal radius whose arc spans the
     gap.  (Short-gap hypothesis as in (P1).)  The antipode condition is automatic: a < pi/2.
(P3) DISTANCE QUADRATIC.  |H - c(phi)|^2 = |H|^2 + rho^2 - 2 rho |H| cos(phi - psi_H), psi_H = arg H.
     So phi -> |H - c| is unimodal on the circle: minimum at phi = psi_H, maximum at phi = psi_H + pi.
     Since s = arccos(d/(2r)) is DECREASING in d (arccos decreasing), s is MAXIMISED where d is
     MINIMISED and vice versa.  DEGENERATE CASE H = 0: psi_H is undefined and d ≡ rho; then s is the
     constant arccos(rho/(2r)) and no phase optimisation exists (handled separately below).
(P4) EXACT EXTREMA ON THE ADMISSIBLE DOMAIN (lead's corrections applied).
     * s is DEFINED only for d <= 2r.  Since d^2 = |H|^2 + rho^2 - 2 rho|H| cos(phi - psi_H), the
       condition d <= 2r is again a cosine inequality and contributes an interval; the true admissible
       domain is
           Dome = Phi  ^  { phi : d(phi) <= 2r }        (intersection of up to three intervals).
       On Dome (nonempty only), d_min is at the projection of psi_H onto Dome and d_max at the
       farthest point of Dome from psi_H (an endpoint of Dome, or psi_H + pi if that phase is inside);
       s_max = arccos(d_min/(2r)), s_min = arccos(d_max/(2r)).
     * The projection and the "farthest" phase are computed CIRCULARLY modulo 2 pi (candidates
       psi_H + 2 pi k for all k with the clamped/candidate phase inside the interval).
     * H = 0: s ≡ arccos(rho/(2r)) (constant) — separate case, no phase.
     Both are closed-form: no grid, no iteration.
(P5) TWO CONSTRAINTS.  If the ring must simultaneously serve two gaps (equivalently two pairs of
     endpoints), the admissible set is the INTERSECTION of the corresponding intervals (and of the
     d <= 2r interval), listed rigorously below (possibly empty, possibly a single phase).
"""
import math
from pathlib import Path
from mpmath import mp, mpf, sqrt, acos, atan2, pi as MP_PI

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def wrap(x):
    """wrap an angle into (-pi, pi]."""
    while x <= -MP_PI:
        x += 2*MP_PI
    while x > MP_PI:
        x -= 2*MP_PI
    return x


def beta(rho, r):
    """ring boundary half-width (canonical domain)."""
    val = (1 + rho*rho - r*r)/(2*rho)
    val = min(mpf(1), max(mpf(-1), val))
    return acos(val)


def dist2(phi, H, rho):
    Hn = sqrt(H[0]**2 + H[1]**2)
    return Hn*Hn + rho**2 - 2*rho*Hn*mp.cos(phi - atan2(H[1], H[0]))


def phase_interval(rho, r, v1, v2):
    """(P2) with the short-gap hypothesis (P1): returns (interval or None, a, short_gap_flag)."""
    a = beta(rho, r)
    short = (v2 - v1) <= MP_PI
    if (v2 - v1) > 2*a:
        return None, a, short
    return (v2 - a, v1 + a), a, short


def dom_interval(rho, H, r):
    """(P4) {phi : |H - c(phi)| <= 2r}, where s is defined: None = empty, (-inf,inf) = full circle."""
    Hn = sqrt(H[0]**2 + H[1]**2)
    if Hn == 0:
        return (mpf('-inf'), mpf('inf'))          # H = 0: s constant, no phase restriction
    val = (rho*rho + Hn*Hn - 4*r*r)/(2*rho*Hn)
    if val <= -1:
        return (mpf('-inf'), mpf('inf'))
    if val > 1:
        return None
    c0 = acos(val)
    psi = atan2(H[1], H[0])
    return (psi - c0, psi + c0)


def project_and_farthest(lo, hi, H, rho):
    """(P4) circular projection of psi_H onto [lo,hi] and the farthest phase in it."""
    psi = atan2(H[1], H[0])
    best = None
    for k in range(-3, 4):
        a, b = lo + 2*MP_PI*k, hi + 2*MP_PI*k
        t = min(max(psi, a), b)
        key = abs(wrap(t - psi))
        if best is None or key < best[0]:
            best = (key, t)
    phi_proj = best[1]
    tt = []
    for k in range(-3, 4):
        a, b = lo + 2*MP_PI*k, hi + 2*MP_PI*k
        tt += [a, b]
        t = psi + MP_PI + 2*MP_PI*k
        if a <= t <= b:
            tt.append(t)
    phi_far = max(tt, key=lambda t: dist2(t, H, rho))
    return phi_proj, phi_far


def main():
    mp.dps = 30
    P("=" * 100)
    P("FIXED-H SINGLE-RING PHASE OPTIMISATION — exact statements (P1)-(P5) in the header")

    P("")
    P("CALIBRATION 1 (the lead's O5 pinned configuration): r = 3/8, H = (1/2,0), rho = q = sqrt(55)/8,")
    P("gap = (-A, A) with A = asin r  =>  a = beta(rho) = A and Phi = [A - A, -A + A] = {0}: singleton.")
    r1 = mpf(3)/8
    H1 = (mpf(1)/2, mpf(0))
    rho1 = sqrt(mpf(55))/8
    A1 = acos(rho1)                    # = asin(3/8)
    iv1, a1, sh1 = phase_interval(rho1, r1, -A1, A1)
    P("   beta(rho) = %.15f ; A = %.15f ; equal: %s" % (float(a1), float(A1), abs(a1-A1) < mpf('1e-25')))
    P("   admissible phase interval = [%.3e, %.3e]  (single phase 0: the pinning)"
      % (float(iv1[0]), float(iv1[1])))
    lo1, hi1 = iv1
    pmin, pmax = project_and_farthest(lo1, hi1, H1, rho1)
    dmin = sqrt(dist2(pmin, H1, rho1)); dmax = sqrt(dist2(pmax, H1, rho1))
    P("   closest phase = %.3e -> d_min = %.15f -> s_max = arccos(d/(2r)) = %.15f"
      % (float(pmin), float(dmin), float(acos(dmin/(2*r1)))))
    P("   farthest phase = %.3e -> d_max = %.15f -> s_min = %.15f"
      % (float(pmax), float(dmax), float(acos(dmax/(2*r1)))))
    P("   NOTE: s = arccos(|H-c|/(2r)) is the SPOKE angle, a different object from the fan")
    P("   circumradius Rc of the triangle (c_+, c, H); no cross-comparison between them is made.")

    P("")
    P("CALIBRATION 2 (record object 3-ring gap, r = 0.3799838531198387): hub H = (-1.62043e-4,")
    P("-1.49428e-1) (row 0), internal ring radius rho = 0.700870054167 ; gap endpoints v_1, v_2 taken")
    P("from the two neighbouring rings' inner arc ends.")
    from mpmath import mpf as M
    r2 = M('0.37998385311983870905')
    H2 = (M('-0.000162042987'), M('-0.149428411085'))
    rho2 = M('0.700870054167046975')          # |central ring of the record 3-ring gap|
    P("   beta(rho) = %.12f rad = %.6f deg ; so any gap of width <= 2 beta(rho) = %.12f rad is servable"
      % (float(beta(rho2, r2)), float(beta(rho2, r2)*180/MP_PI), float(2*beta(rho2, r2))))
    v1, v2 = M('-0.2'), M('0.2')              # gap width 0.4 rad < 2 beta = 0.5616
    iv2, a2, sh2 = phase_interval(rho2, r2, v1, v2)
    P("   gap width 0.4 rad ; 2 beta(rho) = %.12f rad -> %s"
      % (float(2*a2), "nonempty" if iv2 else "EMPTY (gap wider than the ring's arc)"))
    if iv2:
        P("   admissible phases = [%.12f, %.12f] (width %.12f)"
          % (float(iv2[0]), float(iv2[1]), float(iv2[1]-iv2[0])))
        pmin2, pmax2 = project_and_farthest(iv2[0], iv2[1], H2, rho2)
        d1 = sqrt(dist2(pmin2, H2, rho2)); d2 = sqrt(dist2(pmax2, H2, rho2))
        P("   s_max = %.12f at phase %.12f (closest phase) ; s_min = %.12f at phase %.12f"
          % (float(acos(d1/(2*r2))), float(pmin2), float(acos(d2/(2*r2))), float(pmax2)))
        P("   sanity: both s values are in (0, pi/2) and s_max > s_min: %s"
          % (0 < float(acos(d1/(2*r2))) < float(MP_PI)/2 and float(acos(d1/(2*r2))) > float(acos(d2/(2*r2)))))
    # consistency check: an actual ring phase must lie inside its own gap's interval
    phi_ring = M('0.0')                        # a ring phase serving gap [-0.2, 0.2]
    P("   consistency: a ring at phase %.3f serving the gap [-0.2,0.2] is admissible: %s"
      % (float(phi_ring), bool(iv2 and iv2[0] <= phi_ring <= iv2[1])))

    P("")
    P("TWO-CONSTRAINT CASE (P5): the ring must serve two gaps; admissible set = interval intersection")
    P("   gap A = [v1a, v2a] -> phases [v2a - a, v1a + a] ; gap B = [v1b, v2b] -> [v2b - a, v1b + a]")
    a = beta(rho2, r2)
    cases = [("overlapping", (M('-0.20'), M('-0.05')), (M('0.05'), M('0.20'))),
             ("touching", (M('-0.60'), M('-0.40')), (M('-0.2384'), M('-0.0384'))),
             ("disjoint-far", (M('-1.00'), M('-0.90')), (M('0.90'), M('1.00')))]
    for nm, (v1a, v2a), (v1b, v2b) in cases:
        ia, _, _ = phase_interval(rho2, r2, v1a, v2a)
        ib, _, _ = phase_interval(rho2, r2, v1b, v2b)
        if ia is None or ib is None:
            P("   %-14s : one gap exceeds the ring arc -> EMPTY" % nm)
            continue
        lo = max(ia[0], ib[0]); hi = min(ia[1], ib[1])
        if lo > hi:
            P("   %-14s : intervals [%.4f,%.4f] and [%.4f,%.4f] -> INTERSECTION EMPTY"
              % (nm, float(ia[0]), float(ia[1]), float(ib[0]), float(ib[1])))
        else:
            P("   %-14s : intersection = [%.6f, %.6f] (width %.6f) -> admissible phases form one interval"
              % (nm, float(lo), float(hi), float(hi-lo)))
    P("   (mod 2pi wrap: each interval is listed in unwrapped coordinates; if v_2 < v_1 the gap crosses")
    P("    azimuth 0 and the interval is to be read modulo 2 pi.)")

    P("")
    P("SCOPE: one ring, fixed hub, exact phase statements.  NO chain/tightening inference is drawn")
    P("   here (the withdrawn §5.10 route is recorded separately in DEAD.md).  All formulas closed-form.")

    (OUT / "r20_single_ring_phase_exact.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_single_ring_phase_exact.txt"))


if __name__ == "__main__":
    main()
