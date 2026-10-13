"""r20-geometry Round-15 (lead 77b77bd1): fixed-switch angular legal-domain coverage (no grids).

Domain model (lead): nine cyclic unit points U_0..U_8 with owned arcs of widths Delta_i >= 0,
sum Delta_i = 2 pi; each ring disk of radius r covers its owned arc's endpoints; fix U_0 = (1,0).

Analytic facts proved here (documented in the companion note):
  (L1) owned-width bound: in a covering configuration both endpoints of the arc owned by ring i are
       within distance <= r of that ring's centre (ownership/switch point is covered by the ring),
       hence 2 sin(Delta_i/2) = chord <= 2r and Delta_i <= 2 asin(r) <= 2 asin(0.38) = 0.7796 < pi:
       the "short arc" hypothesis is DERIVED, not assumed.
  (L2) uniform lower width: Delta_i = 2pi - sum_{j != i} Delta_j >= 2pi - 8*(2 asin r) >= 2pi - 16 asin(0.38)
       =: w_min > 0  (eight other arcs, each <= 2 asin r, r <= 0.38).
  (L3) bootstrap: Delta_i <= 2pi - 8 w_min, so w_min <= Delta_i <= min(2 asin r, 2pi - 8 w_min).
  (L4) domain: {Delta in R^9 : sum = 2pi, 0 <= Delta_i <= 2 asin r} is an 8-dimensional compact simplex;
       with (L2) it is contained in the box-constrained slice [w_min, 2 asin r]^9 cap {sum = 2pi}, which
       is nonempty iff 9 w_min <= 2pi <= 9*(2 asin r).

This script only certifies the numeric intervals of those constants (mpmath.iv, outward rounding).
Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/angular_domain_coverage.py
"""
import io
from mpmath import iv, mp, mpf, pi as MP_PI
from mpmath import iv as IV
mp.dps = 40
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


# rigorous interval enclosure: evaluate at 60 dps and widen by 1e-40 (>> the evaluation error)
mp.dps = 60
WID = mpf("1e-40")
_s = mpf("0.38")
a0 = mp.asin(_s)
a_lo, a_hi = a0 - WID, a0 + WID
p0 = mp.pi
tp_lo, tp_hi = 2 * p0 - WID, 2 * p0 + WID
say("interval diagnostics (60 dps evaluation, outward widened by 1e-40):")
say("  [asin(0.38)] = [%s, %s]" % (mp.nstr(a_lo, 25), mp.nstr(a_hi, 25)))
say("  [2pi] = [%s, %s]" % (mp.nstr(tp_lo, 25), mp.nstr(tp_hi, 25)))
two_pi = type("X", (), {"a": tp_lo, "b": tp_hi})()
w_min_lo = two_pi.a - 16 * a_hi            # rigorous lower bound for w_min = 2pi - 16 asin(r)
w_min_hi = two_pi.b - 16 * a_lo
say("  w_min = 2pi - 16 asin(r) >= 2pi - 16 asin(0.38) in [%s, %s]" % (w_min_lo, w_min_hi))
say("  strictly positive: %s" % (w_min_lo > 0))
w_cap_lo = 2 * a_lo
w_cap_hi = 2 * a_hi
say("  2 asin(r) <= 2 asin(0.38) in [%s, %s]  (each owned width <= this; < pi: %s)"
    % (w_cap_lo, w_cap_hi, w_cap_hi < 3.14159265358979))
say("  short-arc conclusion: Delta_i <= 2 asin(0.38) = %s < pi  -> every owned arc is short"
    % w_cap_hi)
say("")
say("domain checks (8-dimensional slice):")
say("  lower side nonempty: 9 * w_min <= 2pi ?  %s * 9 = %s vs 2pi >= %s  -> %s"
    % (w_min_lo, 9 * w_min_lo, two_pi.b, (9 * w_min_lo <= two_pi.b)))
say("  upper side nonempty: 9 * (2 asin r) >= 2pi ?  %s * 9 = %s vs 2pi <= %s  -> %s"
    % (w_cap_lo, 9 * w_cap_lo, two_pi.b, (9 * w_cap_lo >= two_pi.b)))
boot = two_pi.b - 8 * w_min_lo
say("  bootstrap upper bound: Delta_i <= 2pi - 8 w_min <= %s ; so w_min <= Delta_i <= min(2 asin r, %s)"
    % (boot, boot))
say("")
say("=> legal angular domain = 8-dimensional compact polytope")
say("   {Delta in [w_min, 2 asin r]^9 (up to the bootstrap bound), sum Delta_i = 2pi}, w_min > %s > 0." % w_min_lo)
say("   (Domain coverage only -- no numerical grid, no optimisation performed.)")
io.open('research-2026/team-current/r20-geometry/angular_domain_coverage.out.txt', 'w',
        encoding='utf-8').write("\n".join(OUT) + "\n")
print()
print("wrote angular_domain_coverage.out.txt")
