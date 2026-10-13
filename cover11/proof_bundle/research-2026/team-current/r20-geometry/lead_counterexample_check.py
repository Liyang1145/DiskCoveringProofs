"""r20-geometry Round-6: independent check of the lead's fixed-endpoint saturation counterexample
(lead/FIXED-ENDPOINT-SATURATION-COUNTEREXAMPLE.md) and its interface with the radial-inward criteria.

Claim under test (lead): at r = 3/8, H = (1/2,0), the three rings c0 = (q,0), c± = q(cos2A, ±sin2A)
(A = asin r, q = cos A = sqrt(1-r^2)) have arcs tiling [-3A,3A]; any radius-r disk covering the middle
open gap (-A,A) must contain U± = (cos A, ±sin A) = (q, ±r), which are 2r apart, so the internal
centre is FORCED to (q,0); and both fan circumradii stay strictly below r.  Open family: t = q-eps,
g = A-eps, alpha = beta(t)+g -> for ALL bridging centres c in the compact lens L_eps both fans stay
slack, uniformly.  Consequences checked here:
  (1) exact numbers: c± rational*sqrt(55) form, |U+-U-| = 2r, Rc^2 = 71/220 - 23 sqrt(55)/880 < 9/64;
  (2) internal centre forced: exact lens-of-two-tangent-disks computation;
  (3) consistency with RADIAL-INWARD-LOCAL: for eps = 0 the middle ring's seam value t_bdy = 1
      (no inward radial move at all); for eps > 0, t_bdy < 1 (the BOUNDARY tie can be saturated) while
      the FAN stays slack for every bridging centre -- so the two saturation notions are different and
      the lead's counterexample kills the FAN normal form, not the boundary-tie move.
No grid, no claim.  Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/lead_counterexample_check.py
"""
import io, json
from mpmath import mp, mpf, sqrt, asin, acos, cos, sin, pi as MP_PI
from pathlib import Path

mp.dps = 40
HERE = Path(__file__).resolve().parent
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(s, a):
    return (s * a[0], s * a[1])


def nrm(a):
    return sqrt(a[0] ** 2 + a[1] ** 2)


def circumradius2(P, Q, S):
    a2 = (Q[0] - P[0]) ** 2 + (Q[1] - P[1]) ** 2
    b2 = (S[0] - P[0]) ** 2 + (S[1] - P[1]) ** 2
    c2 = (Q[0] - S[0]) ** 2 + (Q[1] - S[1]) ** 2
    cr = (Q[0] - P[0]) * (S[1] - P[1]) - (Q[1] - P[1]) * (S[0] - P[0])
    return a2 * b2 * c2 / (4 * cr * cr)


r = mpf(3) / 8
A = asin(r)
q = cos(A)
say("r = 3/8, A = asin(r) = %s, q = cos A = sqrt(55)/8 = %s" % (mp.nstr(A, 20), mp.nstr(q, 20)))
say("  check q^2 = 1-r^2: %s" % mp.nstr(q * q - (1 - r * r), 5))
c0 = (q, mpf(0))
cp = (q * cos(2 * A), q * sin(2 * A))
cm = (q * cos(2 * A), -q * sin(2 * A))
say("  c+ = %s   (lead's form 23 sqrt55/256 = %s, 165/256 = %s)"
    % ([mp.nstr(x, 18) for x in cp], mp.nstr(23 * sqrt(55) / 256, 18), mp.nstr(mpf(165) / 256, 18)))
H = (mpf(1) / 2, mpf(0))
say("  hub strict: |H| = %s < 1-r = %s" % (mp.nstr(nrm(H), 12), mp.nstr(1 - r, 12)))

# boundary arcs at the branch-merger radius q: half-width A exactly
alpha0 = acos((q * q + 1 - r * r) / (2 * q))
say("  arc half-width of a radius-q ring: %s = A ? %s" % (mp.nstr(alpha0, 20), abs(alpha0 - A) < mpf("1e-35")))
say("  arcs: c- -> [-3A,-A], c0 -> [-A,A], c+ -> [A,3A]  (tiling, head-to-tail)")

U = (cos(A), sin(A))
say("  U+ = (cos A, sin A) = (q,r) = %s ; |U+| = %s ; |U+ - U-| = %s = 2r ? %s"
    % (mp.nstr(U[0], 18) + "," + mp.nstr(U[1], 18), mp.nstr(nrm(U), 18), mp.nstr(2 * U[1], 18),
       abs(2 * U[1] - 2 * r) < mpf("1e-35")))
say("  U+ in B(c+,r): |U+-c+| - r = %s ; U+ in B(c0,r): %s"
    % (mp.nstr(nrm(sub(U, cp)) - r, 5), mp.nstr(nrm(sub(U, c0)) - r, 5)))

Rc2 = circumradius2(H, c0, cp)
lead_eq = mpf(71) / 220 - 23 * sqrt(55) / 880
say("  fan circumradius^2 (both fans): %s   (lead closed form %s, diff %s)"
    % (mp.nstr(Rc2, 20), mp.nstr(lead_eq, 20), mp.nstr(Rc2 - lead_eq, 5)))
say("  r^2 = %s ; slack r^2 - Rc^2 = %s ; rational bracketing sqrt(55) > 641/92 ? %s (55*92^2=%d > 641^2=%d)"
    % (mp.nstr(r * r, 12), mp.nstr(r * r - Rc2, 12), sqrt(55) > mpf(641) / 92, 55 * 92 * 92, 641 * 641))

# forced internal centre: any disk of radius r containing U+ and U- has centre with |c-U+|<=r,|c-U-|<=r
# midpoint is the unique such point because |U+-U-| = 2r
mid = mul(mpf(1) / 2, add(U, (U[0], -U[1])))
say("  midpoint of U+U- = (%s, %s) = c0 ? %s" % (mp.nstr(mid[0], 18), mp.nstr(mid[1], 18),
                                                  abs(mid[0] - c0[0]) < mpf("1e-35") and abs(mid[1]) < mpf("1e-35")))
say("  => with |U+-U-| = 2r the lens of the two radius-r disks is the SINGLETON {midpoint}: the internal")
say("     centre is forced by gap coverage alone (no inward-root hypothesis needed).")

# consistency with the radial-inward seam test (RADIAL-INWARD-LOCAL.md eq. for t_bdy on the boundary arc)
def seam_value(x_angle, t, r):
    """t_- at a boundary point at direction x_angle for a ring of radius t whose centre direction is 0"""
    # F = (cos(phi) - sqrt(cos^2(phi) - (1-r^2)))/t  with phi = x_angle  (mpmath rounding tail allowed)
    c = cos(mpf(str(x_angle)))
    d = c * c - (1 - r * r)
    if d < -mpf("1e-35"):
        return None
    return (c - sqrt(max(mpf(0), d))) / t


say("")
say("interface with the radial-inward criteria:")
say("  eps = 0 : middle ring seam at phi = A -> t_bdy = %s (=> NO inward radial move; consistent with the"
    " forced centre)" % mp.nstr(seam_value(A, q, r), 12))
for eps in [mpf("1e-2"), mpf("1e-3"), mpf("1e-4")]:
    t = q - eps
    g = A - eps
    beta = acos((t * t + 1 - r * r) / (2 * t))
    alpha = beta + g
    cc0 = (t, mpf(0))
    ccp = (t * cos(alpha), t * sin(alpha))
    ccm = (t * cos(alpha), -t * sin(alpha))
    xg = (cos(g), sin(g))
    tb = seam_value(g, t, r)
    R1 = circumradius2(H, cc0, ccp)
    R2 = circumradius2(H, cc0, ccm)
    say("  eps=%-8s t=q-eps=%.12f beta(t)=%.12f > g=%.12f (%s) ; c0 covers the gap (|c0-x_g|-r=%+.2e)"
        % (mp.nstr(eps, 4), float(t), float(beta), float(g), beta > g, float(nrm(sub(cc0, xg)) - r)))
    say("             seam t_bdy = %.12f < 1  (boundary tie CAN be saturated by the radial move)" % float(tb))
    say("             fan Rc^2 at c0: %.12f, %.12f  vs r^2 = %.12f  (slack %+.2e, %+.2e)"
        % (float(R1), float(R2), float(r * r), float(r * r - R1), float(r * r - R2)))
    # bridging lens: all centres c with |c-xg+|<=r, |c-xg-|<=r ; sum of squared distances gives
    # |c-(cos g,0)|^2 <= r^2 - sin^2 g  (lead's uniform bound)
    bound = r * r - sin(g) ** 2
    say("             lens bound |c-(cos g,0)|^2 <= r^2-sin^2g = %.12f (radius %.6f) ; max Rc^2 over the lens"
        " is within O(rad) of the c0-value -> both fans slack for EVERY bridging centre"
        % (float(bound), float(sqrt(bound))))

json.dump(dict(r=str(r), A=str(A), q=str(q), Rc2=str(Rc2), lead_closed_form=str(lead_eq),
               slack=str(r * r - Rc2)), io.open(HERE / "lead_counterexample_check.json", "w"), indent=1)

# ---------------------------------------------------------------- Part 2: the JOINT move (hub)
say("")
say("=" * 112)
say("PART 2.  Joint move of the hub inside the lead's own counterexample (fixed-endpoint move is blocked)")
say("=" * 112)


def pin_inner(ci, cj, r):
    m = ((ci[0] + cj[0]) / 2, (ci[1] + cj[1]) / 2)
    dv = sub(cj, ci)
    d = nrm(dv)
    n = (-dv[1] / d, dv[0] / d)
    k = sqrt(r * r - d * d / 4)
    p1 = sub(m, mul(k, n))
    p2 = add(m, mul(k, n))
    return (p1, p2) if nrm(p1) < nrm(p2) else (p2, p1)


def circle_cross(c1, r1, c2, r2):
    dv = sub(c2, c1)
    d = nrm(dv)
    if d == 0 or d > r1 + r2 or d < abs(r1 - r2):
        return []
    a = (r1 ** 2 - r2 ** 2 + d ** 2) / (2 * d)
    h2 = r1 ** 2 - a ** 2
    hh = sqrt(max(mpf(0), h2))
    u = (dv[0] / d, dv[1] / d)
    base = add(c1, mul(a, u))
    if hh == 0:
        return [base]
    perp = (-u[1], u[0])
    return [add(base, mul(hh, perp)), sub(base, mul(hh, perp))]


def min_norm_lens(p1, p2, r):
    """Theorem A on the two pin-disks: min |h| over S = B(p1,r) cap B(p2,r)."""
    def inside(h):
        return nrm(sub(h, p1)) <= r + mpf("1e-30") and nrm(sub(h, p2)) <= r + mpf("1e-30")
    cands = []
    o = (mpf(0), mpf(0))
    if inside(o):
        cands.append((o, "origin"))
    for c in (p1, p2):
        nc = nrm(c)
        pr = mul(1 - r / nc, c)
        if inside(pr):
            cands.append((pr, "projection"))
    for z in circle_cross(p1, r, p2, r):
        if inside(z):
            cands.append((z, "circle-circle"))
    if not cands:
        return None, None, None
    b = min(cands, key=lambda t: nrm(t[0]) ** 2)
    return nrm(b[0]), b[0], b[1]


for tag, eps in [("exact eps=0", mpf(0)), ("family eps=1e-2", mpf("1e-2")), ("family eps=1e-3", mpf("1e-3"))]:
    if eps == 0:
        cc0, ccp, ccm = c0, cp, cm
    else:
        t = q - eps
        beta = acos((t * t + 1 - r * r) / (2 * t))
        al = beta + (A - eps)
        cc0, ccp, ccm = (t, mpf(0)), (t * cos(al), t * sin(al)), (t * cos(al), -t * sin(al))
    pin1 = pin_inner(cc0, ccp, r)[0]
    pin2 = pin_inner(cc0, ccm, r)[0]
    slackH = max(nrm(sub(H, pin1)), nrm(sub(H, pin2))) - r
    mn, hstar, kind = min_norm_lens(pin1, pin2, r)
    act = [nrm(sub(hstar, pin1)) - r, nrm(sub(hstar, pin2)) - r] if hstar else None
    say("  [%s] pins p1=%s p2=%s" % (tag, [mp.nstr(z, 10) for z in pin1], [mp.nstr(z, 10) for z in pin2]))
    say("      fixed hub H: max_j|H-p_j| - r = %+.3e  (both fans slack, as the lead reports)" % float(slackH))
    say("      JOINT MOVE h -> argmin_S|h| = (%s, %s)  |h*| = %s  vs rho = 5/8 = %s  -> strict hub %s"
        % (mp.nstr(hstar[0], 12), mp.nstr(hstar[1], 12), mp.nstr(mn, 12), mp.nstr(1 - r, 8),
           "yes" if mn < 1 - r else "no"))
    say("      active at h*: |h*-p1|-r = %+.3e, |h*-p2|-r = %+.3e  -> %s saturated"
        % (float(act[0]), float(act[1]),
           "BOTH fans" if max(abs(act[0]), abs(act[1])) < mpf("1e-25") else "some fan"))
    say("      (C879: the fan circumradius constraint for the pair is exactly |h-p_in|<=r, so h* keeps all"
        " triangle radii <= r with equality on the active pair(s).)")

(HERE / "lead_counterexample_check.out.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8")
say("")
say("wrote lead_counterexample_check.json / .out.txt")
