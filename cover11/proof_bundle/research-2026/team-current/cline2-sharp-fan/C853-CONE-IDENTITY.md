# C853-CONE-IDENTITY.md — independent check of the (T,D,eps) cap identity and the (u,eps) chart

Owner: cline2-sharp-fan (own files only; no kernel write).  Instrument
tools/cone_identity_check.py -> out/p36_cone_identity.txt.

================================================================================
1. THE IDENTITY — CORRECT
================================================================================
Claim: with T = b1+b2, D = b1-b2, eps = delta - D, so that A = b2 - eps, B = b1 + eps and
the two face arguments are b1+A = T - eps and b2+B = T + eps,
      min( sin(T+eps), sin(T-eps) ) = sinT cos eps - |cos T sin eps| = sin(beta - |eps|),
      beta := min(T, pi-T)  (so T in (0,pi) => beta in (0,pi/2]).
Verified:
 * reparametrisation exact (sympy differences all 0): A-(b2-eps), B-(b1+eps),
   (b1+A)-(T-eps), (b2+B)-(T+eps);
 * the two-form identity checked numerically at nine (T,eps) pairs spanning T below and above
   pi/2 and eps of both signs, including |eps| > 1 and T near pi: all three expressions
   (direct min, sinT cos eps - |cos T sin eps|, sin(beta-|eps|)) agree to 10 digits.
 * derivation: sin(T±eps) = sinT cos eps ± cosT sin eps, so the smaller one is obtained by
   adding the term of opposite sign, i.e. -|cosT sin eps|; writing sin beta = sinT and
   cos beta = |cos T| (valid for beta = min(T,pi-T)) gives exactly sin(beta-|eps|).
RANGE OF VALIDITY (one refinement to the lead's phrasing): the identity needs only |eps| <= pi,
not |eps| < pi/2.  The bound |eps| < pi/2 is automatic here anyway, because A = b2-eps > 0 and
B = b1+eps > 0 give eps in (-b1, b2), hence |eps| < max(b1,b2) < pi/2 on the chart domain.
The binding condition is not |eps| < pi/2 but |eps| < beta, which is exactly the positivity of
the cap.

================================================================================
2. CAP, CONE AND RIDGE MAXIMALITY — CORRECT
================================================================================
 cap(eps) := min(2r sin(T+eps), 2r sin(T-eps)) = 2r sin(beta-|eps|)
  * cap is EVEN in eps and strictly decreasing in |eps|, so it is maximised at eps = 0 — the
    ridge — with cap(0) = 2r sin(beta) = 2r sin T = min(h1,h2) there.  This holds in BOTH
    regimes (beta = T acute, beta = pi-T obtuse): the ridge maximises the face H-cap globally,
    with no obtuse hypothesis.  (This is the global version of the Round-15 box observation.)
  * a nonempty fiber with H > 0 needs 0 < H <= cap(eps), i.e. beta - |eps| > 0, i.e. |eps| < beta;
  * substituting H = 2r sin u, u := asin(H/(2r)) in (0, pi/2), gives beta - |eps| >= u, i.e.
        **  |eps| + u <= beta  **   — linear in (|eps|, u), the "exact cone constraint".
    The equivalence is exact because beta <= pi/2 and asin is increasing on [0, pi/2], so
    H <= 2r sin(beta-|eps|)  <=>  u <= beta - |eps|.
  * ACTIVE-FACE FLIP: sin(T-eps) < sin(T+eps) <=> cosT sin eps > 0, so the T-eps face (i.e. the
    b1+A bound) is the active one iff eps cosT > 0: for eps > 0 when T < pi/2 (acute) and for
    eps < 0 when T > pi/2 (obtuse).  The flip is at T = pi/2, and both branches produce the same
    cap, which is why the cap statement is regime-independent.

================================================================================
3. NO MISSING ARGUMENTS UNDER FEASIBILITY — CORRECT
================================================================================
A and B are the angles at c2 in the two site faces, so A,B in (0,pi); note A+B = T, so
T in (0,2pi).  Then T-eps = b1+A in (0, 3pi/2) and T+eps = b2+B in (0, 3pi/2), both inside
(0,2pi).  A nonempty fiber requires both face uppers to be positive, i.e. sin(T-eps) > 0 and
sin(T+eps) > 0, and on (0,2pi) this forces both arguments into (0,pi).  So no feasible branch
has an argument outside (0,pi), and the beta-form of the min is the correct one on every
feasible configuration (beta = min(T,pi-T) with T in (0,pi)).

================================================================================
4. THE (u,eps) CHART — WHAT IS LINEAR AND WHAT IS NOT
================================================================================
In coordinates (eps, u) with H = 2r sin u:
  * the FACE CAP is exactly the linear triangle   |eps| + u <= beta,  u >= 0,
    with vertices (eps,u) = (0,0), (+-beta,0), (0,beta); the ridge sits at the vertex (0,beta).
  * the remaining C848 constraints are trigonometric as they stand:
       separation  H >= 2r|sin delta|,  delta = D+eps   <=>   sin u >= |sin(D+eps)|,
       hub norm    H^2 - 2s cos(delta) H + 2r(1-r) <= 0
                   <=>   4r^2 sin^2 u - 4rs cos(D+eps) sin u + 2r(1-r) <= 0.
    Note the separation constraint IS piecewise linear in (eps,u) once the branch of delta is
    fixed: for delta in (0,pi], |sin delta| <= sin u  <=>  u >= delta  or  u >= pi - delta;
    the hub-norm one stays quadratic in sin u and linear in cos(D+eps).  So the fiber is the
    cone triangle cut by a piecewise-linear strip (separation) and a trig strip (hub norm) —
    the "linear triangle" describes the face-cap part exactly, not the whole fiber.
  * ridge-feasibility facts from the previous rounds apply to eps = 0; for eps != 0 the hub-norm
    constraint is generally active and must be carried.

STATUS: identity, cap/cone form, ridge maximality, active-face flip and the no-missing-arguments
claim all independently confirmed; one refinement (|eps| <= pi suffices for the identity; the
binding condition is |eps| < beta).  No claim registered, no kernel write.
