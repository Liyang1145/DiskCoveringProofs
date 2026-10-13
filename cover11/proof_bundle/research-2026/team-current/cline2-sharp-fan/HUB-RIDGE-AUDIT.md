# HUB-RIDGE-AUDIT.md — independent audit of LOCAL-HUB-RIDGE-ELIMINATION.md

Owner: cline2-sharp-fan (own files only; no lead edits). Scope: LOCAL box only; not global.
Read: lead/LOCAL-HUB-RIDGE-ELIMINATION.md, certify_h_monotone_box.py, certify_delta_ridge.py,
check_ridge_feasibility.py, delta_ridge_feasibility.json, interval_patch_delta.py (for the
H-projection only).  Instrument: tools/ridge_independent_check.py -> out/p33_ridge_independent.txt
(my own C849 chart code and my own coefficient reader on the CURRENT joint_nested_frozen.json).

VERDICT: no concrete discrepancy found.  The inference from "FH' > 0 on the projected fiber"
+ "H upper = min(h1,h2)" + "the two branch derivatives have opposite signs" + "the ridge point
is feasible" to "the local maximiser is (delta*, H*) = (b1-b2, 2r sin(b1+b2)) on Q0" is valid.
Independent confirmations and the residual caveats follow.

================================================================================
1. WHAT THE CHAIN OF INFERENCE ACTUALLY IS (and why it closes)
================================================================================
For fixed (r,b1,b2,widths) the local relaxed objective is
   G(delta,H) = (z3-z1) delta + K'(r,b1,b2) + FH(delta,H),   delta = b1 - A, B = b2 + delta,
with FH strictly increasing in H (certified FH' >= .324122527 > 0 on the whole projected fiber),
so for every delta whose C848 fiber is nonempty the sup over H sits at
   H_max(delta) = min( h1(delta), h2(delta) ),  h1 = 2r sin(2b1-delta), h2 = 2r sin(2b2+delta).
On Q both sine arguments lie in (pi/2,pi), so h1 is strictly increasing and h2 strictly
decreasing in delta, and h1 = h2 exactly at delta* = b1 - b2 (the two arguments coincide:
2b1 - delta* = b1 + b2 = 2b2 + delta*).  Hence H_max = h1 for delta <= delta* and h2 for
delta >= delta*.  The two branch functions delta -> G(delta, h1(delta)) and G(delta, h2(delta))
have delta-derivatives of strictly opposite signs on the whole box, so the first increases up to
delta* and the second decreases after it; the ridge point is feasible (strictly, for every
(r,b1,b2) in Q0) and both branches meet there.  Therefore sup over (delta,H) = G(delta*,H*).
The widths do not enter (they are independent of delta and H), and no WLOG is used: the box is
asymmetric and separately bounded in b1 and b2, and the Q0 restriction b1 in [1.106,1.108]
forces delta* = b1-b2 in [0.035,0.040], exactly the delta-range of Q.

================================================================================
2. INDEPENDENT CHECKS (my own code, mpmath dps=40, current coefficients)
================================================================================
(2a) RIDGE TRIG DATA — CONFIRMED.  Constructing the two site faces from the chart
     (c2=(s,0), c1=c2+2r sin b1(-cos b1,-sin b1), c3=c2+2r sin b2(-cos b2,+sin b2),
      hub at c9 = c2 + H*(-cos delta,-sin delta)) and reading off the hub angles and the
     hub-to-ring edges at delta = delta*, H = H*:
        phi1 - b1 = 0,  phi2 - b2 = 0,  L1 - 2r sin b2 = 0,  L2 - 2r sin b1 = 0
     to machine zero (1e-41 at dps=40) at four (r,b1,b2) tuples, and h1 - H* = h2 - H* = 0
     exactly.  So "hubanglesphi1=b1,phi2=b2, L1=2rsinb2,L2=2rsinb1" and "both face upper
     constraints saturated exactly" are both correct.
(2b) RADICAL-FREE FORM — CONFIRMED, factor 4 included.  Direct two-face evaluation of
      FH = sum [ H y/2 + az atan2(y,x) + bz ee^2 + gz ee ],  ee = L/(2R0),
     at the ridge equals the radical-free expression
      FH* = 4r^2 sin(b1+b2) sin b1 sin b2 + (z1-z9) b1 + (z3-z9) b2
            - z16 t^2 sin^2 b2 - z78 t sin b2 + z20 t^2 sin^2 b1 + z82 t sin b1,  t = r/R0,
     to 1e-41.  The factor 4 is right: face 1 gives H r sin b1 sin b2 = 2r^2 sin(b1+b2) sin b1 sin b2
     and face 2 the same, and the two atan2 terms evaluate to b1 and b2 because the ridge
     identity H* - 2r sin b1 cos b2 = 2r cos b1 sin b2 holds.
(2c) BRANCH ORIENTATION — CONFIRMED.  On the box 2b1-delta in [2.170000, 2.181000] and
     2b2+delta in [2.171000, 2.182000], both strictly inside (pi/2, pi); therefore
     dh1/ddelta = -2r cos(2b1-delta) in [0.4286, 0.4344] > 0 and
     dh2/ddelta = +2r cos(2b2+delta) in [-0.4350, -0.4293] < 0, and h1 = h2 exactly at delta*.
(2d) CHAIN RULE / 2R NORMALISATION — CONFIRMED.  I recomputed the total branch derivative
     (z3-z1) + d/ddelta FH(delta, h_branch(delta)) by central finite differences of MY OWN FH
     and compared it with the analytic expression as coded in certify_delta_ridge.py; the
     agreement is 1e-22 at four (r,b1,b2,delta) tuples on both branches.  Term by term the
     coded factors are right: (Hd y + H yd)/2 for the linear term, az (x yd - y xd)/Q for the
     atan2 term, bz Qd/(4 R0^2) and gz Qd/(4 R0 sqrt(Q)) for the quad_range terms with
     ee = sqrt(Q)/(2R0), and xd,yd carry the correct td = -/+1 signs and Hd = -/+2r cos(arg).
     My finite-difference values (+0.1616..+0.1636 left, -0.1584..-0.1597 right) lie inside the
     certified intervals [0.09428710, 0.23048130] and [-0.22693327, -0.09032456].
(2e) FEASIBILITY — CONFIRMED.  My own evaluations at five (r,b1,b2) tuples, delta* = b1-b2,
     H* = 2r sin(b1+b2):  sep = H* - 2r|sin delta*| in [0.59403, 0.59700] > 0 and
     norm = H*^2 - 2 s cos(delta*) H* + 2r(1-r) in [-0.29410, -0.29285] < 0.  norm < 0 is
     exactly the C848 hub-norm condition for H*, whose roots s cos delta* +- sqrt(D) show it
     also yields the second lower bound H* >= s cos delta* - sqrt(D); the first lower bound is
     the sep check.  Both are strictly satisfied, so the ridge has a nonempty C848 fiber for
     every (r,b1,b2) in Q0, as stated.
(2f) DERIVATIVE COVERAGE.  FH' at the branch endpoints evaluates to +0.3722 (my own derivative
     of FH) at the sampled tuples, consistent with the certified lower bound .3241.  The
     H-projection [.3034806266617, .6271676523897] used by certify_h_monotone_box comes from
     interval_patch_delta.setup line 20, i.e. hl = max( (2r|sin delta|).a, (s cos delta - root).a, 0 )
     and hh = min( (2r sin(b1+A)).b, (2r sin(b2+B)).b, (s cos delta + root).b, (2r).b ): it takes
     the outward endpoints of the C848 bounds, so it contains the actual fiber at EVERY point of
     the outer box.  Since the active H (h1 or h2) lies in the actual fiber, it lies in the
     projected interval, so the monotonicity certificate applies to the branch points too.

================================================================================
3. NOTES (documentation nits only, no inference gap)
================================================================================
(N1) certify_h_monotone_box.py asserts the hub-norm upper bound is inactive (hubup.a > both
     faceupper.b) but does not assert the remaining C848 upper H <= 2r.  That is immediate from
     the numbers it already records: 2r >= 0.758 > faceupper_upper = .6275965948.  No gap, but
     worth one line if the certificate is read standalone.
(N2) The certificate names the conclusion "maximum at min(2r sin(2b1-delta), 2r sin(2b2+delta))";
     the delta-elimination needs, in addition, the branch-orientation fact (this is what makes
     min switch branches at delta*), which lives in certify_delta_ridge.py plus the (pi/2,pi)
     observation.  Both are present; the coupling is only in the prose.
(N3) Scope as stated is local and conditional: box Q/Q0, frozen joint_nested_frozen.json
     (all z50..z72 = 0, confirmed in my own read), necessary relaxation C849, no claim about the
     actual global cover or about the exterior parameter domain.  My audit confirms nothing
     beyond that local scope.

STATUS: inference audited and confirmed; no claim registered; no lead files modified.
