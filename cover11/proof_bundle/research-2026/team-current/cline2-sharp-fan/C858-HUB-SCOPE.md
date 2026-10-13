# C858-HUB-SCOPE.md — Cartesian hub objective: curvature anatomy and two structural reductions

Owner: cline2-sharp-fan (own files only; no kernel write).  Companion to
HUB-DISK-AUDIT.md / C853-RIDGE-UNIFORM.md.  Instrument tools/cartesian_scope.py ->
out/p38_cartesian_scope.txt.  Responds to the lead's diagnostics: the naive Hessian cap fails
even locally (2.815 vs 2 sum lambda 1.198), so the normal-cone condition alone is NOT enough.

================================================================================
1. WHAT IS VERIFIED IN CARTESIAN-HUB-DISK-INTERSECTION.md / CARTESIAN-ANGLE-CANCELLATION.md
================================================================================
All confirmed:
 * phi1 = theta1 + delta and phi2 = theta2 - delta with theta_j = atan2(Y_j,X_j),
   X1 = v - D1cos b1, Y1 = D1 sin b1 - t, X2 = v - D2cos b2, Y2 = D2 sin b2 + t
   (checked to machine precision at four legal points; the hub is at -(v,t) in the c2 frame);
   hence the two direction cosines obey Y_j > 0.  Exact margins: for delta >= 0,
   H sin delta <= 2r sin(b1+A) sin delta = 2r(sin^2 b1 - sin^2 A) so Y1 >= 2r sin^2 A; for
   delta < 0 Y1 > 0 immediately; symmetrically Y2 >= 2r sin^2 B for delta <= 0.
 * cancellation: a1 phi1 + a2 phi2 + (z3-z1)delta = a1 theta1 + a2 theta2 (exact, since
   a1 - a2 = z1 - z3 and phi_j differ from theta_j by -+delta).
 * area identity (symbolic residual 0): area1+area2 = r(sin^2 b1 + sin^2 b2)v + r(sin b2 cos b2 -
   sin b1 cos b1)t = r(1 - cos T cos D)v - r cos T sin D t with T = b1+b2, D = b1-b2.
 * hub factor = (that affine part) + a1 theta1 + a2 theta2 + beta1 L1^2 + gamma1 L1
   + beta2 L2^2 + gamma2 L2, L_j = |hub - c_j| = |(X_j,Y_j)|,
   beta1 = 0.701924084, gamma1 = -1.145102454, beta2 = 0.693952741, gamma2 = -1.138494697.

================================================================================
2. CURVATURE ANATOMY — WHY THE NAIVE CAP FAILS, EXACTLY
================================================================================
Write û_j for the unit vector from Q_j := (D_j cos b_j, -+D_j sin b_j) to the hub; then
L_j = |(v,t) - Q_j| and  [CORRECTED FORMULA — the lead caught the dropped term]
   Hess(beta_j L_j^2 + gamma_j L_j) = 2 beta_j I + (gamma_j / L_j)(I - û_j û_j^T)
                                    = 2 beta_j û_j û_j^T + (2 beta_j + gamma_j/L_j)(I - û_j û_j^T),
with eigenvalues 2 beta_j (radial) and 2 beta_j + gamma_j/L_j (tangential).  (My first version
omitted the 2 beta_j (I - û_jû_j^T) part; the two eigenvalues I quoted were already the correct
ones, but the tensor expression was wrong and is fixed here.)  Since L_j <= 2r <= 0.76,
   2 beta_j + gamma_j / L_j <= 2 beta_j + gamma_j/0.76 = -0.102866 (j=1), -0.110114 (j=2),
(and 2 beta_j L_j + gamma_j <= -0.078178 resp. -0.083687 at L_j = 0.76), so the tangential part is
uniformly NEGATIVE; the RADIAL eigenvalue +2 beta_j is the whole failure of the naive cap
sum(2 beta + ...) ~ 2( beta1 + beta2 ) = 2.808 (the angle terms contribute only the observed
0.007).  This is exactly the convexity of beta L^2 + gamma L in L.
Angle terms: Hess(a_j theta_j) has eigenvalues +- a_j/L_j^2 and its POSITIVE eigendirection is
   w_j = (X_j + Y_j, Y_j - X_j)/|.| = the direction of û_j rotated by -pi/4,
an explicit vector, so the two angle terms do not share a single worst direction.
[... WITHDRAWN — the following per-term concavity claim was WRONG; see C858-CORRECTIONS.md ...]
The correct per-term statement in the orthonormal basis (û, û^perp) is the 2x2 matrix
   Hess(a theta - c L) = [[0, -a/L^2], [-a/L^2, -c/L]],   det = -a^2/L^4 < 0 for EVERY L,
so a single (angle - norm) term is INDEFINITE at every radius and no threshold of the form
L >= a/c can repair the mixed directions.  Concavity of a SUM of such terms is a genuine
whole-2x2 question, settled (in 2D) by trace <= 0 AND det >= 0, not by any single-term test.

================================================================================
3. REDUCTION A (secant): removes the radial convexity; concavity of the ENVELOPE is a separate
   whole-2x2 question (see C858-CORRECTIONS.md), NOT established by any per-term threshold
================================================================================
Convexity of phi_j(L) = beta_j L^2 + gamma_j L on [0,0.76] with phi_j(0) = 0 gives the secant
    beta_j L_j^2 + gamma_j L_j <= m_j L_j ,   m_j = 0.76 beta_j + gamma_j ,
    m_1 = -0.611640154,  m_2 = -0.611090614   (both strictly negative).
So the hub factor is bounded above by
    U(v,t) := r(1 - cos T cos D) v - r cos T sin D t + a1 theta1 + a2 theta2 - |m1| L1 - |m2| L2,
a sum of an affine function, two angle terms and two NEGATIVE multiples of norms.  The norm part is
NSD, with Hessian -( |m_j|/L_j )(I - û_jû_j^T)  (trace -( |m_j|/L_j ), eigenvalues 0 and
-|m_j|/L_j).  [WITHDRAWN: the claim that U is "concave wherever L_j >= a_j/|m_j|".  A single
(a_j theta_j - |m_j| L_j) term has Hessian [[0, -a/L^2],[-a/L^2, -c/L]] with negative determinant,
so the mixed directions are never fixed by any such threshold.  What remains true and useful:
trace(Hess U) = -( |m_1|/L_1 + |m_2|/L_2 ) < 0 automatically, and in 2D negative semidefiniteness
is equivalent to  det(Hess U) >= 0.  A derived SUFFICIENT condition is in C858-CORRECTIONS.md.]
Cost of the secant (exact at L = 0 and L = 0.76): phi_j(L_j) - m_j L_j = beta_j L_j(0.76 - L_j)
<= beta_j (0.38)^2 = 0.1014 per face, i.e. up to ~0.20 total — comparable to the 0.28 gap the
lead reports on the width side.  All of this is about the BOUND, and is unaffected by the
concavity withdrawal.

REDUCTION B (radial monotonicity, no secant slack).  phi_j'(L) = 2 beta_j L + gamma_j <= -0.0782
< 0 on [0,0.76], so phi_j is STRICTLY DECREASING: phi_j(L_j) <= phi_j(lambda_j) for any certified
lower bound lambda_j <= L_j, and also phi_j(L_j) <= 0 = phi_j(0).  Taking the better of the two
    beta_j L_j^2 + gamma_j L_j <= min( 0 , phi_j(lambda_j) )
removes the radial convexity at the exact price of the lambda_j bound.  Structural lambda_j —
NOTATION FIXED per lead: the law of sines in the face triangle (hub, c_j, c2) relates L_j to the
angle at c2 (which is A = b1 - delta for j=1 and B = b2 + delta for j=2, NOT the Cartesian
theta_j = atan2(Y_j,X_j) = phi_j -+ delta used elsewhere in this file):
    L_j / sin(angle at c2) = D_j / sin(phi_j),
and the face constraint (circumradius <= r, i.e. phi_j in [b_j, pi - b_j], sin phi_j >= sin b_j)
gives, writing thC_j for that angle at c2 (thC_1 = A, thC_2 = B),
    2 r sin b_j sin(thC_j) <= L_j <= 2 r sin(thC_j) / 1 = 2r sin(thC_j)·(sin b_j/sin b_j)…
    precisely:   L_j >= D_j sin(thC_j) = 2 r sin b_j sin(thC_j)    and
                 L_j <= D_j sin(thC_j)/sin b_j = 2 r sin(thC_j).
This derivation is elementary but must be stated with thC_j (the face angle at c2), otherwise the
symbol theta_j collides with the Cartesian angle and the bound is meaningless; the lead's caution
is accepted.  On the C853 box (b ~ 1.07, A,B ~ 1.07) this gives L_j >= ~0.58, and near a face
degeneracy thC_j -> 0 the bound degrades linearly.

================================================================================
4. RESULTING PROBLEM; second-order statement RESTATED (see C858-CORRECTIONS.md)
================================================================================
On the convex lens Omega (3 disks INTERSECT wedge), whichever reduction is used, the hub factor is
bounded above by a function of the form
    affine(v,t) + sum_j [ a_j theta_j - c_j L_j ]  (+ constants),
and its STATIONARY (interior) points satisfy, with û_j the unit vectors above,
    (r(1 - cos T cos D), -r cos T sin D)  =  sum_j c_j û_j  +  sum_j a_j grad theta_j
                                          + (normal-cone term),
i.e. a two-vector balance, with the constraint multipliers only from the active disk/wedge
boundaries.  [WITHDRAWN: "because the reduced function is concave ... the second-order condition is
decidable" — the per-term matrices are indefinite, so concavity must be established by the whole
2x2 criterion of C858-CORRECTIONS.md (trace < 0 automatic, determinant >= 0 the real condition,
with the derived sufficient version requiring the two radial directions to be separated).  Until
that criterion is verified on a region, the balance identity is only a stationarity condition, NOT
a sufficient one, and no global-optimality claim follows from it.  The observation that the
normal-cone condition alone is insufficient stands, and the secant still removes the RADIAL
eigenvalue +2 beta_j — it does not by itself remove the angle terms' mixed directions.]
Angle handling: without caps, theta_j < pi - b_j exactly (triangle angle sum: phi_j + (angle at
c_j) + (angle at c2) = pi, and the angle at c2 is thC_j = A resp. B > 0), and theta_j > 0 from
Y_j > 0, so sum_j a_j theta_j <= a1(pi - b1) + a2(pi - b2) <= 0.053745 on the C858 box — a
closed-form cap needing no search.  If that cap is too lossy, the exact extremal value of theta_j
over the convex lens is attained on a supporting line through Q_j (a short geometric computation),
not by grid.

================================================================================
5. SCOPE, HONESTLY
================================================================================
 * This is an UPPER-BOUND machinery for the hub factor, not an exact maximum: reduction A loses
   up to ~0.10 per face via the secant, reduction B loses only the lambda_j bound but needs
   lambda_j > 0 certified (which fails as theta_j -> 0).
 * Nothing here assumes the ridge maximises anything: the ridge is one point of Omega, and the
   balance/KKT characterisation decides where the reduced maximum sits within Omega.
 * No convexity or concavity of the ORIGINAL hub factor is claimed; the vertical curvature sign
   change the lead measured is reproduced here as the radial eigenvalue +2 beta_j.
 * Degeneracies to handle explicitly: L_j -> 0 (subgradient ball for |(v,t) - Q_j|), Y_j -> 0
   (closure of the domain, atan2 not smooth across the ray), and theta_j -> 0 (lambda_j -> 0).
 * Separability is unchanged, so the width-side slack (28.52 vs 28.24) is untouched by this note;
   the hub factor is an additive term.

STATUS: verified identities + curvature anatomy + two structural reductions with explicit
conditions and quantified slack.  No claim registered, no kernel write.

