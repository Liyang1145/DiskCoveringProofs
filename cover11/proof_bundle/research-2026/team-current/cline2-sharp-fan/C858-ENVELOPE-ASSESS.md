# C858-ENVELOPE-ASSESS.md — witness confirmed; envelope is promising, with a recipe and losses

Owner: cline2-sharp-fan.  Instrument tools/witness_check.py -> out/p39_witness_check.txt.
Companion to C858-HUB-SCOPE.md (curvature anatomy, secant/radial reductions).

================================================================================
1. WITNESS INDEPENDENTLY CONFIRMED
================================================================================
Recomputing with my own code on joint_nested_frozen.json:
 * the point (r,b1,b2,v,t) = (.3750951887748506, .9471039318692589, .9148561742031202,
   .4089871357815944, -.2502035007058863) is STRICTLY feasible: delta = -0.549024438583 lies in
   (-b2,b1), v > 0, face-disk residuals -0.001387769, -0.114776538, hub-disk residual
   -0.059581098, and the (automatic) separation margin is +0.087959.
 * hub factor witness = -0.45134479461042063891, ridge = -0.4975006139586483194,
   difference = +0.04615581934822768048916 — identical to the lead's interval
   [.0461558193482276804891637, .0461558193482276804891653] to the digits I print.
So the global-ridge-maximum hypothesis is indeed FALSE, while C855 feasibility and the C853
LOCAL box result are untouched: the witness has b1 = 0.9471, b2 = 0.9149, outside the C853 box
(b1 in [1.105,1.108], b2 in [1.068,1.071]).

================================================================================
2. IS A GENERAL UPPER ENVELOPE PROMISING? YES for the BOUND; concavity is an open obligation
================================================================================
[WITHDRAWN from this section per lead: (i) the claim that U_A "is CONCAVE on the region
{L_j >= a_j/|m_j|}"; (ii) the associated KKT-sufficiency/global-optimality claims; (iii) reduction
(B)'s lambda_j written with the symbol theta_j, which collided with the Cartesian angle.  Reason:
a single term a theta - c L has Hessian [[0,-a/L^2],[-a/L^2,-c/L]] in the (radial,tangential)
basis, determinant -a^2/L^4 < 0 at EVERY L, so no per-term threshold fixes the mixed directions;
and the radial Hessian I quoted earlier was missing the 2 beta (I - ûû^T) part (correct form
2 beta I + (gamma/L)(I - ûû^T)).  The correct whole-2x2 criterion and a derived sufficient version
are in C858-CORRECTIONS.md; the secant INEQUALITY itself and the loss accounting below remain
valid.]
Hub factor = affine(v,t) + a1 theta1 + a2 theta2 + beta1 L1^2 + gamma1 L1 + beta2 L2^2 + gamma2 L2
over the convex lens Omega (3 disks INTERSECT wedge), with
   affine = r(1 - cos T cos D) v - r cos T sin D t,  beta1=.7019240841, gamma1=-1.145102454,
   beta2=.6939527407, gamma2=-1.138494697,  a1=.012841585, a2=.013306528.
Two structural upper bounds, both analytic and grid-free:
 (A) SECANT (globally valid INEQUALITY).  beta_j L^2 + gamma_j L <= m_j L with m_j = 0.76 beta_j +
     gamma_j = -0.611640150, -0.611090614 < 0 (convexity of phi_j on [0,0.76], phi_j(0) = 0).
     U_A = affine + a1 theta1 + a2 theta2 - |m1|L1 - |m2|L2 is a valid upper bound; its norm part is
     negative semidefinite.  Loss vs truth: beta_j L_j (0.76 - L_j) <= beta_j (0.38)^2 = 0.1014 per
     face, so <= 0.203 in total.  Whether U_A is concave is NOT settled by any per-term condition —
     see C858-CORRECTIONS.md.
 (B) RADIAL MONOTONICITY (tighter locally).  phi_j' = 2 beta_j L + gamma_j <= -0.0782 < 0, so
     phi_j is strictly decreasing and phi_j(L_j) <= phi_j(lambda_j) for any certified
     lambda_j <= L_j.  The STRUCTURAL bound, restated with thC_j (the face angle at c2: A for j=1,
     B for j=2 — NOT the Cartesian theta_j), is L_j >= 2 r sin b_j sin(thC_j) and
     L_j <= 2 r sin(thC_j), from the law of sines plus sin phi_j >= sin b_j.  At the C853 box values
     this costs phi_j(lambda_j) ~ 0.43 against the secant's 0.35 (so B is better by ~0.07 per face
     there), and B has no radial-convexity defect.  Derivation required before use, as the lead
     asks; it is given in C858-CORRECTIONS.md section 4.
Stationarity of the envelope: on the interior of Omega the first-order condition is the two-vector
balance
   alpha = ( r(1 - cos T cos D), - r cos T sin D ) = c1 û1 + c2 û2 - a1 grad theta1 - a2 grad theta2,
with c_j = |m_j| (envelope A) or the effective radial slope (envelope B), û_j the unit vectors
from Q_j = (D_j cos b_j, -+ D_j sin b_j) to the hub, and grad theta_j of length 1/L_j; boundary
maxima add only the disk/wedge multipliers.  The angle contributions to the balance are a_j/L_j
(0.0172 and 0.0589 at the witness), small against c_j ~ 0.61, so the balance is norm-dominated.
[WITHDRAWN: "concavity makes KKT sufficient" — no concavity is established; the balance is a
NECESSARY stationarity condition only until the whole-2x2 determinant criterion of
C858-CORRECTIONS.md is verified on the region in question.  No normal-cone assumption is made
either way.]

================================================================================
3. HONEST LIMITS
================================================================================
 * The envelopes bound the HUB FACTOR only; separability is unchanged, so width-side slack is
   untouched by this.
 * Envelope A's <=0.203 total overhead is of the same order as the 0.046 ridge gap and the 0.28
   width gap, so if the certificate needs to be tight, envelope B on boxes with certified
   lambda_j, plus the angle cap sum a_j theta_j <= a1(pi-b1) + a2(pi-b2) <= 0.053745 or the exact
   extremal-ray value of theta_j, is the better route.
 * The witness shows the objective has an interior optimum in Omega; consistent with the earlier
   finding that F_H is neither monotone nor concave in H.  Nothing here contradicts C853.

STATUS: witness confirmed independently; envelope recipe given with explicit losses; no claim.
