# C858-CORRECTIONS.md — withdrawal of the per-term concavity claim; correct 2x2 criterion

Owner: cline2-sharp-fan.  Supersedes the concavity/KKT statements in C858-HUB-SCOPE.md and
C858-ENVELOPE-ASSESS.md.  Lead's corrections accepted in full.

================================================================================
1. WHAT I GOT WRONG (accepted)
================================================================================
(W1) TENSOR FORM.  I wrote Hess(beta L^2 + gamma L) = 2 beta u u^T + (gamma/L)(I - u u^T), which
     drops the 2 beta (I - u u^T) part.  Correct:
        Hess(beta L^2 + gamma L) = 2 beta I + (gamma/L)(I - u u^T)
                                 = 2 beta u u^T + (2 beta + gamma/L)(I - u u^T),
     eigenvalues 2 beta (radial) and 2 beta + gamma/L (tangential).  The eigenvalues I quoted
     were already correct, the tensor expression was not.
(W2) PER-TERM CONCAVITY.  In the orthonormal basis (u, u^perp), with theta the polar angle,
        Hess(a theta - c L) = [[0, -a/L^2], [-a/L^2, -c/L]],   det = -a^2/L^4 < 0 for EVERY L.
     The matrix is INDEFINITE at every radius, so a threshold of the form L >= a/c does NOT make
     a single (angle - norm) term concave: the mixed (radial,tangential) entry is exactly what the
     determinant sees.  My "concavity threshold L_j >= a_j/|m_j|" and the "factor ~32 test passes"
     sentence were both wrong (the latter was also a malformed quadratic form: I dropped the
     negative part of the angle Hessian).  WITHDRAWN.
(W3) CONSEQUENCES WITHDRAWN.  Therefore: no claim of concavity for the secant envelope U_A, no
     claim that KKT is sufficient for it, no claim that a global optimum of the envelope is
     characterised by the two-vector balance, and no reduction-B coefficient claim that rests on
     the Cartesian symbol theta_j standing for the face angle at c2 (that was a notation collision,
     now fixed as thC_j below).
STILL VALID (unaffected by the above): the secant inequality beta_j L^2 + gamma_j L <= m_j L with
m_j = 0.76 beta_j + gamma_j < 0 (convexity + phi_j(0) = 0); the positivity Y_j > 0 and the angle
cancellation; the area identity; the disk and wedge geometry; the witness verification.

================================================================================
2. THE CORRECT WHOLE-2x2 CRITERION (the proof the lead asks for)
================================================================================
For U = affine + sum_j [ a_j theta_j - c_j L_j ]  (c_j = |m_j| for the secant envelope, or the
effective radial slope for reduction B) with u_j the unit vector from Q_j to the hub:
   Hess U = sum_j H_j ,    H_j = -(c_j/L_j)(I - u_j u_j^T) + (a_j/L_j^2) M_j ,
   M_j = 2 w_j w_j^T - I  (trace-free, M_j^2 = I, w_j = u_j rotated by -pi/4 = the positive
   eigendirection of the angle Hessian).
Trace:  tr(Hess U) = - ( c_1/L_1 + c_2/L_2 ) < 0    AUTOMATICALLY (each M_j is trace-free).
In 2D a symmetric matrix is negative semidefinite iff trace <= 0 AND determinant >= 0, so
     ** Hess U <= 0  <=>  det(Hess U) >= 0 **
and with the 2x2 identity det(A+B) = det A + det B + tr A tr B - tr(AB):
     det(Hess U) = - ( a_1^2/L_1^4 + a_2^2/L_2^4 ) + (c_1 c_2)/(L_1 L_2) - tr(H_1 H_2).
So concavity is a single scalar inequality; tr(H_1 H_2) is the only term that depends on the
relative orientation of the two radial frames (equivalently on u_1, u_2), which is exactly the
"radial directions separated" condition.  This is the honest form of the obligation.

================================================================================
3. A DERIVED SUFFICIENT CONDITION (valid, but only partial)
================================================================================
For a unit w, using w^T M_j w <= 1 (eigenvalues +-1) and the plane identity
max_alpha [ cos^2 alpha + cos^2(alpha - phi) ] = 1 + |cos phi|  (phi = angle between u_1,u_2):
    w^T (Hess U) w <= sum_j a_j/L_j^2 - min_j(c_j/L_j) * sum_j (1 - (w.u_j)^2)
                    <= sum_j a_j/L_j^2 - min_j(c_j/L_j) * (1 - |cos phi|).
Hence U is CONCAVE on any region where
    sum_j a_j/L_j^2  <=  (1 - |cos phi|) * min_j (c_j/L_j).
Numbers (secant envelope, c_j = |m_j|): at L = (0.6654, 0.6785) the two sides need
1 - |cos phi| >= 0.0579051/0.900649 = 0.0643, i.e. phi >= 20.6 degrees; at the witness point
(L1 = .7464, L2 = .2257) the requirement is 1 - |cos phi| >= 0.3468, i.e. phi >= 49.2 degrees.
So: concavity holds when the two radial directions are well separated, and the condition becomes
vacuous as they align — the sufficient test is real but NOT global, and near alignment needs a
different argument (e.g. merging the two nearly parallel norms).  This is offered as a derived
sufficient condition, not as a claim about the whole lens.

================================================================================
4. REDUCTION B RESTATED WITHOUT THE SYMBOL COLLISION
================================================================================
Let thC_j be the angle at c2 in the face triangle (hub, c_j, c2), so thC_1 = A = b1 - delta and
thC_2 = B = b2 + delta — NOT the Cartesian theta_j = atan2(Y_j,X_j) = phi_j -+ delta.  Law of
sines: L_j/sin(thC_j) = D_j/sin(phi_j) with D_j = 2r sin b_j, and the circumradius constraint gives
sin phi_j >= sin b_j, hence
    L_j >= 2 r sin b_j sin(thC_j)      and      L_j <= 2 r sin(thC_j).
This is the only place the structural bound is used; with thC_j written explicitly there is no
dependence on the Cartesian angle, and the bound must be re-derived (done above) before use.

STATUS: corrections applied to both C858 files; withdrawn claims marked; no claim registered.
