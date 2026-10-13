# C868-FACE-ARC-MECHANISM.md — face-arc vs ridge: reduced form of the difference

Owner: cline2-sharp-fan (own files, own instrument).  Instrument tools/face_arc_difference.py ->
out/p45_face_arc.txt.  Pure mechanism at formula level; no large run; own derivatives only where
verified symbolically.

================================================================================
1. THE FACE-ARC CHART, MADE EXPLICIT (all three identities symbolic, residual 0)
================================================================================
Face 1 saturated (the lead's chart): A = b1 - delta free, H = 2r sin(b1+A), hub = H(cos delta,
sin delta).  Then exactly
   (i)   (v,t) = ( H cos delta, H sin delta ) = r( sin2b1 + sin2A , cos2A - cos2b1 ),
   (ii)  L1^2 = |hub - c1|^2 = (2 r sin A)^2,   c1 = (r sin2b1, 2r sin^2 b1),
   (iii) sin^2 phi1 = sin^2 b1,   phi1 = atan2(D1 sin A, H - D1 cos A),  D1 = 2r sin b1.
(iii) says: the face-1 circle IS the locus {circumradius = r}, and there the law of sines gives
sin phi1 = D1/(2R_circ) = sin b1; numerically on the C868 arc phi1 == b1 to 10 digits.  So
** the a1 angle term is CONSTANT along the face-1 arc and cancels in every difference along it **.
This is the structural simplification the comparison needs: on the arc the only genuinely
transcendental pieces are the face-2 angle and the face-2 radius.

================================================================================
2. THE REDUCED ARC OBJECTIVE AND THE RIDGE POINT
================================================================================
Collecting the (delta,H)-chart objective along face 1 (K's delta-linear piece included, the
delta-independent constants dropped):
  G_arc(A) = [area](A) + a1 b1 + a2 phi2(A) + beta1 L1(A)^2 + gamma1 L1(A)
             + beta2 L2(A)^2 + gamma2 L2(A) + (z3 - z1)(b1 - A),
  [area](A) = r^2 [ (sin^2 b1 + sin^2 b2)(sin2b1 + sin2A)
                    + (sin b2 cos b2 - sin b1 cos b1)(cos2A - cos2b1) ],
  L1(A) = 2 r sin A ,    L2(A) = |hub(A) - c3| ,   c3 = (r sin2b2, -2 r sin^2 b2),
  phi2(A) = atan2( D2 sin B , H - D2 cos B ),   B = b1 + b2 - A ,  D2 = 2r sin b2 ,
and the RIDGE is the arc point A = b2 (delta = b1 - b2), where L1 = 2r sin b2, L2 = 2r sin b1.
Note the two simplifications that make this usable: the area is AFFINE in (sin2A, cos2A)
(same mechanism as the lead's ridge decomposition) and L1 is elementary, so the only coupled
terms are a2 phi2 and beta2 L2^2 + gamma2 L2.
Numerical frame check at r = .377, b1 = 1.008, b2 = 1.001 (arc constant dropped):
   G_arc(ridge) = -0.480558 ;  G_arc at delta = -.320 / -.315 / -.310 = -0.484664 / -0.484662 /
   -0.484671.  So the arc's certified interior local maximum sits BELOW the ridge value, by
   ~4.1e-3 — same sign and magnitude as the lead's -0.4988 vs -0.4947, with the difference
   robust to the arc-constant and to the width terms (both delta-independent).

================================================================================
3. THE COMPARISON AS AN INTEGRAL, AND WHAT MUST NOT BE ASSUMED
================================================================================
  G_arc(A) - G_arc(b2) = integral_{b2}^{A} G_arc'(s) ds.
The certified C868 arc carries an interior local maximum (G' > 0 at delta = -.32 and G' < 0 at
delta = -.31), and the ridge lies at delta = b1 - b2, far on the other side; so G' must change
sign at least twice between them.  Therefore:
  * G is NOT monotone and NOT concave along the arc — neither may be assumed;
  * the integral must be shown sign-definite by a structural argument, not by a derivative sign;
  * the natural splitting is: the AFFINE-in-(sin2A,cos2A) part (area) + the elementary (z3-z1) and
    L1-terms are handled by the same chord/tangent linearisation as RIDGE-RANK-ONE-COUPLING.md
    (there: h(T) = -sin2T with h'' = 4 sin 2T < 0 on the legal interval, so h lies below every
    tangent); the residual transcendental part is the pair
        a2 phi2(A) + beta2 L2(A)^2 + gamma2 L2(A),
    whose A-dependence is exactly the face-2 data along the face-1 circle.

================================================================================
4. CONCRETE NEXT OBLIGATION (reduced, not reduced-then-lost)
================================================================================
On the arc, put S(A) := a2 phi2(A) + beta2 L2(A)^2 + gamma2 L2(A) and let Phi(A) be the
elementary part; the target is the single scalar inequality
        Phi(A) + S(A) <= Phi(b2) + S(b2)      for all legal A on the arc,
or its weaker endpoint form against max(Phi + S) at the arc ends and the certified interior
critical point.  Two routes that stay inside the lead's existing machinery:
  (a) certify G_arc(A) <= G_ridge directly by the same second-order interval AD used in
      face_second_jet.py, now comparing against a CONSTANT (the ridge value) instead of studying
      the stationary structure — this needs no new derivative theory, only the already certified
      chart plus the ridge constant;
  (b) prove the inequality analytically by eliminating L2 and phi2 in favour of A: L2 and phi2
      are linked by the law of sines in the face-2 triangle (L2 / sin B = D2 / sin phi2) and B is
      affine in A, so S is a function of a single angle with explicit coefficients.

================================================================================
5. LIMITS
================================================================================
* Section 1 is exact (three symbolic residuals are 0); section 2's formula is the definition of
  the arc objective with the constants that cancel in differences explicitly dropped, and its
  numeric frame check reproduces the ORDER AND SIGN of the lead's comparison but not the absolute
  values (K's constant and the width terms are omitted, which is harmless for the difference).
* Nothing here proves the domination: it reduces the target to the scalar inequality of section 4
  and records the two obstructions (non-monotonicity, non-concavity) that any proof must respect.
* The C860 low-bearing counterexample (b < 1) stays outside this mechanism's scope, as the lead
  notes; nothing here contradicts C868.

STATUS: mechanism + exact structural identities + validated frame; no claim registered.
