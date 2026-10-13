# C862c-PINCHED-STATIONARITY.md — sign audit, exact reduction, corrected diagnostics

Owner: cline2-sharp-fan (own files, own drivers).  Exploratory + formula-level; NOT a certificate.
Drivers: tools/sign_audit.py, tools/corrected_diagnostics.py.  Outputs: out/p43_sign_audit.txt,
out/p43.log, out/p43_corrected.log.  Coefficients joint_nested_frozen.json.

================================================================================
1. SIGN AUDIT — THE TWO ANGLE TERMS HAVE OPPOSITE CHIRALITY (this was the trap)
================================================================================
Symbolic differentiation in the lead's coordinates (X1,Y1) = (v - D1cos b1, D1 sin b1 - t),
(X2,Y2) = (v - D2cos b2, D2 sin b2 + t) gives exactly
    grad theta1 = (-Y1, -X1)/L1^2 ,      grad theta2 = (-Y2, +X2)/L2^2 ,
    n1 = (X1, -Y1)/L1 ,                  n2 = (X2, Y2)/L2        (unit vectors to the hub),
and the mixed entries of the angle Hessians in their own radial/tangential frames are
    <n1, Hess(theta1) n1^perp> * L1^2 = -1 ,   <n2, Hess(theta2) n2^perp> * L2^2 = -1
[CORRECTED per lead: the mixed entry scales as 1/L^2, so multiplying by L^2 gives the
 constant -1; an earlier version printed "*L = +-1", which is dimensionally wrong.]
So the pad is NOT uniform: the a1-term and the a2-term enter with OPPOSITE orientation, i.e.
    M1 = -(2 w1 w1^T - I) ,   M2 = +(2 w2 w2^T - I) ,   w_j = n_j rotated by -pi/4,
    Hess F = 2(beta1+beta2) I - sum_j (c_j/L_j)(I - n_j n_j^T) + (a1/L1^2) M1 + (a2/L2^2) M2 .
Consequences: (i) the RADIAL entries n_j^T M_j n_j = 0 are sign-independent, so the pinched
necessary conditions below are unaffected; (ii) every MIXED-direction statement (determinant,
directional curvature) flips if the chirality is mishandled — my Round-23 diagnostic used the same
chirality for both terms, so it computed a neighbouring function.  Re-run with the corrected pad:
calibration against finite differences of the corrected objective over 30 legal points gives
worst |analytic - numeric| = 5.47e-4 (finite-difference error level), so the corrected formula is
the Hessian of the objective, not of a look-alike.

================================================================================
2. EXACT REDUCTION: an interior local maximum must satisfy four scalar conditions
================================================================================
F = affine + sum_j [a_j theta_j + beta_j L_j^2 + gamma_j L_j],  c_j = |gamma_j|,  a_j > 0,
alpha = ( r(1 - cos T cos D), - r cos T sin D ),  T = b1+b2,  D = b1-b2.
(R1) radial test w = n_j (uses only n_j^T M_j n_j = 0):
        c_j/L_j + a_j/L_j^2  >=  2(beta1+beta2)      =>   L_j <= L*_j ,
        L*_1 = 0.421097, L*_2 = 0.419177 (positive roots of 2 sum(beta) L^2 - c_j L - a_j = 0).
(R2) trace: tr Hess = 4(beta1+beta2) - sum_j c_j/L_j <= 0  =>  sum_j c_j/L_j >= 4 sum(beta).
(R3) 2D semidefiniteness: Hess <= 0  <=>  tr <= 0 AND det >= 0, i.e. the single scalar inequality
        (tr/2)^2  >=  ((H11 - H22)/2)^2 + H12^2 ,
     with H11, H22, H12 the entries of Hess F as given in section 1 — the only place the
     chirality signs enter.
(R4) stationarity [CORRECTED per lead: the quadratic terms must be included]:
        alpha + sum_j 2 beta_j L_j n_j  =  sum_j c_j n_j - sum_j a_j grad theta_j ,
     where alpha = (r(1-cos T cos D), -r cos T sin D) is the gradient of the AFFINE part
     ONLY.  My earlier R4 string omitted the sum_j 2 beta_j L_j n_j term (order 2*0.70*0.4
     ~ 0.6 per component), inconsistent with the Hessian 2(beta1+beta2) I had written.
     After the fix: analytic gradient vs finite differences of the verified Cartesian
     objective agrees to 1.2e-10 (tools/interface_check.py, part B).
So an interior local maximum must satisfy (R1)+(R2)+(R3)+(R4).  (R1)+(R2) alone are SATISFIABLE —
the width-legal ND witness below has L1,L2 ~ 0.35 and sum c/L ~ 6.7 — so the exclusion of interior
maxima cannot come from the pinch and the trace; it must use (R4), optionally together with (R3).
Equivalently, a witness of "no interior maximum" is an explicit linear combination of grad F that
never vanishes on the pinched region; the natural candidates are <grad F, n_j> = <alpha,n_j> - c_j
- c_j' (n_j.n_j') + (angle terms), which vanish at the stationary points found, so a combination
adapted to the two-sided balance (for instance alpha - sum c_j n_j, tested against the achievable
n_j-geometry) is the object to bound.

================================================================================
3. CORRECTED DIAGNOSTICS (2 seeds x 80 iterations each; exploratory)
================================================================================
(a) ND points still exist with the corrected objective and remain width-legal:
    min lambda_max = -0.572099 (lambda_min = -0.572381) at r = 0.375, b1 = b2 = 0.61254 ~ bmin(r),
    delta = -0.00220, H = 0.58464, H strictly interior to its fiber, sum c/L = 6.728, trace = -1.145.
    So the positive-eigenvalue conjecture is dead under the corrected objective too.
(b) Interior stationary points exist (|grad| ~ 1e-9, width-legal, H interior) and are SADDLES:
    seed 86270: eigen (-0.7416, +1.7718);  seed 86271: eigen (-0.0022, +1.4276).
    No interior local maximum was found.  [CORRECTED per lead: the second case has
    (lambda_min, lambda_max) = (-0.0022, +1.4276), which is INDEFINITE because lambda_max > 0,
    NOT semidefinite, and it is a saddle.  I withdraw the phrase "semidefinite".  The only
    correct remark is that lambda_min happens to sit near zero, so an exclusion argument may
    not assume lambda_min is bounded away from 0.]

================================================================================
4. LIMITS
================================================================================
 * Everything numeric here is exploration (4 x (2 seeds x 80) DE runs and 30-point calibration);
   the formula-level content is section 1 (exact) and section 2 (exact necessary conditions).
 * Round 23's quantitative conclusions are unchanged in direction under the corrected pad, but its
   eigenvalues were those of a slightly different function; the re-run above supersedes them.
 * The pinch + trace are not enough to exclude interior maxima; the reduction in section 2 shows
   precisely what is missing, and the near-zero eigenvalue in (b) shows why (R3) must be stated
   with <= and >= (semidefinite), not with strict inequalities.

STATUS: formula-level reduction + corrected diagnostics; no claim registered.


================================================================================
5. INTERFACE CHECK (added after the lead's objection)
================================================================================
The lead correctly demanded that the Cartesian form be checked against the code objective rather
than against my own construction.  tools/interface_check.py compares, at 300 random legal-ish
points, my Cartesian hub factor with the (delta,H)-chart hub part used by the code chain:
   worst |F_cartesian - F_chart|                  = 5.355e-04
   worst |F_cartesian - F_chart - (z3-z1) delta|  = 3.666e-16
with z3-z1 = 0.000464943.  The first number is exactly the delta-linear piece of K that the
cancellation identity absorbs into a1 theta1 + a2 theta2 and which my comparison string omitted;
once it is restored the two forms agree to MACHINE ZERO, so the Cartesian form IS the objective and
the interface is sound.  Part B of the same script confirms the corrected gradient.
