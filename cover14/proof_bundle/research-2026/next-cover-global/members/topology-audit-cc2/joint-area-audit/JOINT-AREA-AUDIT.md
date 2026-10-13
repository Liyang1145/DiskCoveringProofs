# Audit — joint boundary area/perimeter support: FINAL CORRECTED VERSION
# Scope members/topology-audit-cc2/joint-area-audit/. Analytic only; derivative variable explicit.

**Derivative variable convention used here and in the lead's notes:**
`α ∈ [0,π]` is the view angle at the site, `t = α/2 ∈ [0,π/2]`, `b(α) = 2·asin(r sin(α/2))`,
`z = r sin t`, `w = √(1 − z²)`. All primed quantities below are d/dα.
Every derivative in the LEAD notes is with respect to α. My earlier objections differentiated
with respect to t = α/2 (which introduces a factor 4 on second derivatives, since d²/dα² =
¼ d²/dt²) and moreover evaluated at t-values such as t = 2.458, i.e. α = 4.916, OUTSIDE the
legal domain α ∈ [0,π]. All of those objections are withdrawn.

## Retractions (final, mine)

R1. My `b''` "correction" is withdrawn and was itself wrong. Correctly, with respect to α:
      b'(α) = r cos t / w ,      b''(α) = −r(1−r²)·sin t / (2w³) ,
    strictly negative for every 0 < t < π/2 (0 < α < π) and every 0 < r < 1. This is exactly the
    lead's formula. My earlier numbers were d²/dt² values (a factor 4 too large in magnitude) and
    my quoted "closed form" mixed the two variables. Verified by adaptive differentiation with
    respect to α (mpmath, dps 40): (r,α) = (U,1.0) gives −0.0735420272972, matching the lead's
    formula to all displayed digits; (0.3,2.0) −0.126784970692; (0.9,1.6) −0.137722043719.
R2. My concavity objection is withdrawn. In the legal domain the exact chain is
      F''(α) = −r² sin t cos t + r³ sin t cos²t / w + (z² + μ)·b''(α) ,
    the first two terms sum ≤ 0 whenever r cos t ≤ w (true for r² ≤ 1), and the third term is ≤ 0
    because b''(α) < 0. Hence F''(α) ≤ 0 on the WHOLE legal domain α ∈ [0,π], for every r ≤ 1 and
    every μ ≥ 0, strictly negative on (0,π). No restriction on t, no concavity threshold, and no
    feasible-angle maximum premise is needed or used. Verified: closed-form F''(α) against
    adaptive numeric d²F/dα² at 41 points for r = U (agreement to 40 digits) and negative on
    (0,π) for r = U, 0.5, 0.9, 0.99.
R3. Deleted as artifacts of the wrong variable / out-of-domain evaluation: the "α* = 3.4656"
    threshold, the "t* = 1.7328" sign change, and the "α_max = 3.14" norm-max premise. No such
    premise is used in the corrected audit.
R4. The previously withdrawn items stay withdrawn: my transfer wording (correct transfer is the
    ε→0 compact limit, then the bound at ρ = U), the alleged a≠b equality problem (the lead's
    general identity uses ab sinα/2), and the alleged double counting (the identity is inherited
    from AREA-SAFE-RELAXATION.md).

## What the audit confirms as correct (unchanged)

A1. Separate convexity of F(a,b): θ(d) = 2asin(d/2) is convex and nondecreasing; φ/2+μθ =
    θ(1/2+μ) − sinθ/2 has second derivative sinθ/2 ≥ 0; composition of convex nondecreasing with
    convex is convex; d is the norm of an affine map of (a,b); ab sinα/2 is separately affine.
A2. Corner reduction exact and tight:
      F ≤ max( r²sinα/2 + g(b_r)/2 + μb_r ,  g(A_r)/2 + μA_r ),
    b_r = 2asin(r sin(α/2)), A_r = 2asin(r/2); the (r,0) corner keeps zero triangle area and is
    retained.
A3. Concavity of F(α) and global tangent majorisation: correct as written by the lead (R2).
A4. Transfer by the ε→0 compact limit, then the bound at ρ = U.
A5. Degenerate arcs α = 0, a = 0, b = 0, d = 0 are continuous limits; r sin(α/2) ≤ r < 1, so no
    denominator degenerates.

## Status

The analytic chain of BOUNDARY-AREA-PERIMETER-JOINT.md and JOINT-EXACT-CAP-CONCAVITY.md is
complete and correct as written, with the derivative variable fixed to α. No correction to the
lead's concavity argument is required. No new claim registered; no further numerics needed.
