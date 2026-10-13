# H-FIBER-H-DEPENDENCE.md — exact H-dependence of the patch face atoms (Round 12)

Owner: cline2-sharp-fan (own files only; no claim registration).
Instruments: `tools/h_dependence.py` (symbolic structure), `tools/h_curvature_check.py`
(coefficient extraction), `tools/h_endpoint_max.py` (verified numerics, corrected signs),
`tools/telescoping_check.py`, `tools/fullsum_h.py`.
Outputs: `out/p25_h_dependence.txt`, `out/p26_h_curvature.txt`, `out/p27_h_endpoint_max.txt`,
`out/p28_telescoping.txt`, `out/p29_fullsum_h.txt`.
Inputs read (not modified): `lead/DEGENERATE-SECTOR-HUB-PATCH.md`,
`lead/exchange_middle_inward_dual.py`, `lead/joint_patch_frozen_v2.json`.

Caliber: unit circle; equal disks of radius r (the ACTUAL allowance, 3/8 ≤ r ≤ R0 = 19/50;
the numeric evaluations below are on the slice r = R0 = 0.38); chart s = √(1−r²), P1 = (s,−r),
P2 = (s,r), c2 = (s,0); faces [9,1,2], [9,2,3]; b1,b2 switch half-angles; A,B the angles at
c2 in faces 1,2 with A+B = b1+b2; H = |c9−c2|, δ = b1−A, D1 = 2r sin b1, D2 = 2r sin b2;
θ1 = A, θ2 = B. All statements below are verified either symbolically or by term-by-term
agreement with a verbatim mirror of the lead's atom code.

================================================================================
1. STRUCTURAL FACTS (exact, independent of z)
================================================================================
S1 [shared edge cancels]  In face j the angle opposite the shared edge (9,2) is ψ1 (face 1)
    resp. ψ2 (face 2), and 2ρ_j sin ψ_j = |(9,2)| = H, so t_j sin ψ_j = H/(2R0) for both.
    With the two faces receiving opposite edge signs (s2 = −s1) the shared-edge slots
    cancel IDENTICALLY:
       z11[e92] coefficient: s1(H/2R0)² + s2(H/2R0)² = 0
       z73[e92] coefficient: s1(H/2R0)  + s2(H/2R0)   = 0
    Verified against the code: direct terms −1.051765928 + 1.051765928 = 0 and
    −1.776315789 + 1.776315789 = 0 at the test point.

S2 [telescoping theorem — recorded as VERIFICATION ONLY]  For EVERY internal edge e (two incident faces f,g) the
    z11[e] and z73[e] slots cancel identically, in every configuration and for every z:
    in face f the angle opposite e subtends e, hence t_f sin θ_f^opp = |e|/(2R0) = t_g sin θ_g^opp,
    and the signs are opposite.  Consequently
       **in the full 11-face atom sum the z11/z73 slots survive only on the 9 leaf edges**
    (the ring-ring edges of the q0 graph).  In the q0(6,7) graph those are exactly
    (0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,0) — all of them join RING centres, so
    **their lengths are H-independent** and so is the whole z11/z73 part of the sum.
    Numeric confirmation (p28): the full-sum z11/z73 contribution is −12.081921165806 at
    H = 0.30, 0.40, 0.50, 0.60 with spread 3.6e-14.
    CONSEQUENCE: the H-dependence of the FULL sum is carried by
       (i) the six hub-9 face values (piecewise affine in H: each face's value is its area
           = (1/2)|(c_i−c9)×(c_{i+1}−c9)|, affine in c9; kinks only when a signed area
           changes sign), and
       (ii) the angle slots (site-angle z[i], edge-angle z[50+ee]) of those six faces,
            i.e. atan2/arctan expressions.
    There are NO sqrt-of-quadratic and NO H² terms in the full sum.  (p29 shows the
    values' second differences vanish away from the kinks, and the z11/z73 part constant.)

================================================================================
2. THE TWO-FACE OBJECT ASKED FOR (exact, verified to 1e-15)
================================================================================
  F(H) = C0 + λ0 H + α1 φ1 + α2 φ2 + β1 L1² + γ1 L1 + β2 L2² + γ2 L2
    φ_j = atan2(D_j sin θ_j, H − D_j cos θ_j),  L_j = |H − D_j cos θ_j|/|sin φ_j| = √(H²+D_j²−2HD_j cos θ_j)
    λ0 = r ( sin b1 sin A + sin b2 sin B ) > 0   (this is the face values: v1+v2 = λ0 H)
         *** CAVEAT (lead correction, 2026-09-25): λ0 carries the ACTUAL allowance r, ***
         *** not R0.  Each face value is its area (1/2)·D_j·H·sin θ_j with D_j = 2r sin b_j, ***
         *** so v1+v2 = r H (sin b1 sin A + sin b2 sin B).  My earlier "λ0 = R0(...)" is ***
         *** valid only on the maximal-allowance slice r = R0; every number in section 3 ***
         *** was evaluated at r = R0 = 0.38 and must be read as that slice.  The chart, ***
         *** the fiber inequalities and D_j = 2r sin b_j already use the actual r. ***
    α1 = (z1 + zang[e92]) − (z9 + zang[e12])
    α2 = (z3 + zang[e92]) − (z9 + zang[e23])
    β1 = sgn(f1,e91)·z[11+e91]/(4R0²)        γ1 = sgn(f1,e91)·z[73+e91]/(2R0)
    β2 = sgn(f2,e93)·z[11+e93]/(4R0²)        γ2 = sgn(f2,e93)·z[73+e93]/(2R0)
    C0 = −(z1+zang[e92])(π−A) − (z3+zang[e92])(π−B) − (A+B) z2 − A zang[e91] − B zang[e93]
         + sgn(f1,e12)[sin²b1 z[11+e12] + sin b1 z[73+e12]]
         + sgn(f2,e23)[sin²b2 z[11+e23] + sin b2 z[73+e23]]
  DERIVATIVES
    F'  = λ0 − α1 D1 sinA/L1² − α2 D2 sinB/L2²
          + 2β1(H−D1cosA) + 2β2(H−D2cosB) + γ1(H−D1cosA)/L1 + γ2(H−D2cosB)/L2
    F'' = 2(β1+β2) + Σ_j [ 2α_j D_j sinθ_j (H−D_j cosθ_j)/L_j⁴ + γ_j D_j² sin²θ_j/L_j³ ]
  EXACT TRIGONOMETRIC FORM (used below): with cos φ_j = (H−D_jcosθ_j)/L_j,
    sin φ_j = D_j sinθ_j/L_j,  L_j = D_j sinθ_j / sin φ_j,
      F''(H) = 2(β1+β2) + Σ_j sin³φ_j/(D_j sinθ_j) · [ 2α_j cosφ_j/(D_j sinθ_j) + γ_j ].
  VERIFICATION: p27 STEP 1 — closed form = direct code mirror to 1e-15 at five points;
  p27 STEP 2 — F' matches direct finite differences to 6e-9, F'' matches dF'/dH to 1e-10.

================================================================================
3. FROZEN COEFFICIENTS (lead/joint_patch_frozen_v2.json) AND THE CURVATURE VERDICT
================================================================================
  λ0 = r (sin b1 sin A + sin b2 sin B)  — evaluated at r = R0 = 0.38 in this section,
       giving +0.527408910 ; for a general allowance r multiply by r/R0.
  α1 = +0.011949606   α2 = +0.012762705
  β1 = +0.703356672   β2 = +0.728753523      [ = 0.406258814/(4R0²), 0.420928035/(4R0²) ]
  γ1 = −1.151106437   γ2 = −1.188609458      [ = −0.874840892/(2R0), −0.903343188/(2R0) ]
  z9, z1, z3 = −0.051393395, −0.039443789, −0.038630690  (lead's quotes confirmed)
  edge-angle slots z[50+ee] = 0 for all five patch edges, so the α's reduce to z1−z9, z3−z9.
  SIGN-FREE CONVEXITY BOUND: |F''−2(β1+β2)| ≤ M := Σ_j[2|α_j|/(D_j sinθ_j)² + |γ_j|/(D_j sinθ_j)],
  and M ≥ (|γ1|+|γ2|)/(2R0) = 3.078574 > 2(β1+β2) = 2.864220 ALWAYS.  Hence
     **no uniform convexity (or concavity) bound can hold for these coefficients.**
  SHARP TEST (exact 1-D): minimizing the exact F'' over the fiber [H_lo,H_hi] gives, with
  the frozen numbers (p27 STEP 3):
     (b1,b2,A)      fiber            F''min      F''max      argmax of F
     (1.00,1.00,0.80) [0.3144,0.6145]  −1.392718  −0.341953   endpoint (F concave, F'>0)
     (0.90,1.10,0.70) [0.3144,0.5134]  −1.607949  −1.283451   endpoint (F concave, F'>0)
     (0.80,0.80,0.80) [0.3050,0.7597]  −3.121148  +0.738893   H=0.49584 INTERIOR, gap +4.25e-02
     (0.60,0.60,0.60) [0.3050,0.7083]  −6.804098  +1.251003   H=0.37507 INTERIOR, gap +1.65e-02
     (0.50,0.50,0.40) [0.3073,0.5953] −10.877547  +1.093493   H=0.32464 INTERIOR, gap +1.63e-03
     (1.10,0.70,0.90) [0.3144,0.6911]  −2.294053  +0.316667   H=0.61291 INTERIOR, gap +3.27e-04
  In the four interior cases F'(H_lo) > 0 > F'(H_hi), i.e. an interior critical point exists.
  STATUS OF THIS FINDING (lead instruction: do not promote to proof): the four rows are
  NUMERIC instances, evaluated at r = R0 = 0.38 in double precision without an interval
  witness.  They are therefore evidence that "endpoint max" is not a theorem, NOT a proof
  that it fails, and they say nothing about the actual certificate's fiber position.
  A rigorous version would require an interval-witnessed (b1,b2,A) with a certified sign
  change of F' and a certified positive gap over both endpoints.  What IS exact and usable
  is the derivative form: F', F'' and the trigonometric form of F'' above.
  Note the direction of the failure (numeric): it is the two sqrt terms (γ_j L_j with γ_j < 0)
  that create the negative curvature; by S2 those terms are not part of the full-sum H-fibre.

================================================================================
4. WHAT THIS MEANS FOR THE 7-FACTOR UPPER — as decided by the lead
================================================================================
LEAD DECISION (2026-09-25): the certificate patch keeps the TWO site faces only, so the
external sqrt terms STAY, and the relevant object is section 2/3 above.  The full-sum
telescoping S2 is already known to the lead (matching) and is IRRELEVANT to the patch
certificate; it is recorded only as a verification that the two-face bookkeeping is
consistent.  R2/R3 below are therefore background, not part of the certificate path.
R1 For the two-face object the correct reduction is NOT "endpoint max" but the explicit
   1-D problem: evaluate F at H_lo and H_hi and at the zeros of the displayed F'
   (a scalar equation with the atan2 derivatives −D_j sinθ_j/L_j²).  Endpoint-max may be
   asserted only after testing 2(β1+β2) ≥ M (never true here) or after solving F'=0.
   Sqrt terms stay in F, F', F''.
R2 [background only] In the full 11-face sum the sqrt/H² terms cancel by S2; that sum is
   not the certificate's object.
R3 [background only] If the lead's gauge accounting (mu2 / cl113 / cl114 → 9π) uses S2,
   the neighbouring hub-9 faces are already accounted there.

STATUS: derivation + verified numerics; no claim registered; no mainTarget change.
The one open item for the lead: decide whether the certificate's H-fibre is the two-face
object (then use R1) or the full sum (then R2 + S2 apply and the sqrt terms drop out).
