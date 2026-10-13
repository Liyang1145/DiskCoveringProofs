# H-FIBER-AUDIT — audit of lead/DEGENERATE-SECTOR-HUB-PATCH.md

Owner: cline2-sharp-fan (own files only). Instrument: `tools/audit_h_fiber.py`
(repro: `py -3 -B -X utf8 tools/audit_h_fiber.py`; output `out/p24_audit_h_fiber.txt`).
All checks below are **symbolic (sympy) in r, b1, b2, A, H**; the trailing dps=50 block
only re-evaluates the same closed forms at fixed points (identity confirmation, not
search, not a verdict source).

Caliber: unit circle; equal disks radius r ≤ 19/50; angles radians; lengths in units of
the unit-circle radius. Chart of the patch (lead's own reduction, corner lemma):
s = √(1−r²), P1 = (s,−r), P2 = (s,r), c2 = (s,0); switches P1,P2 are at distance exactly
r from c1,c2 and c2,c3 respectively; sector 2 is flat: α2 = π, u2 = v2 = 1, w2 = 2 asin r,
L2 = T2 = 0. Face1 = [9,1,2], Face2 = [9,2,3]; A, B the angles at c2 in Face1, Face2;
H = |c9 − c2|, δ = b1 − A, D1 = 2r sin b1, D2 = 2r sin b2.

================================================================================
VERDICT SUMMARY
================================================================================
V1 CONFIRMED (exact)  the two centre-difference vectors and |c1−c2| = D1, |c3−c2| = D2
V2 CONFIRMED (exact)  A + B = b1 + b2, and B = b1 + b2 − A
V3 CONFIRMED (exact)  hub coordinate c9 = (s − H cos δ, −H sin δ); |c9−c2| = H
V4 CONFIRMED (exact)  ρ1² = (H² + D1² − 2 H D1 cos A)/(4 sin²A)
V5 CONFIRMED (exact)  ρ1 ≤ r ⟺ 2r sin(b1−A) ≤ H ≤ 2r sin(b1+A)
V6 CONFIRMED (exact)  combined lower bound H ≥ 2r|sin δ|
V7 CONFIRMED (exact)  combined upper bound H ≤ 2r·min(sin(b1+A), sin(b2+B)), both sines
                      must be > 0 (else the patch is impossible) — as the note says
V8 CONFIRMED (exact)  |c9| ≤ 1−r ⟺ H² − 2 s cos δ H + 2 r (1−r) ≤ 0
V9 RESTATEMENT (not an addition): δ ∈ (−b2, b1) is the explicit form of the note's
                      inline A,B > 0.  (Withdrawn as an "addition" after lead review.)
V10 WITHDRAWN as an addition.  cos δ > 0 is NOT a separate necessary condition: it is
                      forced by V9, because b1,b2 ∈ (0,π/2) gives
                      δ ∈ (−b2,b1) ⊂ (−π/2,π/2) ⟹ cos δ > 0 automatically.
                      (The root-positivity computation below stays as a consistency
                      check, not as an extra domain restriction.)
V11 CONFIRMED (exact) the pointwise closure makes the site-2 angle coefficient exactly
                      −π and the two switch-angle coefficients exactly π: constants, so
                      the global constant must not be adjusted
V12 SCOPE NOTE        ρ_j ≤ r is necessary only because the face's Voronoi vertex lies
                      inside D; the patch domain is a necessary domain for
                      configurations in which both faces are genuine refined-dual faces
V13 NORMALIZATION (must be kept explicit): the degenerate sector-2 data are
                      u2 = v2 = t = r/R0 in the dual normalization (distances ÷ R0,
                      R0 = 19/50), and w2 = 2 asin(R0 t) = 2 asin r; they equal 1 only
                      in r-units (distances ÷ r).  See section 6.

================================================================================
1. V1, V2, V3 — the chart (exact)
================================================================================
With u1 = (−cos b1, −sin b1), u2 = (−cos b2, +sin b2):
  c1 − c2 = D1 u1,  c3 − c2 = D2 u2,  |u1| = |u2| = 1                    [V1]
  u1·u2 = cos b1 cos b2 − sin b1 sin b2 = cos(b1+b2)                     [checked = 0]
  ⇒ the angle at c2 from the ray c2→c1 (direction π+b1) to c2→c3 (direction π−b2),
    measured through the inward direction π, is b1+b2. Since the two faces share the
    edge (9,2), the ray c2→c9 lies strictly inside that wedge, hence A,B > 0 and
    A + B = b1 + b2, B = b1 + b2 − A                                       [V2]
  With D1 = 2r sin b1: |c1−c2|² − D1² = 0 (and likewise D2).
Hub coordinate: put the direction c2→c9 at angle π + δ (δ = b1 − A). Then
  c9 = c2 + H(cos(π+δ), sin(π+δ)) = (s − H cos δ, −H sin δ)              [V3]
  |c9−c2|² − H² = 0; u1·û9 = cos A (since b1 − δ = A); û9·u2 = cos B        [all = 0]

DOMAIN OF δ (restatement of the note's inline A,B > 0):  A > 0 ⟺ δ < b1;  B > 0 ⟺ δ > −b2.
  ⇒  δ ∈ (−b2, b1)                                                        [V9]
  Check: b2 − B = b2 − (b1+b2−A) = A − b1 = −δ  (the note's identity) ⟹ = 0 exactly.
  CONSEQUENCE (recorded, not an extra condition): since b1,b2 ∈ (0,π/2),
     δ ∈ (−b2,b1) ⊂ (−π/2,π/2)  ⟹  cos δ > 0 automatically.  No separate hypothesis
     on δ is needed anywhere below.

================================================================================
2. V4, V5 — face-1 circumradius and its H-interval (the central claim)
================================================================================
  |c1−c9|² = H² + D1² − 2 H D1 cos A       [symbolic difference = 0, V4]
  ρ1 = |c1−c9| / (2 sin A)                 (side opposite the angle A at c2)
  ρ1² = (H² + D1² − 2 H D1 cos A)/(4 sin²A)
  ρ1 ≤ r ⟺ H² − 4 r sin b1 cos A · H + 4r²(sin²b1 − sin²A) ≤ 0
  roots  H = D1 cos A ± sin A √(4r² − D1²) = 2r[sin b1 cos A ± cos b1 sin A]
            = 2r sin(b1 ± A)                [using D1 = 2r sin b1, b1 ∈ (0,π/2)]  [V5]
  the quadratic opens upward (leading coeff. 1/(4sin²A) > 0) ⇒ the feasible set is the
  closed interval between the roots.  The roots are correctly ORDERED with no extra
  hypothesis:  2r sin(b1+A) − 2r sin(b1−A) = 4 r cos b1 sin A > 0.            [checked]
  Face2 identically with (A,b1) → (B,b2); and b2 − B = −δ, so its lower root is
  2r sin(−δ) = −2r sin δ.                                                    [checked]

  ⇒ COMBINED (V6, V7):
      lower   H ≥ max(2r sin δ, −2r sin δ) = 2 r |sin δ|                     [V6]
      upper   H ≤ 2r · min( sin(b1+A), sin(b2+B) )                           [V7]
  Emptiness: if sin(b1+A) ≤ 0 or sin(b2+B) ≤ 0 the interval is empty (the note's
  caveat is exactly right; equivalent condition: b1+A ≥ π or b2+B ≥ π).

  Exact H-fiber (V6 ∩ V7 ∩ V8), the object requested:
    r, b1, b2, A  fixed, δ = b1 − A,  s = √(1−r²),  D = s²cos²δ − 2r(1−r)
    H ∈ [ max( 2r|sin δ| , s cos δ − √D ) ,
          min( 2r sin(b1+A) , 2r sin(b2+B) , s cos δ + √D ) ]
    preconditions: b1,b2 ∈ (0,π/2); δ ∈ (−b2,b1) [which already gives cos δ > 0]; D ≥ 0;
                   sin(b1+A) > 0; sin(b2+B) > 0; nonempty ⟺ lower ≤ upper.

================================================================================
3. V8, V10 — hub interiority quadratic (V10 withdrawn)
================================================================================
  |c9|² = H² − 2 s H cos δ + 1 − r²   [symbolic]
  |c9| ≤ 1−r ⟺ |c9|² − (1−r)² ≤ 0 ⟺ H² − 2 s cos δ H + 2 r (1−r) ≤ 0        [V8]
  discriminant/4 = D = s²cos²δ − 2r(1−r)  ✓ (the note's D)
  roots  H = s cos δ ∓ √D  (both written with ± in the note) ✓
  CONSISTENCY CHECK ONLY (withdrawn as a domain condition, V10): the two roots have
  product 2r(1−r) > 0 (same sign) and sum 2 s cos δ > 0, so both roots are positive.
  The sum is positive automatically because V9 gives cos δ > 0.  Hence nothing new is
  imposed: D ≥ 0 is the only emptiness test coming from hub interiority, exactly as the
  note states.  (Also, when D ≥ 0, s cos δ − √D > 0 since D < s²cos²δ, so the lower hub
  root never needs a separate positivity check.)

================================================================================
4. V11 — what "pointwise closure" actually cancels (bookkeeping confirmed)
================================================================================
Closure equations in this chart (L2 = T2 = 0, w2 = 2 asin r; see section 6 for units):
   P1:  T1 + L2 + 2b1 + (w1+w2)/2 = π  ⟹ 2b1 = π − T1 − (w1+w2)/2
   P2:  T2 + L3 + 2b2 + (w2+w3)/2 = π  ⟹ 2b2 = π − L3 − (w2+w3)/2
The asymmetric roles are correct: T1 is the base angle at P1, which is sector 1's RIGHT
endpoint (endpoint distance v1 = r); L3 is the base angle at P2, which is sector 3's LEFT
endpoint (u3 = r).  Both closures are identities of the chart (b_j is the geometric half
angle at P_j between the two adjacent centres), so they cost no degree of freedom.

Multiplier coefficients in the sum of the seven original atoms:
  site-2 angle slot:  −α2 − A − B + b1 + b2 = −π − (A+B) + (b1+b2) = −π   [constant]
  switch-angle slot 1: (T1 + w1/2) + (L2 + w2/2) + 2b1 = π               [constant]
  switch-angle slot 2: (T2 + w2/2) + (L3 + w3/2) + 2b2 = π               [constant]
⇒ the pointwise closure turns exactly these three coefficients into constants, so the
cluster's improvement is booked only in the coupled variables, and the global constant
must be left unchanged (no double subtraction).  All three equalities verified
symbolically.

================================================================================
5. V12 — scope / what is still missing
================================================================================
S1. ρ_j ≤ r enters only through "the face's Voronoi vertex is in D and must be covered".
    For a genuine refined-dual face this holds; the domain is therefore necessary for
    configurations in which both faces are actual faces.  Realization of the rest of the
    graph, the nearest-site inequalities beyond the patch, and the second hub are still
    omitted — a maximum over this H-fiber is a SAFE upper bound only after that domain
    coverage is verified (the note says this; it stays true).
S2. The chart itself assumes the switch radii equal r exactly (P1,P2 at distance r from
    the adjacent centres) and the flat middle sector α2 = π.  Neither is a WLOG statement
    about the whole class; the H-fiber above is conditional on the chart.
S3. Not checked here (outside the patch): |T1 − c3| ≥ ρ1, |T2 − c1| ≥ ρ2 (the tips must
    not be nearer to the neighbouring ring), and the corresponding conditions involving
    the second hub.  These are additional patch-level Voronoi necessities; if they bite,
    they shrink the H-fiber further.
S4. The note's "H in [2r sin(b1-A), 2r sin(b1+A)]" needs sin(b1+A) > 0 for the interval
    to be nonempty at H > 0; the note flags this — confirmed and made explicit above.

================================================================================
6. V13 — UNITS MUST BE SEPARATED EXPLICITLY (correction from lead review)
================================================================================
The chart of the note is stated in unit-circle geometry with disk radius = allowance r
(so |P1−c2| = |P1−c1| = r and c1−c2 = 2r sin b1(...)).  The dual atoms, however, are
normalized by R0 = 19/50, not by r.  Two consistent readings, never to be mixed:

 (a) r-units (distances ÷ r):   u2 = v2 = 1,  |c1−c2|/r = 2 sin b1,
     chord(P1,P2)/r = 2.
 (b) dual normalization (distances ÷ R0 = 19/50), which is what the atoms use:
     u2 = v2 = t = r/R0,   w2 = 2 asin(R0 t) = 2 asin r,
     and the code's forms w = 2 asin(R0 √Q/2), value = R0² u v sin α/2 + (w − sin w)/2,
     switch value = R0² t² sin(2b)/2 all stay valid with R0 in place of r.
In particular u2 = v2 = 1 ONLY in r-units; in the atom normalization they are t = r/R0,
which equals 1 only at the maximal allowance r = R0 = 19/50.  The sector-2 area atom is
R0² t² sin(α2)/2 + (w2 − sin w2)/2 = (w2 − sin w2)/2 = a − sin(2a)/2 with a = asin r,
independent of the reading (the triangle term vanishes because α2 = π).
All H-fiber inequalities in section 2 are geometric (unit-circle/r-units) and are
unaffected; only the atom arguments (u2,v2,t) must be converted by the factor r/R0 when
the seven atoms are summed.
