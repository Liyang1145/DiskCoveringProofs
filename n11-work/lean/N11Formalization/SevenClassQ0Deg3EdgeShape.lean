import N11Formalization.SevenClassQ0Deg3EdgeSuffixNonpos
import N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh

/-! Lane A: shape assembly for the zero-peak and negative-coefficient edges.

Edges 12 and 13 have zero peaks, already handled by
`SevenClassQ0Deg3EdgeSuffixHigh`.  Edges 9 and 10 have witness 1489, while the
proved narrow cosine tail starts at the next grid point 1490.  The helper here
keeps that one exact grid step explicit and then applies the analytic tail. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3EdgeShape

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Cos
open SevenClassQ0Deg3EdgeReal
open SevenClassQ0Deg3EdgeSuffixNonpos
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables

/-- On the remaining arc between `π/2` and `2`, the sine Taylor bracket stays
nonnegative.  The true sine is at least `1/2` there, while the degree-29
remainder is below `1/4`. -/
theorem sinT14_nonneg_of_half_pi_le_of_le_two {x : ℝ}
    (hx0 : Real.pi / 2 ≤ x) (hx : x ≤ 2) : 0 ≤ sinT 14 x := by
  have hxnonneg : 0 ≤ x := (by positivity : (0 : ℝ) ≤ Real.pi / 2).trans hx0
  have hsin : (1 / 2 : ℝ) ≤ Real.sin x := by
    have hx5 : x ≤ 5 * Real.pi / 6 := by
      nlinarith [Real.pi_gt_three]
    have hlow : Real.pi / 6 ≤ Real.pi - x := by linarith
    have hhigh : Real.pi - x ≤ Real.pi / 2 := by linarith
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ Real.pi / 6 by positivity) hhigh hlow
    rw [Real.sin_pi_sub, Real.sin_pi_div_six] at h
    norm_num at h ⊢
    exact h
  have hb := sin_bound_abs 14 x
  have hlower : Real.sin x - x ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤
      sinT 14 x := by
    have h := (abs_le.mp hb).2
    rw [abs_of_nonneg hxnonneg] at h
    linarith
  have hx2 : x ≤ 2 := hx
  have hpow : x ^ 29 ≤ 2 ^ 29 := pow_le_pow_left₀ hxnonneg hx2 29
  have herr : x ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤ (1 / 4 : ℝ) :=
    (div_le_div_of_nonneg_right hpow (by positivity)).trans (by
      norm_num [Nat.factorial])
  linarith

/-- The degree-28 Taylor polynomial of cosine is antitone on the quarter
circle.  Its derivative is the degree-27 sine polynomial, which is at least
the nonnegative degree-29 bracket `sinT 14`. -/
theorem cosT14_antitoneOn : AntitoneOn (cosT 14) (Set.Icc 0 (Real.pi / 2)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact fun x _ =>
      (hasDerivAt_cosT_succ 13 x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_cosT_succ 13 x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosT_succ 13 x).deriv]
    apply neg_nonpos.mpr
    have h14 := sinT14_nonneg (le_of_lt hx.1) (le_of_lt hx.2)
    have hterm : 0 ≤ x ^ 27 / ((Nat.factorial 27 : ℕ) : ℝ) := by positivity
    rw [sinT_succ] at h14
    norm_num at h14 ⊢
    linarith

/-- The same degree-28 Taylor cosine polynomial is antitone through `3π/4`.
The derivative sign is supplied by the three proved branches for the
degree-27 sine bracket. -/
theorem cosT14_antitoneOn_three_pi_div_four :
    AntitoneOn (cosT 14) (Set.Icc 0 (3 * Real.pi / 4)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact fun x _ =>
      (hasDerivAt_cosT_succ 13 x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_cosT_succ 13 x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosT_succ 13 x).deriv]
    apply neg_nonpos.mpr
    have h14 : 0 ≤ sinT 14 x := by
      by_cases hhalf : x ≤ Real.pi / 2
      · exact sinT14_nonneg (le_of_lt hx.1) hhalf
      · have hhalf' : Real.pi / 2 ≤ x := le_of_lt (lt_of_not_ge hhalf)
        by_cases htwo : x ≤ 2
        · exact sinT14_nonneg_of_half_pi_le_of_le_two hhalf' htwo
        · exact sinT14_nonneg_of_two_le_of_le_three_pi_div_four
            (le_of_lt (lt_of_not_ge htwo)) (le_of_lt hx.2)
    have hterm : 0 ≤ x ^ 27 / ((Nat.factorial 27 : ℕ) : ℝ) := by positivity
    rw [sinT_succ] at h14
    norm_num at h14 ⊢
    linarith

/-- Edge 14's exact positive coefficient threshold lies below the degree-28
cosine polynomial at grid node 486. -/
theorem edge_ratio_fourteen_lt_cosT14_nodeQ_486 :
    (edgeCoeff 14 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 486) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

/-- The upper cosine bracket stays above edge 14's threshold throughout its
increasing prefix.  The positive Taylor remainder is discarded and the
degree-28 polynomial is bounded below by its exact value at node 486. -/
theorem edge_ratio_fourteen_le_cosHiReal_of_prefix {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ (nodeQ RatInterval.piHi 2048 486 : ℚ)) :
    (edgeCoeff 14 : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x := by
  have hq486_pi4 : (nodeQ RatInterval.piHi 2048 486 : ℚ) ≤ Real.pi / 4 := by
    norm_num [nodeQ, RatInterval.piHi]
  have hmono := cosT14_antitoneOn
    (show (nodeQ RatInterval.piHi 2048 486 : ℚ) ∈
        Set.Icc 0 (Real.pi / 2) by
      exact ⟨by positivity, hq486_pi4.trans (by linarith [Real.pi_pos])⟩)
    (show x ∈ Set.Icc 0 (Real.pi / 2) by
      exact ⟨hx0, hx1.trans (hq486_pi4.trans (by linarith [Real.pi_pos]))⟩)
    hx1
  have hrat : (edgeCoeff 14 : ℝ) / (19 / 50 : ℝ) ^ 2 <
      (cosTQ 14 (nodeQ RatInterval.piHi 2048 486) : ℝ) := by
    exact_mod_cast edge_ratio_fourteen_lt_cosT14_nodeQ_486
  have htail : 0 ≤ x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by positivity
  have hct : cosT 14 x ≤ cosT 14 (nodeQ RatInterval.piHi 2048 486 : ℚ) := by
    exact hmono hx0
  unfold cosHiReal
  linarith

/-- The edge-14 cosine argument applies to any edge whose exact threshold lies
below its witness-node Taylor value. -/
theorem edge_ratio_le_cosHiReal_of_prefix (i : Fin 21) (w : Fin 2049)
    (hw_pi2 : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ Real.pi / 2)
    (hratio : (edgeCoeff i : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 w))
    {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ (nodeQ RatInterval.piHi 2048 w : ℚ)) :
    (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x := by
  have hmono := cosT14_antitoneOn
    (show (nodeQ RatInterval.piHi 2048 w : ℚ) ∈
        Set.Icc 0 (Real.pi / 2) by
      exact ⟨by positivity, hw_pi2⟩)
    (show x ∈ Set.Icc 0 (Real.pi / 2) by
      exact ⟨hx0, hx1.trans hw_pi2⟩)
    hx1
  have hrat : (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 <
      (cosTQ 14 (nodeQ RatInterval.piHi 2048 w) : ℝ) := by
    exact_mod_cast hratio
  have htail : 0 ≤ x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by positivity
  have hct : cosT 14 x ≤ cosT 14 (nodeQ RatInterval.piHi 2048 w : ℚ) := by
    exact hmono hx0
  unfold cosHiReal
  linarith

/-- Witness-node version of the cosine bridge on the extended interval
`[0, 3π/4]`. -/
theorem edge_ratio_le_cosHiReal_of_prefix_three_pi_div_four
    (i : Fin 21) (w : Fin 2049)
    (hw3 : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ 3 * Real.pi / 4)
    (hratio : (edgeCoeff i : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 w))
    {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ (nodeQ RatInterval.piHi 2048 w : ℚ)) :
    (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x := by
  have hmono := cosT14_antitoneOn_three_pi_div_four
    (show (nodeQ RatInterval.piHi 2048 w : ℚ) ∈
        Set.Icc 0 (3 * Real.pi / 4) by
      exact ⟨by positivity, hw3⟩)
    (show x ∈ Set.Icc 0 (3 * Real.pi / 4) by
      exact ⟨hx0, hx1.trans hw3⟩)
    hx1
  have hrat : (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 <
      (cosTQ 14 (nodeQ RatInterval.piHi 2048 w) : ℝ) := by
    exact_mod_cast hratio
  have htail : 0 ≤ x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by positivity
  have hct : cosT 14 x ≤ cosT 14 (nodeQ RatInterval.piHi 2048 w : ℚ) := by
    exact hmono hx0
  unfold cosHiReal
  linarith

/-- An exact threshold below the cosine Taylor value at a node makes the edge
bracket nondecreasing on the preceding prefix. -/
theorem edgeHiReal_monotoneOn_of_ratio_le (i : Fin 21) (w : Fin 2049)
    (hcos : ∀ x ∈ Set.Icc 0 (nodeQ RatInterval.piHi 2048 w : ℚ),
      (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x) :
    MonotoneOn (edgeHiReal (edgeCoeff i))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 w : ℚ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · exact fun x _ =>
      (hasDerivAt_edgeHiReal (edgeCoeff i) x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_edgeHiReal (edgeCoeff i) x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_edgeHiReal (edgeCoeff i) x).deriv]
    have hA : (0 : ℝ) < (19 / 50 : ℝ) ^ 2 := by norm_num
    have hc := hcos x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hprod : (edgeCoeff i : ℝ) ≤
        (19 / 50 : ℝ) ^ 2 * cosHiReal x := by
      calc
        (edgeCoeff i : ℝ) =
            (19 / 50 : ℝ) ^ 2 *
              ((edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2) := by
          field_simp [ne_of_gt hA]
        _ ≤ (19 / 50 : ℝ) ^ 2 * cosHiReal x :=
          mul_le_mul_of_nonneg_left hc hA.le
    linarith

theorem edge_ratio_fifteen_lt_cosT14_nodeQ_389 :
    (edgeCoeff 15 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 389) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_fifteen :
    MonotoneOn (edgeHiReal (edgeCoeff 15))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 389 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 15 389
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 15 389
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_fifteen_lt_cosT14_nodeQ_389
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_fifteen : EdgeIncTo 15 := by
  apply edgeIncTo_of_monotoneOn_to 15 389
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_fifteen

theorem edge_ratio_nineteen_lt_cosT14_nodeQ_389 :
    (edgeCoeff 19 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 389) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_nineteen :
    MonotoneOn (edgeHiReal (edgeCoeff 19))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 389 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 19 389
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 19 389
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_nineteen_lt_cosT14_nodeQ_389
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_nineteen : EdgeIncTo 19 := by
  apply edgeIncTo_of_monotoneOn_to 19 389
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_nineteen

theorem edge_ratio_twenty_lt_cosT14_nodeQ_486 :
    (edgeCoeff 20 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 486) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_twenty :
    MonotoneOn (edgeHiReal (edgeCoeff 20))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 486 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 20 486
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 20 486
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_twenty_lt_cosT14_nodeQ_486
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_twenty : EdgeIncTo 20 := by
  apply edgeIncTo_of_monotoneOn_to 20 486
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_twenty

theorem edge_ratio_zero_lt_cosT14_nodeQ_543 :
    (edgeCoeff 0 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 543) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_zero :
    MonotoneOn (edgeHiReal (edgeCoeff 0))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 543 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 0 543
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 0 543
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_zero_lt_cosT14_nodeQ_543
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_zero : EdgeIncTo 0 := by
  apply edgeIncTo_of_monotoneOn_to 0 543
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_zero

theorem edge_ratio_one_lt_cosT14_nodeQ_878 :
    (edgeCoeff 1 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 878) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_one :
    MonotoneOn (edgeHiReal (edgeCoeff 1))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 878 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 1 878
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 1 878
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_one_lt_cosT14_nodeQ_878
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_one : EdgeIncTo 1 := by
  apply edgeIncTo_of_monotoneOn_to 1 878
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_one

theorem edge_ratio_eight_lt_cosT14_nodeQ_878 :
    (edgeCoeff 8 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 878) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_eight :
    MonotoneOn (edgeHiReal (edgeCoeff 8))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 878 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 8 878
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 8 878
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_eight_lt_cosT14_nodeQ_878
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_eight : EdgeIncTo 8 := by
  apply edgeIncTo_of_monotoneOn_to 8 878
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_eight

/-- A threshold at the node before a peak, followed by one exact grid step,
closes an increasing prefix when the peak lies beyond `π/2`. -/
theorem edgeIncTo_of_prefix_three_pi_div_four (i : Fin 21)
    (w prev : Fin 2049) (hprev : prev.val + 1 = w.val)
    (hw : w = edgeWitness i)
    (hw3 : (nodeQ RatInterval.piHi 2048 prev : ℚ) ≤ 3 * Real.pi / 4)
    (hratio : (edgeCoeff i : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 prev))
    (hstep : edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 prev) ≤
      edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w)) : EdgeIncTo i := by
  apply edgeIncTo_of_monotoneOn_to_prev_and_step i w prev hprev hw
  · apply edgeHiReal_monotoneOn_of_ratio_le i prev
    intro x hx
    exact edge_ratio_le_cosHiReal_of_prefix_three_pi_div_four i prev hw3 hratio
      hx.1 hx.2
  · exact hstep

theorem edgeIncTo_two : EdgeIncTo 2 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 2 1112 1111
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_three : EdgeIncTo 3 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 3 1064 1063
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_four : EdgeIncTo 4 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 4 1073 1072
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_five : EdgeIncTo 5 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 5 1073 1072
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_six : EdgeIncTo 6 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 6 1064 1063
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_seven : EdgeIncTo 7 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 7 1112 1111
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_nine : EdgeIncTo 9 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 9 1489 1488
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_ten : EdgeIncTo 10 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 10 1489 1488
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

theorem edgeIncTo_eleven : EdgeIncTo 11 := by
  apply edgeIncTo_of_prefix_three_pi_div_four 11 1118 1117
  · norm_num
  · norm_num [edgeWitness]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, RatInterval.piHi, Finset.sum_range_succ]

/-- The upper cosine bracket decreases from node 1118 through `3π/4`. -/
theorem cosHiReal_antitoneOn_1118_to_three_pi_div_four :
    AntitoneOn cosHiReal
      (Set.Icc (nodeQ RatInterval.piHi 2048 1118 : ℚ) (3 * Real.pi / 4)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_cosHiReal x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_cosHiReal x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosHiReal x).deriv]
    apply neg_nonpos.mpr
    by_cases hhalf : x ≤ Real.pi / 2
    · exact sinT14_nonneg (le_of_lt hx.1) hhalf
    · have hhalf' : Real.pi / 2 ≤ x := le_of_lt (lt_of_not_ge hhalf)
      by_cases htwo : x ≤ 2
      · exact sinT14_nonneg_of_half_pi_le_of_le_two hhalf' htwo
      · exact sinT14_nonneg_of_two_le_of_le_three_pi_div_four
          (le_of_lt (lt_of_not_ge htwo)) (le_of_lt hx.2)

/-- A decreasing analytic tail beginning one grid point after a witness closes
a decreasing suffix, provided the intervening grid step is checked exactly. -/
theorem edgeDecFrom_of_antitoneOn_from_next (i : Fin 21) (w wnext : Fin 2049)
    (hw : w = edgeWitness i) (hnext : wnext.val = w.val + 1)
    (hstep : edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 wnext) ≤
      edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w))
    (hanti : AntitoneOn (edgeHiReal (edgeCoeff i))
      (Set.Icc (nodeQ RatInterval.piHi 2048 wnext) (RatInterval.piHi : ℝ))) :
    EdgeDecFrom i := by
  intro k hk
  rcases lt_or_eq_of_le hk with hlt | hkw
  · have hwle : wnext ≤ k := by
      apply Fin.le_iff_val_le_val.mpr
      have hwlt : w.val < k.val := hlt
      omega
    have hqk0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 k := by
      unfold nodeQ
      positivity
    have hqw0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 wnext := by
      unfold nodeQ
      positivity
    have hqkhi : (nodeQ RatInterval.piHi 2048 k : ℚ) ≤ RatInterval.piHi := by
      unfold nodeQ
      have hkR : (k.val : ℝ) ≤ 2048 := by exact_mod_cast k.isLt
      have hp : (0 : ℝ) ≤ (RatInterval.piHi : ℝ) := by norm_num [RatInterval.piHi]
      have hqR : ((nodeQ RatInterval.piHi 2048 k : ℚ) : ℝ) ≤ (RatInterval.piHi : ℝ) := by
        unfold nodeQ
        push_cast
        nlinarith
      exact_mod_cast hqR
    have hqwhi : (nodeQ RatInterval.piHi 2048 wnext : ℚ) ≤ RatInterval.piHi := by
      unfold nodeQ
      have hwR : (wnext.val : ℝ) ≤ 2048 := by exact_mod_cast wnext.isLt
      have hp : (0 : ℝ) ≤ (RatInterval.piHi : ℝ) := by norm_num [RatInterval.piHi]
      have hqR : ((nodeQ RatInterval.piHi 2048 wnext : ℚ) : ℝ) ≤ (RatInterval.piHi : ℝ) := by
        unfold nodeQ
        push_cast
        nlinarith
      exact_mod_cast hqR
    have hqle : nodeQ RatInterval.piHi 2048 wnext ≤ nodeQ RatInterval.piHi 2048 k := by
      unfold nodeQ
      have hwk : (wnext.val : ℚ) ≤ (k.val : ℚ) := by exact_mod_cast hwle
      have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwk hp) (by norm_num)
    have hanti' : edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
        edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 wnext) := by
      exact hanti ⟨by exact_mod_cast hqw0, by exact_mod_cast hqwhi⟩
        ⟨by exact_mod_cast hqk0, by exact_mod_cast hqkhi⟩ (by exact_mod_cast hqle)
    have hR : ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) : ℚ) : ℝ) ≤
        ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 wnext) : ℚ) : ℝ) := by
      rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) hqk0]
      rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 wnext) hqw0]
      exact hanti'
    have hfin : edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
        edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 wnext) := by
      exact_mod_cast hR
    exact hfin.trans hstep
  · rw [hkw, hw]
    exact le_rfl

/-- The upper cosine bracket is antitone from any nonnegative grid node up to
`3*pi/4`.  This combines the already-proved signs of the degree-27 sine
bracket on `[0, pi/2]`, `[pi/2, 2]`, and `[2, 3*pi/4]`. -/
theorem cosHiReal_antitoneOn_up_to_three_pi_div_four {s : ℚ}
    (hs0 : 0 ≤ s) (hs : (s : ℝ) ≤ 3 * Real.pi / 4) :
    AntitoneOn cosHiReal (Set.Icc (s : ℝ) (3 * Real.pi / 4)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_cosHiReal x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_cosHiReal x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosHiReal x).deriv]
    apply neg_nonpos.mpr
    have hs0R : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs0
    by_cases hhalf : x ≤ Real.pi / 2
    · exact sinT14_nonneg (le_trans hs0R (le_of_lt hx.1)) hhalf
    · have hhalf' : Real.pi / 2 ≤ x := le_of_lt (lt_of_not_ge hhalf)
      by_cases htwo : x ≤ 2
      · exact sinT14_nonneg_of_half_pi_le_of_le_two hhalf' htwo
      · exact sinT14_nonneg_of_two_le_of_le_three_pi_div_four
          (le_of_lt (lt_of_not_ge htwo)) (le_of_lt hx.2)

/-- A grid-node comparison with the exact cosine threshold propagates over the
whole decreasing grid tail.  The final interval is covered by the proved
`-2/3` cosine bound. -/
theorem cosHiReal_le_edge_ratio_of_nodeQ_le {i : Fin 21} {s w : Fin 2049}
    (hs : s = w)
    (hval : cosHiNLag (nodeQ RatInterval.piHi 2048 w) ≤
      edgeCoeff i / (19 / 50 : ℚ) ^ 2)
    (h3 : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ 3 * Real.pi / 4)
    (htail : (-(2 / 3) : ℚ) ≤ edgeCoeff i / (19 / 50 : ℚ) ^ 2)
    {x : ℝ} (hx0 : (nodeQ RatInterval.piHi 2048 s : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  subst hs
  have hq0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 w := by
    unfold nodeQ
    positivity
  have hcast : ((cosHiNLag (nodeQ RatInterval.piHi 2048 w) : ℚ) : ℝ) =
      cosHiReal (nodeQ RatInterval.piHi 2048 w : ℚ) := by
    rw [cosHiNLag_cast, cosHiReal]
    have hq0R : (0 : ℝ) ≤ (nodeQ RatInterval.piHi 2048 w : ℚ) := by
      exact_mod_cast hq0
    rw [abs_of_nonneg hq0R]
  have hvalR : cosHiReal (nodeQ RatInterval.piHi 2048 w : ℚ) ≤
      (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    rw [← hcast]
    exact_mod_cast hval
  have htailR : (-(2 / 3) : ℝ) ≤
      (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast htail
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hanti := cosHiReal_antitoneOn_up_to_three_pi_div_four hq0 h3
    exact (hanti ⟨le_rfl, h3⟩ ⟨hx0, h34⟩ hx0).trans hvalR
  · have h34' : 3 * Real.pi / 4 ≤ x := le_of_lt (lt_of_not_ge h34)
    exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le h34' hx).trans htailR

/-- The corresponding edge-bracket antitone wrapper on a node tail. -/
theorem edgeHiReal_antitoneOn_of_nodeQ_cos_le_ratio {i : Fin 21} {w : Fin 2049}
    (hcos : ∀ x ∈ Set.Icc (nodeQ RatInterval.piHi 2048 w : ℚ)
      (RatInterval.piHi : ℝ),
      cosHiReal x ≤ (edgeCoeff i : ℝ) / (19 / 50 : ℝ) ^ 2) :
    AntitoneOn (edgeHiReal (edgeCoeff i))
      (Set.Icc (nodeQ RatInterval.piHi 2048 w : ℚ) (RatInterval.piHi : ℝ)) := by
  apply edgeHiReal_antitoneOn_of_cos_le_coeff (edgeCoeff i)
    (nodeQ RatInterval.piHi 2048 w)
  intro x hx
  exact hcos x ⟨le_of_lt hx.1, hx.2⟩

theorem edgeDecFrom_of_witness_nodeQ_cos_le_ratio (i : Fin 21) (w : Fin 2049)
    (hw : w = edgeWitness i)
    (hval : cosHiNLag (nodeQ RatInterval.piHi 2048 w) ≤
      edgeCoeff i / (19 / 50 : ℚ) ^ 2)
    (h3 : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ 3 * Real.pi / 4)
    (htail : (-(2 / 3) : ℚ) ≤ edgeCoeff i / (19 / 50 : ℚ) ^ 2) :
    EdgeDecFrom i := by
  apply edgeDecFrom_of_antitoneOn_from i w hw
  apply edgeHiReal_antitoneOn_of_nodeQ_cos_le_ratio
  intro x hx
  exact cosHiReal_le_edge_ratio_of_nodeQ_le rfl hval h3 htail hx.1 hx.2

theorem edgeDecFrom_of_next_nodeQ_cos_le_ratio (i : Fin 21)
    (w wnext : Fin 2049) (hw : w = edgeWitness i)
    (hnext : wnext.val = w.val + 1)
    (hstep : edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 wnext) ≤
      edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w))
    (hval : cosHiNLag (nodeQ RatInterval.piHi 2048 wnext) ≤
      edgeCoeff i / (19 / 50 : ℚ) ^ 2)
    (h3 : (nodeQ RatInterval.piHi 2048 wnext : ℚ) ≤ 3 * Real.pi / 4)
    (htail : (-(2 / 3) : ℚ) ≤ edgeCoeff i / (19 / 50 : ℚ) ^ 2) :
    EdgeDecFrom i := by
  apply edgeDecFrom_of_antitoneOn_from_next i w wnext hw hnext hstep
  apply edgeHiReal_antitoneOn_of_nodeQ_cos_le_ratio
  intro x hx
  exact cosHiReal_le_edge_ratio_of_nodeQ_le rfl hval h3 htail hx.1 hx.2

theorem neg_131_over_200_le_edge_ratio_nine :
    (-131 / 200 : ℚ) ≤ edgeCoeff 9 / (19 / 50 : ℚ) ^ 2 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem neg_131_over_200_le_edge_ratio_ten :
    (-131 / 200 : ℚ) ≤ edgeCoeff 10 / (19 / 50 : ℚ) ^ 2 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem neg_two_thirds_le_edge_ratio_nine :
    (-(2 / 3) : ℚ) ≤ edgeCoeff 9 / (19 / 50 : ℚ) ^ 2 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem neg_two_thirds_le_edge_ratio_ten :
    (-(2 / 3) : ℚ) ≤ edgeCoeff 10 / (19 / 50 : ℚ) ^ 2 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem cosHiReal_le_edge_ratio_nine {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1490 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ (edgeCoeff 9 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  have hratio_narrow : (-131 / 200 : ℝ) ≤
      (edgeCoeff 9 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast neg_131_over_200_le_edge_ratio_nine
  have hratio_high : (-(2 / 3) : ℝ) ≤
      (edgeCoeff 9 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast neg_two_thirds_le_edge_ratio_nine
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · exact (cosHiReal_le_neg_131_over_200_of_narrow hx0 h34).trans hratio_narrow
  · have h34' : 3 * Real.pi / 4 ≤ x := le_of_lt (lt_of_not_ge h34)
    exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le h34' hx).trans hratio_high

theorem cosHiReal_le_edge_ratio_ten {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1490 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ (edgeCoeff 10 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  have hratio_narrow : (-131 / 200 : ℝ) ≤
      (edgeCoeff 10 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast neg_131_over_200_le_edge_ratio_ten
  have hratio_high : (-(2 / 3) : ℝ) ≤
      (edgeCoeff 10 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast neg_two_thirds_le_edge_ratio_ten
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · exact (cosHiReal_le_neg_131_over_200_of_narrow hx0 h34).trans hratio_narrow
  · have h34' : 3 * Real.pi / 4 ≤ x := le_of_lt (lt_of_not_ge h34)
    exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le h34' hx).trans hratio_high

theorem edgeHiReal_antitoneOn_nine :
    AntitoneOn (edgeHiReal (edgeCoeff 9))
      (Set.Icc (nodeQ RatInterval.piHi 2048 1490) (RatInterval.piHi : ℝ)) := by
  apply edgeHiReal_antitoneOn_of_cos_le_coeff (edgeCoeff 9) 1490
  intro x hx
  exact cosHiReal_le_edge_ratio_nine (le_of_lt hx.1) hx.2

theorem edgeHiReal_antitoneOn_ten :
    AntitoneOn (edgeHiReal (edgeCoeff 10))
      (Set.Icc (nodeQ RatInterval.piHi 2048 1490) (RatInterval.piHi : ℝ)) := by
  apply edgeHiReal_antitoneOn_of_cos_le_coeff (edgeCoeff 10) 1490
  intro x hx
  exact cosHiReal_le_edge_ratio_ten (le_of_lt hx.1) hx.2

theorem edgeStep_nine :
    edgeUpper (edgeCoeff 9) (nodeQ RatInterval.piHi 2048 1490) ≤
      edgeUpper (edgeCoeff 9) (nodeQ RatInterval.piHi 2048 1489) := by
  norm_num [edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag, sinTQ,
    Finset.sum_range_succ, RatInterval.piHi]

theorem edgeStep_ten :
    edgeUpper (edgeCoeff 10) (nodeQ RatInterval.piHi 2048 1490) ≤
      edgeUpper (edgeCoeff 10) (nodeQ RatInterval.piHi 2048 1489) := by
  norm_num [edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag, sinTQ,
    Finset.sum_range_succ, RatInterval.piHi]

theorem edgeDecFrom_nine : EdgeDecFrom 9 := by
  apply edgeDecFrom_of_antitoneOn_from_next 9 1489 1490
  · norm_num [edgeWitness]
  · norm_num
  · exact edgeStep_nine
  · exact edgeHiReal_antitoneOn_nine

theorem edgeDecFrom_ten : EdgeDecFrom 10 := by
  apply edgeDecFrom_of_antitoneOn_from_next 10 1489 1490
  · norm_num [edgeWitness]
  · norm_num
  · exact edgeStep_ten
  · exact edgeHiReal_antitoneOn_ten

theorem neg_103_over_720_le_edge_ratio_eleven :
    (-103 / 720 : ℚ) ≤ edgeCoeff 11 / (19 / 50 : ℚ) ^ 2 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem neg_two_thirds_le_edge_ratio_eleven :
    (-(2 / 3) : ℚ) ≤ edgeCoeff 11 / (19 / 50 : ℚ) ^ 2 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem cosHiReal_nodeQ_1118_le_neg_103_over_720 :
    cosHiReal (nodeQ RatInterval.piHi 2048 1118 : ℚ) ≤ (-103 / 720 : ℝ) := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 1118
  have hq0 : (0 : ℚ) ≤ q := by
    unfold q nodeQ
    positivity
  have hcast : ((cosHiNLag q : ℚ) : ℝ) = cosHiReal (q : ℝ) := by
    rw [cosHiNLag_cast, cosHiReal]
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    rw [abs_of_nonneg hq0R]
  have h : cosHiNLag q ≤ (-103 / 720 : ℚ) := by
    norm_num [q, cosHiNLag, cosTQ, nodeQ, RatInterval.piHi, Finset.sum_range_succ]
  have hR : ((cosHiNLag q : ℚ) : ℝ) ≤ ((-103 / 720 : ℚ) : ℝ) := by
    exact_mod_cast h
  rw [hcast] at hR
  exact hR

theorem cosHiReal_le_edge_ratio_eleven {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1118 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ (edgeCoeff 11 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  have hratio_low : (-103 / 720 : ℝ) ≤
      (edgeCoeff 11 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast neg_103_over_720_le_edge_ratio_eleven
  have hratio_high : (-(2 / 3) : ℝ) ≤
      (edgeCoeff 11 : ℝ) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast neg_two_thirds_le_edge_ratio_eleven
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hs34 : (nodeQ RatInterval.piHi 2048 1118 : ℚ) ≤ 3 * Real.pi / 4 := by
      norm_num [nodeQ, RatInterval.piHi]
    have hanti := cosHiReal_antitoneOn_1118_to_three_pi_div_four
      ⟨le_rfl, hs34⟩ ⟨hx0, h34⟩ hx0
    exact hanti.trans (cosHiReal_nodeQ_1118_le_neg_103_over_720.trans hratio_low)
  · have h34' : 3 * Real.pi / 4 ≤ x := le_of_lt (lt_of_not_ge h34)
    exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le h34' hx).trans hratio_high

theorem edgeHiReal_antitoneOn_eleven :
    AntitoneOn (edgeHiReal (edgeCoeff 11))
      (Set.Icc (nodeQ RatInterval.piHi 2048 1118) (RatInterval.piHi : ℝ)) := by
  apply edgeHiReal_antitoneOn_of_cos_le_coeff (edgeCoeff 11) 1118
  intro x hx
  exact cosHiReal_le_edge_ratio_eleven (le_of_lt hx.1) hx.2

theorem edgeDecFrom_eleven : EdgeDecFrom 11 := by
  apply edgeDecFrom_of_antitoneOn_from 11 1118
  · norm_num [edgeWitness]
  · exact edgeHiReal_antitoneOn_eleven

/-- The degree-28 edge bracket increases throughout edge 14's prefix. -/
theorem edgeHiReal_monotoneOn_fourteen :
    MonotoneOn (edgeHiReal (edgeCoeff 14))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 486 : ℚ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_edgeHiReal (edgeCoeff 14) x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_edgeHiReal (edgeCoeff 14) x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_edgeHiReal (edgeCoeff 14) x).deriv]
    have hA : (0 : ℝ) < (19 / 50 : ℝ) ^ 2 := by norm_num
    have hcos := edge_ratio_fourteen_le_cosHiReal_of_prefix (le_of_lt hx.1) (le_of_lt hx.2)
    have hprod : (edgeCoeff 14 : ℝ) ≤
        (19 / 50 : ℝ) ^ 2 * cosHiReal x := by
      calc
        (edgeCoeff 14 : ℝ) =
            (19 / 50 : ℝ) ^ 2 *
              ((edgeCoeff 14 : ℝ) / (19 / 50 : ℝ) ^ 2) := by
          field_simp [ne_of_gt hA]
        _ ≤ (19 / 50 : ℝ) ^ 2 * cosHiReal x :=
          mul_le_mul_of_nonneg_left hcos hA.le
    linarith

/-- A monotone analytic prefix closes an increasing-grid-prefix obligation. -/
theorem edgeIncTo_of_monotoneOn_to (i : Fin 21) (w : Fin 2049)
    (hw : w = edgeWitness i)
    (hmono : MonotoneOn (edgeHiReal (edgeCoeff i))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 w : ℚ))) :
    EdgeIncTo i := by
  intro k hk
  rcases lt_or_eq_of_le hk with hlt | hkw
  · have hqk0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 k := by
      unfold nodeQ
      positivity
    have hqw0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 w := by
      unfold nodeQ
      positivity
    have hqle : nodeQ RatInterval.piHi 2048 k ≤ nodeQ RatInterval.piHi 2048 w := by
      unfold nodeQ
      have hkw' : (k.val : ℚ) ≤ (w.val : ℚ) := by
        exact_mod_cast (Fin.le_iff_val_le_val.mpr (le_of_lt hlt))
      have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkw' hp) (by norm_num)
    have hmono' : edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
        edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w) := by
      exact hmono ⟨by exact_mod_cast hqk0, hqle⟩
        ⟨by exact_mod_cast hqw0, le_rfl⟩ hqle
    have hR : ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) : ℚ) : ℝ) ≤
        ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w) : ℚ) : ℝ) := by
      rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) hqk0]
      rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w) hqw0]
      exact hmono'
    have hfin : edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
        edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w) := by
      exact_mod_cast hR
    simpa [hw] using hfin
  · rw [hkw, hw]
    exact le_rfl

/-- A monotone prefix ending at the node immediately before a peak, followed
by one exact grid step, closes the increasing-prefix obligation. -/
theorem edgeIncTo_of_monotoneOn_to_prev_and_step (i : Fin 21)
    (w prev : Fin 2049) (hprev : prev.val + 1 = w.val)
    (hw : w = edgeWitness i)
    (hmono : MonotoneOn (edgeHiReal (edgeCoeff i))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 prev : ℚ)))
    (hstep : edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 prev) ≤
      edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w)) :
    EdgeIncTo i := by
  intro k hk
  by_cases hkp : k ≤ prev
  · have hqk0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 k := by
      unfold nodeQ
      positivity
    have hqp0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 prev := by
      unfold nodeQ
      positivity
    have hqle : nodeQ RatInterval.piHi 2048 k ≤
        nodeQ RatInterval.piHi 2048 prev := by
      unfold nodeQ
      have hkv : (k.val : ℚ) ≤ (prev.val : ℚ) := by
        exact_mod_cast (Fin.le_iff_val_le_val.mp hkp)
      have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkv hp) (by norm_num)
    have hmono' : edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
        edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 prev) := by
      exact hmono ⟨by exact_mod_cast hqk0, hqle⟩
        ⟨by exact_mod_cast hqp0, le_rfl⟩ hqle
    have hR : ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) : ℚ) : ℝ) ≤
        ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 prev) : ℚ) : ℝ) := by
      rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) hqk0]
      rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 prev) hqp0]
      exact hmono'
    have hfin : edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
        edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 prev) := by
      exact_mod_cast hR
    exact hfin.trans hstep
  · have hlt : prev.val < k.val := by
      exact Fin.lt_def.mp (lt_of_not_ge hkp)
    have hkle : k.val ≤ w.val := Fin.le_iff_val_le_val.mp hk
    have hkeq : k = w := Fin.ext (by omega)
    rw [hkeq, hw]
    exact le_rfl

theorem edge_ratio_sixteen_lt_cosT14_nodeQ_410 :
    (edgeCoeff 16 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 410) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_sixteen :
    MonotoneOn (edgeHiReal (edgeCoeff 16))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 410 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 16 410
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 16 410
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_sixteen_lt_cosT14_nodeQ_410
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_sixteen : EdgeIncTo 16 := by
  apply edgeIncTo_of_monotoneOn_to_prev_and_step 16 411 410
  · norm_num
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_sixteen
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, Finset.sum_range_succ, RatInterval.piHi]

theorem edge_ratio_seventeen_lt_cosT14_nodeQ_405 :
    (edgeCoeff 17 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 405) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_seventeen :
    MonotoneOn (edgeHiReal (edgeCoeff 17))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 405 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 17 405
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 17 405
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_seventeen_lt_cosT14_nodeQ_405
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_seventeen : EdgeIncTo 17 := by
  apply edgeIncTo_of_monotoneOn_to_prev_and_step 17 406 405
  · norm_num
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_seventeen
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, Finset.sum_range_succ, RatInterval.piHi]

theorem edge_ratio_eighteen_lt_cosT14_nodeQ_410 :
    (edgeCoeff 18 : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 410) := by
  norm_num [edgeCoeff, tableEdges, mu, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ]

theorem edgeHiReal_monotoneOn_eighteen :
    MonotoneOn (edgeHiReal (edgeCoeff 18))
      (Set.Icc 0 (nodeQ RatInterval.piHi 2048 410 : ℚ)) := by
  apply edgeHiReal_monotoneOn_of_ratio_le 18 410
  intro x hx
  apply edge_ratio_le_cosHiReal_of_prefix 18 410
  · norm_num [nodeQ, RatInterval.piHi]
  · exact edge_ratio_eighteen_lt_cosT14_nodeQ_410
  · exact hx.1
  · exact hx.2

theorem edgeIncTo_eighteen : EdgeIncTo 18 := by
  apply edgeIncTo_of_monotoneOn_to_prev_and_step 18 411 410
  · norm_num
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_eighteen
  · norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag,
      sinTQ, Finset.sum_range_succ, RatInterval.piHi]

theorem edgeIncTo_fourteen : EdgeIncTo 14 := by
  apply edgeIncTo_of_monotoneOn_to 14 486
  · norm_num [edgeWitness]
  · exact edgeHiReal_monotoneOn_fourteen

/-- A zero-witness edge has a one-point increasing prefix. -/
theorem edgeIncTo_of_witness_zero (i : Fin 21) (hw : edgeWitness i = 0) :
    EdgeIncTo i := by
  intro k hk
  rw [hw] at hk
  have hk0 : k = 0 := Fin.ext (Nat.eq_zero_of_le_zero hk)
  rw [hk0, hw]
  exact le_rfl

theorem edgeIncTo_twelve : EdgeIncTo 12 := by
  apply edgeIncTo_of_witness_zero 12
  norm_num [edgeWitness]

theorem edgeIncTo_thirteen : EdgeIncTo 13 := by
  apply edgeIncTo_of_witness_zero 13
  norm_num [edgeWitness]

theorem edgeDecFrom_one : EdgeDecFrom 1 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 1 878
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_two : EdgeDecFrom 2 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 2 1112
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_three : EdgeDecFrom 3 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 3 1064
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_four : EdgeDecFrom 4 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 4 1073
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_five : EdgeDecFrom 5 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 5 1073
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_six : EdgeDecFrom 6 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 6 1064
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_seven : EdgeDecFrom 7 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 7 1112
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_eight : EdgeDecFrom 8 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 8 878
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_sixteen : EdgeDecFrom 16 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 16 411
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_seventeen : EdgeDecFrom 17 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 17 406
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_eighteen : EdgeDecFrom 18 := by
  apply edgeDecFrom_of_witness_nodeQ_cos_le_ratio 18 411
  · norm_num [edgeWitness]
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeStep_zero :
    edgeUpper (edgeCoeff 0) (nodeQ RatInterval.piHi 2048 544) ≤
      edgeUpper (edgeCoeff 0) (nodeQ RatInterval.piHi 2048 543) := by
  norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag, sinTQ,
    Finset.sum_range_succ, RatInterval.piHi]

theorem edgeDecFrom_zero : EdgeDecFrom 0 := by
  apply edgeDecFrom_of_next_nodeQ_cos_le_ratio 0 543 544
  · norm_num [edgeWitness]
  · norm_num
  · exact edgeStep_zero
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeStep_fourteen :
    edgeUpper (edgeCoeff 14) (nodeQ RatInterval.piHi 2048 487) ≤
      edgeUpper (edgeCoeff 14) (nodeQ RatInterval.piHi 2048 486) := by
  norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag, sinTQ,
    Finset.sum_range_succ, RatInterval.piHi]

theorem edgeDecFrom_fourteen : EdgeDecFrom 14 := by
  apply edgeDecFrom_of_next_nodeQ_cos_le_ratio 14 486 487
  · norm_num [edgeWitness]
  · norm_num
  · exact edgeStep_fourteen
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeStep_fifteen :
    edgeUpper (edgeCoeff 15) (nodeQ RatInterval.piHi 2048 390) ≤
      edgeUpper (edgeCoeff 15) (nodeQ RatInterval.piHi 2048 389) := by
  norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag, sinTQ,
    Finset.sum_range_succ, RatInterval.piHi]

theorem edgeDecFrom_fifteen : EdgeDecFrom 15 := by
  apply edgeDecFrom_of_next_nodeQ_cos_le_ratio 15 389 390
  · norm_num [edgeWitness]
  · norm_num
  · exact edgeStep_fifteen
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeStep_nineteen :
    edgeUpper (edgeCoeff 19) (nodeQ RatInterval.piHi 2048 390) ≤
      edgeUpper (edgeCoeff 19) (nodeQ RatInterval.piHi 2048 389) := by
  norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag, sinTQ,
    Finset.sum_range_succ, RatInterval.piHi]

theorem edgeDecFrom_nineteen : EdgeDecFrom 19 := by
  apply edgeDecFrom_of_next_nodeQ_cos_le_ratio 19 389 390
  · norm_num [edgeWitness]
  · norm_num
  · exact edgeStep_nineteen
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeStep_twenty :
    edgeUpper (edgeCoeff 20) (nodeQ RatInterval.piHi 2048 487) ≤
      edgeUpper (edgeCoeff 20) (nodeQ RatInterval.piHi 2048 486) := by
  norm_num [edgeUpper, edgeCoeff, tableEdges, mu, nodeQ, sinHiNLag, sinTQ,
    Finset.sum_range_succ, RatInterval.piHi]

theorem edgeDecFrom_twenty : EdgeDecFrom 20 := by
  apply edgeDecFrom_of_next_nodeQ_cos_le_ratio 20 486 487
  · norm_num [edgeWitness]
  · norm_num
  · exact edgeStep_twenty
  · norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ, edgeCoeff, tableEdges, mu]
  · norm_num [nodeQ, RatInterval.piHi]
  · norm_num [edgeCoeff, tableEdges, mu]

theorem edgeMonotone : EdgeMonotone := by
  intro i
  fin_cases i <;>
    first
    | exact ⟨edgeIncTo_zero, edgeDecFrom_zero⟩
    | exact ⟨edgeIncTo_one, edgeDecFrom_one⟩
    | exact ⟨edgeIncTo_two, edgeDecFrom_two⟩
    | exact ⟨edgeIncTo_three, edgeDecFrom_three⟩
    | exact ⟨edgeIncTo_four, edgeDecFrom_four⟩
    | exact ⟨edgeIncTo_five, edgeDecFrom_five⟩
    | exact ⟨edgeIncTo_six, edgeDecFrom_six⟩
    | exact ⟨edgeIncTo_seven, edgeDecFrom_seven⟩
    | exact ⟨edgeIncTo_eight, edgeDecFrom_eight⟩
    | exact ⟨edgeIncTo_nine, edgeDecFrom_nine⟩
    | exact ⟨edgeIncTo_ten, edgeDecFrom_ten⟩
    | exact ⟨edgeIncTo_eleven, edgeDecFrom_eleven⟩
    | exact ⟨edgeIncTo_twelve,
        SevenClassQ0Deg3EdgeSuffixHigh.edgeDecFrom_twelve⟩
    | exact ⟨edgeIncTo_thirteen,
        SevenClassQ0Deg3EdgeSuffixHigh.edgeDecFrom_thirteen⟩
    | exact ⟨edgeIncTo_fourteen, edgeDecFrom_fourteen⟩
    | exact ⟨edgeIncTo_fifteen, edgeDecFrom_fifteen⟩
    | exact ⟨edgeIncTo_sixteen, edgeDecFrom_sixteen⟩
    | exact ⟨edgeIncTo_seventeen, edgeDecFrom_seventeen⟩
    | exact ⟨edgeIncTo_eighteen, edgeDecFrom_eighteen⟩
    | exact ⟨edgeIncTo_nineteen, edgeDecFrom_nineteen⟩
    | exact ⟨edgeIncTo_twenty, edgeDecFrom_twenty⟩

theorem edgeUnimodal : EdgeUnimodal := fun i =>
  ⟨(edgeMonotone i).1, (edgeMonotone i).2, edgePeakValid_all i⟩

theorem edgeValid : EdgeValid := edgeValid_of_unimodal edgeUnimodal

end N11Formalization.SevenClassQ0Deg3EdgeShape
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_nine
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_ten
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_eleven
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_twelve
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_thirteen
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_fifteen
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_nineteen
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_twenty
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_fourteen
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_sixteen
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_seventeen
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_eighteen
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_two
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_three
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_four
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_five
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_six
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_seven
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_nine
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_ten
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_eleven
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_nine
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_ten
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_eleven
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_twelve
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_thirteen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_fifteen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_nineteen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_twenty
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_fourteen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_sixteen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_seventeen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_eighteen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_two
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_three
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_four
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_five
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_six
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_seven
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_nine
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_ten
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeIncTo_eleven
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeMonotone
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeUnimodal
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeValid
