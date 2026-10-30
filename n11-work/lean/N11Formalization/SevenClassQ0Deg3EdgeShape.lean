import N11Formalization.SevenClassQ0Deg3EdgeSuffixNonpos

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

end N11Formalization.SevenClassQ0Deg3EdgeShape
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_nine
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_ten
#check @N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_eleven
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_nine
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_ten
#print axioms N11Formalization.SevenClassQ0Deg3EdgeShape.edgeDecFrom_eleven
