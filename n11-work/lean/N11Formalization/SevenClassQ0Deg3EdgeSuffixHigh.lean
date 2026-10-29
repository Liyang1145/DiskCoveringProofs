import N11Formalization.SevenClassQ0Deg3EdgeReal

/-! Lane A: zero-peak edge suffixes with coefficient above `(19/50)^2`.

For an edge whose coefficient `b` exceeds `A = (19/50)^2`, the derivative is
`A * cosHiReal x - b < 0` throughout the grid.  This closes the decreasing
suffix for the two zero-peak positive-coefficient edges 12 and 13. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Cos
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open SevenClassQ0Deg3EdgeReal

/-- The upper cosine Taylor bracket is at most one on the full grid range. -/
theorem cosHiReal_le_one {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) : cosHiReal x ≤ 1 := by
  by_cases hhalf : x ≤ Real.pi / 2
  · have h := cosHiReal_antitoneOn
      (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) from
        ⟨le_rfl, by positivity⟩)
      (show x ∈ Set.Icc 0 (Real.pi / 2) from ⟨hx0, hhalf⟩) hx0
    simpa [cosHiReal, cosT] using h
  · have hhalf' : Real.pi / 2 ≤ x := le_of_lt (lt_of_not_ge hhalf)
    have hx4 : x ≤ 4 := hx.trans (by norm_num [RatInterval.piHi])
    have hb := cos_bound_abs 14 x
    rw [abs_of_nonneg hx0] at hb
    have hct : cosT 14 x ≤ Real.cos x + x ^ 28 /
        ((Nat.factorial 28 : ℕ) : ℝ) := by
      linarith [(abs_le.mp hb).1]
    have hcos : Real.cos x ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hhalf' (by
        have hp := Real.pi_gt_d20
        norm_num at hp
        linarith)
    have hpow : x ^ 28 ≤ 4 ^ 28 := pow_le_pow_left₀ hx0 hx4 28
    have hdiv : x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) ≤
        4 ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right hpow (by positivity)
    have hsmall : 4 ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) := by
      norm_num [Nat.factorial]
    unfold cosHiReal
    linarith

/-- A coefficient above `(19/50)^2` makes the edge derivative negative. -/
theorem edgeHiReal_deriv_neg_of_coeff_gt_A {b : ℚ}
    (hb : (19 / 50 : ℚ) ^ 2 < b) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    (19 / 50 : ℝ) ^ 2 * cosHiReal x - (b : ℝ) < 0 := by
  have hbR : (19 / 50 : ℝ) ^ 2 < (b : ℝ) := by exact_mod_cast hb
  have hcos := cosHiReal_le_one hx0 hx
  have hmul : (19 / 50 : ℝ) ^ 2 * cosHiReal x ≤ (19 / 50 : ℝ) ^ 2 :=
    mul_le_of_le_one_right (by norm_num) hcos
  linarith

/-- The high-coefficient edge bracket decreases on the whole grid interval. -/
theorem edgeHiReal_antitoneOn_of_coeff_gt_A {b : ℚ}
    (hb : (19 / 50 : ℚ) ^ 2 < b) :
    AntitoneOn (edgeHiReal b) (Set.Icc 0 (RatInterval.piHi : ℝ)) := by
  refine edgeHiReal_antitoneOn_of_deriv_nonpos b ?_
  intro x hx
  exact (edgeHiReal_deriv_neg_of_coeff_gt_A hb (le_of_lt hx.1) hx.2).le

theorem edgeCoeff_twelve_gt_A :
    (19 / 50 : ℚ) ^ 2 < edgeCoeff 12 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem edgeCoeff_thirteen_gt_A :
    (19 / 50 : ℚ) ^ 2 < edgeCoeff 13 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem edgeDecFrom_twelve : EdgeDecFrom 12 := by
  apply edgeDecFrom_of_antitoneOn
  · norm_num [edgeWitness]
  · exact edgeHiReal_antitoneOn_of_coeff_gt_A edgeCoeff_twelve_gt_A

theorem edgeDecFrom_thirteen : EdgeDecFrom 13 := by
  apply edgeDecFrom_of_antitoneOn
  · norm_num [edgeWitness]
  · exact edgeHiReal_antitoneOn_of_coeff_gt_A edgeCoeff_thirteen_gt_A

end N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh
#check @N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh.cosHiReal_le_one
#check @N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh.edgeDecFrom_twelve
#check @N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh.edgeDecFrom_thirteen
#print axioms N11Formalization.SevenClassQ0Deg3EdgeSuffixHigh.edgeDecFrom_twelve
