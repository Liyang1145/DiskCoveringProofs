import N11Formalization.SevenClassQ0Deg3EdgeReal

/-! Lane A: threshold criterion for decreasing suffixes of negative-coefficient
edges.

When `b < 0`, the edge derivative
`(19/50)^2 * cosHiReal x - b` is negative only where
`cosHiReal x ≤ b / (19/50)^2`; merely knowing `cosHiReal x ≤ 0` is
insufficient.  The latter condition is retained as a useful intermediate
fact, while the antitone wrappers below expose the exact cosine threshold that
the edge-9/10 suffix must establish. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3EdgeSuffixNonpos

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Cos
open SevenClassQ0Deg3EdgeReal
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables

theorem cos_le_neg_half_of_mem_suffix {x : ℝ}
    (hx0 : (2 * Real.pi) / 3 ≤ x) (hx : x ≤ (RatInterval.piHi : ℝ)) :
    Real.cos x ≤ -(1 / 2 : ℝ) := by
  have hpiHi : (RatInterval.piHi : ℝ) < 4 * Real.pi / 3 := by
    have hp3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hhi : (RatInterval.piHi : ℝ) < 4 := by norm_num [RatInterval.piHi]
    linarith
  by_cases hxp : x ≤ Real.pi
  · have h0 : (0 : ℝ) ≤ 2 * Real.pi / 3 := by positivity
    have h := Real.cos_le_cos_of_nonneg_of_le_pi h0 hxp hx0
    have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    rwa [hc] at h
  · have hpi : Real.pi ≤ x := le_of_lt (lt_of_not_ge hxp)
    have hy0 : 0 ≤ x - Real.pi := by linarith
    have hy : x - Real.pi ≤ Real.pi / 3 := by linarith
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hy0
      (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) hy
    have hcy : (1 / 2 : ℝ) ≤ Real.cos (x - Real.pi) := by
      simpa [Real.cos_pi_div_three] using hc
    have hxeq : Real.cos x = -Real.cos (x - Real.pi) := by
      have h := Real.cos_add_pi (x - Real.pi)
      rw [sub_add_cancel] at h
      simpa using h.symm
    linarith

theorem cosHiReal_nonpos_of_mem_suffix {x : ℝ}
    (hx0 : (2 * Real.pi) / 3 ≤ x) (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ 0 := by
  have hxnonneg : 0 ≤ x := by positivity
  have hx4 : x ≤ 4 := hx.trans (by norm_num [RatInterval.piHi])
  have hcos := cos_le_neg_half_of_mem_suffix hx0 hx
  have hb := (abs_le.mp (cos_bound_abs 14 x)).1
  rw [abs_of_nonneg hxnonneg] at hb
  have hct : cosT 14 x ≤ Real.cos x + x ^ 28 /
      ((Nat.factorial 28 : ℕ) : ℝ) := by linarith
  have hpow : x ^ 28 ≤ 4 ^ 28 := pow_le_pow_left₀ hxnonneg hx4 28
  have hsmall : 4 ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) ≤ (1 / 4 : ℝ) := by
    norm_num [Nat.factorial]
  have herr : x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) ≤ (1 / 4 : ℝ) :=
    (div_le_div_of_nonneg_right hpow (by positivity)).trans hsmall
  unfold cosHiReal
  linarith

/-- Above `3*pi/4` the upper cosine bracket is strictly below every negative
coefficient threshold needed by edges 9 and 10.  This is the first (upper-tail)
piece of the split suffix estimate; the narrow interval up to `3*pi/4` still
requires a separate rational Taylor check. -/
theorem cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le {x : ℝ}
    (hx0 : 3 * Real.pi / 4 ≤ x) (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ -(2 / 3 : ℝ) := by
  have hxnonneg : 0 ≤ x := by linarith [Real.pi_pos]
  have hx4 : x ≤ 4 := hx.trans (by norm_num [RatInterval.piHi])
  have hcosReal : Real.cos x ≤ -(2 / 3 : ℝ) + 1 / 100 := by
    by_cases hxp : x ≤ Real.pi
    · have h0 : (0 : ℝ) ≤ 3 * Real.pi / 4 := by positivity
      have h := Real.cos_le_cos_of_nonneg_of_le_pi h0 hxp hx0
      have hc : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
        rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_four]
      rw [hc] at h
      have hs2 : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
        have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
      linarith
    · have hpi : Real.pi ≤ x := le_of_lt (lt_of_not_ge hxp)
      have hy0 : 0 ≤ x - Real.pi := by linarith
      have hy : x - Real.pi ≤ 1 / 7 := by
        have hhi : (RatInterval.piHi : ℝ) ≤ 22 / 7 := by
          norm_num [RatInterval.piHi]
        linarith [Real.pi_gt_three]
      have hlow := Real.one_sub_sq_div_two_le_cos (x := x - Real.pi)
      have hy2 : (x - Real.pi) ^ 2 ≤ (1 / 7 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hy0 hy 2
      have hcosy : (97 / 98 : ℝ) ≤ Real.cos (x - Real.pi) := by
        nlinarith
      have hxeq : Real.cos x = -Real.cos (x - Real.pi) := by
        have h := Real.cos_add_pi (x - Real.pi)
        rw [sub_add_cancel] at h
        simpa using h.symm
      linarith
  have hb := (abs_le.mp (cos_bound_abs 14 x)).1
  rw [abs_of_nonneg hxnonneg] at hb
  have hct : cosT 14 x ≤ Real.cos x + x ^ 28 /
      ((Nat.factorial 28 : ℕ) : ℝ) := by linarith
  have hpow : x ^ 28 ≤ 4 ^ 28 := pow_le_pow_left₀ hxnonneg hx4 28
  have hsmall : 4 ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) ≤ (1 / 100 : ℝ) := by
    norm_num [Nat.factorial]
  have herr : x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) ≤ (1 / 100 : ℝ) :=
    (div_le_div_of_nonneg_right hpow (by positivity)).trans hsmall
  unfold cosHiReal
  linarith

theorem edgeHiReal_deriv_neg_of_cos_le_coeff {b : ℚ} {x : ℝ}
    (hcos : cosHiReal x ≤ (b : ℝ) / (19 / 50 : ℝ) ^ 2) :
    (19 / 50 : ℝ) ^ 2 * cosHiReal x - (b : ℝ) < 0 := by
  have hA : (0 : ℝ) < (19 / 50 : ℝ) ^ 2 := by norm_num
  have hprod : (19 / 50 : ℝ) ^ 2 * cosHiReal x ≤ (b : ℝ) := by
    calc
      (19 / 50 : ℝ) ^ 2 * cosHiReal x ≤
          (19 / 50 : ℝ) ^ 2 * ((b : ℝ) / (19 / 50 : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcos hA.le
      _ = (b : ℝ) := by field_simp [ne_of_gt hA]
  linarith

theorem edgeHiReal_antitoneOn_of_cos_le_coeff {b : ℚ} (s : ℚ)
    (hcos : ∀ x ∈ Set.Ioc (s : ℝ) (RatInterval.piHi : ℝ),
      cosHiReal x ≤ (b : ℝ) / (19 / 50 : ℝ) ^ 2) :
    AntitoneOn (edgeHiReal b) (Set.Icc (s : ℝ) (RatInterval.piHi : ℝ)) := by
  refine edgeHiReal_antitoneOn_of_deriv_nonpos b ?_
  intro x hx
  exact (edgeHiReal_deriv_neg_of_cos_le_coeff (hcos x hx)).le

theorem edgeDecFrom_of_antitoneOn_from (i : Fin 21) (w : Fin 2049)
    (hw : w = edgeWitness i)
    (hanti : AntitoneOn (edgeHiReal (edgeCoeff i))
      (Set.Icc (nodeQ RatInterval.piHi 2048 w) (RatInterval.piHi : ℝ))) :
    EdgeDecFrom i := by
  intro k hk
  have hqk0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 k := by
    unfold nodeQ
    positivity
  have hqw0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 w := by
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
  have hqwhi : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ RatInterval.piHi := by
    unfold nodeQ
    have hwR : (w.val : ℝ) ≤ 2048 := by exact_mod_cast w.isLt
    have hp : (0 : ℝ) ≤ (RatInterval.piHi : ℝ) := by norm_num [RatInterval.piHi]
    have hqR : ((nodeQ RatInterval.piHi 2048 w : ℚ) : ℝ) ≤ (RatInterval.piHi : ℝ) := by
      unfold nodeQ
      push_cast
      nlinarith
    exact_mod_cast hqR
  have hqle : nodeQ RatInterval.piHi 2048 w ≤ nodeQ RatInterval.piHi 2048 k := by
    unfold nodeQ
    have hwk : (w.val : ℚ) ≤ (k.val : ℚ) := by exact_mod_cast hk
    have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwk hp) (by norm_num)
  have hqleR : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ nodeQ RatInterval.piHi 2048 k := hqle
  have hanti' : edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) ≤
      edgeHiReal (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w) := by
    exact hanti ⟨by exact_mod_cast hqw0, by exact_mod_cast hqwhi⟩
      ⟨by exact_mod_cast hqk0, by exact_mod_cast hqkhi⟩ (by exact_mod_cast hqleR)
  have hR : ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) : ℚ) : ℝ) ≤
      ((edgeUpper (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w) : ℚ) : ℝ) := by
    rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 k) hqk0]
    rw [edgeUpper_cast_eq (edgeCoeff i) (nodeQ RatInterval.piHi 2048 w) hqw0]
    exact hanti'
  rw [hw]
  exact_mod_cast hR

theorem edgeCoeff_nine_neg : edgeCoeff 9 < 0 := by
  norm_num [edgeCoeff, tableEdges, mu]

theorem edgeCoeff_ten_neg : edgeCoeff 10 < 0 := by
  norm_num [edgeCoeff, tableEdges, mu]

end N11Formalization.SevenClassQ0Deg3EdgeSuffixNonpos
