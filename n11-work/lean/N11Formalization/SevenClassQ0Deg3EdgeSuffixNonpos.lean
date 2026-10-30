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

/-- The degree-27 Taylor upper bracket for sine is positive on the narrow arc
from `2` to `3*pi/4`.  This supplies the derivative sign needed to show that
the degree-28 cosine upper bracket decreases on that arc. -/
theorem sinT14_nonneg_of_two_le_of_le_three_pi_div_four {x : ℝ}
    (hx0 : 2 ≤ x) (hx1 : x ≤ 3 * Real.pi / 4) : 0 ≤ sinT 14 x := by
  have hxnonneg : 0 ≤ x := by linarith
  have hsinlow : (2 / 3 : ℝ) ≤ Real.sin x := by
    have hy0 : Real.pi / 4 ≤ Real.pi - x := by linarith
    have hy1 : Real.pi - x ≤ Real.pi / 2 := by
      linarith [Real.pi_lt_four]
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := Real.pi / 4) (y := Real.pi - x)
      (by linarith [Real.pi_pos]) hy1 hy0
    rw [Real.sin_pi_sub, Real.sin_pi_div_four] at hmono
    have hs2 : (2 / 3 : ℝ) ≤ Real.sqrt 2 / 2 := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hs0 := Real.sqrt_nonneg 2
      nlinarith
    exact hs2.trans hmono
  have hx3 : x ≤ 3 := by linarith [Real.pi_lt_four]
  have hpow : x ^ 29 ≤ (3 : ℝ) ^ 29 :=
    pow_le_pow_left₀ hxnonneg hx3 29
  have hrem : x ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤ (1 / 100 : ℝ) := by
    refine (div_le_div_of_nonneg_right hpow (by positivity)).trans ?_
    norm_num [Nat.factorial]
  have h := (abs_le.mp (sin_bound_abs 14 x)).1
  rw [abs_of_nonneg hxnonneg] at h
  linarith

/-- Exact rational endpoint check at grid node 1490. -/
theorem cosHiNLag_nodeQ_1490_le_neg_131_over_200 :
    cosHiNLag (nodeQ RatInterval.piHi 2048 1490) ≤ (-131 / 200 : ℚ) := by
  norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi, Finset.sum_range_succ]

theorem cosHiReal_nodeQ_1490_le_neg_131_over_200 :
    cosHiReal (nodeQ RatInterval.piHi 2048 1490 : ℚ) ≤ (-131 / 200 : ℝ) := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 1490
  have hq0 : (0 : ℚ) ≤ q := by
    unfold q nodeQ
    positivity
  have hcast : ((cosHiNLag q : ℚ) : ℝ) = cosHiReal (q : ℝ) := by
    rw [cosHiNLag_cast, cosHiReal]
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    rw [abs_of_nonneg hq0R]
  have h : cosHiNLag q ≤ (-131 / 200 : ℚ) :=
    cosHiNLag_nodeQ_1490_le_neg_131_over_200
  have hR : ((cosHiNLag q : ℚ) : ℝ) ≤ ((-131 / 200 : ℚ) : ℝ) := by
    exact_mod_cast h
  rw [hcast] at hR
  exact hR

/-- The degree-28 cosine upper bracket is antitone on the narrow arc beginning
at node 1490. -/
theorem cosHiReal_antitoneOn_narrow :
    AntitoneOn cosHiReal
      (Set.Icc (nodeQ RatInterval.piHi 2048 1490 : ℚ) (3 * Real.pi / 4)) := by
  have hs2 : (2 : ℝ) ≤ (nodeQ RatInterval.piHi 2048 1490 : ℚ) := by
    norm_num [nodeQ, RatInterval.piHi]
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_cosHiReal x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_cosHiReal x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosHiReal x).deriv]
    exact neg_nonpos.mpr
      (sinT14_nonneg_of_two_le_of_le_three_pi_div_four
        (hs2.trans hx.1.le) (le_of_lt hx.2))

/-- Narrow-interval cosine-tail estimate used by both negative-coefficient
edges. -/
theorem cosHiReal_le_neg_131_over_200_of_narrow {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1490 : ℚ) ≤ x)
    (hx1 : x ≤ 3 * Real.pi / 4) : cosHiReal x ≤ (-131 / 200 : ℝ) := by
  have hs_t : (nodeQ RatInterval.piHi 2048 1490 : ℚ) ≤ 3 * Real.pi / 4 :=
    hx0.trans hx1
  have hanti := cosHiReal_antitoneOn_narrow ⟨le_rfl, hs_t⟩ ⟨hx0, hx1⟩ hx0
  exact hanti.trans cosHiReal_nodeQ_1490_le_neg_131_over_200

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
