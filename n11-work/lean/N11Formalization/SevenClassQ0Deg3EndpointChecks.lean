import N11Formalization.SevenClassQ0Deg3Bins

/-! Lane A: exact rational endpoint checks for the q0 degree-three node table.

Each proof is a denominator-cleared `norm_num` comparison for one endpoint.
Keeping the eight checks separate makes CI failures local to a table entry. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3EndpointChecks

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins

/-- The degree-seven part of the sine Taylor series, kept rational. -/
def sinPoly4 (a : ℚ) : ℚ :=
  a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040

/-- A degree-seven rational lower bound for `sinLoNLag`, with explicit
degree-nine and degree-29 Lagrange remainders.  On `[0,1]` its loss is below
one millionth, unlike the cubic bound at the final endpoint. -/
theorem sinLoNLag_ge_sinPoly4_sub (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    sinPoly4 a - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
        2 / ((Nat.factorial 29 : ℕ) : ℚ) ≤ sinLoNLag a := by
  have h4 := (abs_le.mp (sin_bound_abs 4 (a : ℝ))).1
  have h14 := (abs_le.mp (sin_bound_abs 14 (a : ℝ))).1
  have hS : ((sinLoNLag a : ℚ) : ℝ) =
      sinT 14 (a : ℝ) -
        |(a : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) := by
    simp only [sinLoNLag]
    push_cast
    rw [sinTQ_cast]
  have hpoly : sinT 4 (a : ℝ) =
      (a : ℝ) - (a : ℝ) ^ 3 / 6 + (a : ℝ) ^ 5 / 120 -
        (a : ℝ) ^ 7 / 5040 := by
    norm_num [sinT, Finset.sum_range_succ]
  have habs : |(a : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by exact_mod_cast ha)]
    exact_mod_cast ha1
  have h9 : |(a : ℝ)| ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) ≤
      1 / ((Nat.factorial 9 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) habs) (by norm_num)
  have h29 : |(a : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤
      1 / ((Nat.factorial 29 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) habs) (by norm_num)
  have h4poly : ((a : ℝ) - (a : ℝ) ^ 3 / 6 + (a : ℝ) ^ 5 / 120 -
      (a : ℝ) ^ 7 / 5040) - |(a : ℝ)| ^ 9 /
        ((Nat.factorial 9 : ℕ) : ℝ) ≤ Real.sin (a : ℝ) := by
    rw [← hpoly]
    linarith
  have hmain : (((sinPoly4 a - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
      2 / ((Nat.factorial 29 : ℕ) : ℚ) : ℚ) : ℝ) ≤
      ((sinLoNLag a : ℚ) : ℝ) := by
    rw [hS]
    push_cast [sinPoly4]
    linarith [h4poly, h9, h29, h14]
  exact_mod_cast hmain

/-- Matching rational upper bound for `sinHiNLag` on `[0,1]`. -/
theorem sinHiNLag_le_sinPoly4_add (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    sinHiNLag a ≤ sinPoly4 a + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
      2 / ((Nat.factorial 29 : ℕ) : ℚ) := by
  have h4 := (abs_le.mp (sin_bound_abs 4 (a : ℝ))).2
  have h14 := (abs_le.mp (sin_bound_abs 14 (a : ℝ))).2
  have hS : ((sinHiNLag a : ℚ) : ℝ) =
      sinT 14 (a : ℝ) +
        |(a : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) := by
    simp only [sinHiNLag]
    push_cast
    rw [sinTQ_cast]
  have hpoly : sinT 4 (a : ℝ) =
      (a : ℝ) - (a : ℝ) ^ 3 / 6 + (a : ℝ) ^ 5 / 120 -
        (a : ℝ) ^ 7 / 5040 := by
    norm_num [sinT, Finset.sum_range_succ]
  have habs : |(a : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by exact_mod_cast ha)]
    exact_mod_cast ha1
  have h9 : |(a : ℝ)| ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ) ≤
      1 / ((Nat.factorial 9 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) habs) (by norm_num)
  have h29 : |(a : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤
      1 / ((Nat.factorial 29 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) habs) (by norm_num)
  have h4poly : Real.sin (a : ℝ) ≤
      ((a : ℝ) - (a : ℝ) ^ 3 / 6 + (a : ℝ) ^ 5 / 120 -
        (a : ℝ) ^ 7 / 5040) + |(a : ℝ)| ^ 9 /
          ((Nat.factorial 9 : ℕ) : ℝ) := by
    rw [← hpoly]
    linarith
  have h14poly : sinT 14 (a : ℝ) +
      |(a : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤
      ((a : ℝ) - (a : ℝ) ^ 3 / 6 + (a : ℝ) ^ 5 / 120 -
        (a : ℝ) ^ 7 / 5040) + |(a : ℝ)| ^ 9 /
          ((Nat.factorial 9 : ℕ) : ℝ) +
        2 * (|(a : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ)) := by
    linarith
  have hmain : ((sinHiNLag a : ℚ) : ℝ) ≤
      ((sinPoly4 a + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
        2 / ((Nat.factorial 29 : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [hS]
    push_cast
    linarith [h14poly, h9, h29]
  exact_mod_cast hmain

/-- The real degree-seven polynomial underlying `sinPoly4`. -/
def sinPoly4Real (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040

theorem sinPoly4_cast (a : ℚ) :
    ((sinPoly4 a : ℚ) : ℝ) = sinPoly4Real a := by
  simp only [sinPoly4, sinPoly4Real]
  push_cast
  ring

theorem hasDerivAt_sinPoly4Real (x : ℝ) :
    HasDerivAt sinPoly4Real (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) x := by
  unfold sinPoly4Real
  convert (by fun_prop :
    HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040)
      (1 - 3 * x ^ 2 / 6 + 5 * x ^ 4 / 120 - 7 * x ^ 6 / 5040) x) using 1
  ring

theorem sinPoly4_deriv_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
  have hx2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1 2
  have hx6 : x ^ 6 ≤ 1 := pow_le_one₀ hx0 hx1 6
  have hx4 : 0 ≤ x ^ 4 := by positivity
  nlinarith

theorem sinPoly4Real_monotoneOn : MonotoneOn sinPoly4Real (Set.Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · intro x _
    exact (hasDerivAt_sinPoly4Real x).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_sinPoly4Real x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_sinPoly4Real x).deriv]
    exact sinPoly4_deriv_nonneg (le_of_lt hx.1) (le_of_lt hx.2)

/-- `sinPoly4` is monotone on `[0,1]`; this transfers a low-denominator upper
bound on an endpoint argument to the polynomial cap without a huge expansion. -/
theorem sinPoly4_mono_Icc01 {a b : ℚ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    sinPoly4 a ≤ sinPoly4 b := by
  have hR : ((sinPoly4 a : ℚ) : ℝ) ≤ ((sinPoly4 b : ℚ) : ℝ) := by
    rw [sinPoly4_cast, sinPoly4_cast]
    exact sinPoly4Real_monotoneOn
      ⟨by exact_mod_cast ha0, by exact_mod_cast hab.trans hb1⟩
      ⟨by exact_mod_cast ha0.trans hab, by exact_mod_cast hb1⟩
      (by exact_mod_cast hab)
  exact_mod_cast hR

/-- Endpoint-specific rational cap bound using the degree-seven sine upper
bound.  This retains the small first-bin cap without unfolding `sinTQ 14`. -/
theorem capQ_le_sinPoly4 (q : ℚ) (hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    capQ q ≤ 19 / 50 * max (1 / 2) (min 1
      (sinPoly4 (q / 2) + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
        2 / ((Nat.factorial 29 : ℕ) : ℚ))) := by
  have hx0 : 0 ≤ q / 2 := by linarith
  have hx1 : q / 2 ≤ 1 := by linarith
  have hupper := sinHiNLag_le_sinPoly4_add (q / 2) hx0 hx1
  have hinner : min 1 (sinHiNLag (q / 2)) ≤ min 1
      (sinPoly4 (q / 2) + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
        2 / ((Nat.factorial 29 : ℕ) : ℚ)) :=
    min_le_min_left 1 hupper
  have hmax := max_le_max_left (1 / 2) hinner
  unfold capQ
  exact mul_le_mul_of_nonneg_left hmax (by norm_num)

/-- Transfer the cap bound to a low-denominator upper bound `u` for `q / 2`.
This replaces a degree-29 rational expansion by monotonicity of the degree-seven
polynomial on `[0,1]`. -/
theorem capQ_le_sinPoly4_of_u_le (q u : ℚ) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hu0 : 0 ≤ u) (hqu : q / 2 ≤ u) (hu1 : u ≤ 1) :
    capQ q ≤ 19 / 50 * max (1 / 2) (min 1
      (sinPoly4 u + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
        2 / ((Nat.factorial 29 : ℕ) : ℚ))) := by
  refine (capQ_le_sinPoly4 q hq0 hq2).trans ?_
  have hqhalf0 : 0 ≤ q / 2 := div_nonneg hq0 (by norm_num)
  have hpoly := sinPoly4_mono_Icc01 hqhalf0 hqu hu1
  have hinner := min_le_min_left 1 (add_le_add_right hpoly
    (1 / ((Nat.factorial 9 : ℕ) : ℚ) +
      2 / ((Nat.factorial 29 : ℕ) : ℚ)))
  exact mul_le_mul_of_nonneg_left (max_le_max_left (1 / 2) hinner) (by norm_num)

/-- Coarse low-denominator upper caps for `q / 2`, one per endpoint bin.
Their exact slack is recorded by `audit_endpoint_low_denom.py`. -/
def endpointUBin (j : Fin 8) : ℚ :=
  ![1956 / 10000, 3920 / 10000, 5883 / 10000, 7847 / 10000,
    9810 / 10000, 11774 / 10000, 13737 / 10000, 15708 / 10000] j

theorem endpointUBin_nonneg (j : Fin 8) : 0 ≤ endpointUBin j := by
  fin_cases j <;> norm_num [endpointUBin]

theorem endpointUBin_le_one (j : Fin 8) : endpointUBin j ≤ 1 := by
  fin_cases j <;> norm_num [endpointUBin]

theorem nodeQ_binHi_div_two_le_endpointUBin (j : Fin 8) :
    nodeQ RatInterval.piHi 2048 (binHi j) / 2 ≤ endpointUBin j := by
  fin_cases j <;> norm_num [nodeQ, binHi, endpointUBin, RatInterval.piHi]

theorem nodeQ_binHi_nonneg (j : Fin 8) :
    0 ≤ nodeQ RatInterval.piHi 2048 (binHi j) := by
  fin_cases j <;> norm_num [nodeQ, binHi, RatInterval.piHi]

theorem nodeQ_binHi_le_two (j : Fin 8) :
    nodeQ RatInterval.piHi 2048 (binHi j) ≤ 2 := by
  fin_cases j <;> norm_num [nodeQ, binHi, RatInterval.piHi]

theorem capQ_binHi_le_endpointUBin (j : Fin 8) :
    capQ (nodeQ RatInterval.piHi 2048 (binHi j)) ≤
      19 / 50 * max (1 / 2) (min 1
        (sinPoly4 (endpointUBin j) + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
          2 / ((Nat.factorial 29 : ℕ) : ℚ))) :=
  capQ_le_sinPoly4_of_u_le _ _ (nodeQ_binHi_nonneg j) (nodeQ_binHi_le_two j)
    (endpointUBin_nonneg j) (nodeQ_binHi_div_two_le_endpointUBin j)
    (endpointUBin_le_one j)

/-- Combine the cap upper bound with the polynomial lower bound. -/
theorem endpointCheck_of_quartic (j : Fin 8)
    (h : capQ (nodeQ RatInterval.piHi 2048 (binHi j)) ≤
      sinPoly4 (nodeBinAt j) - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
        2 / ((Nat.factorial 29 : ℕ) : ℚ)) : EndpointCheck j := by
  have hmem := nodeBinAt_mem j
  exact h.trans (sinLoNLag_ge_sinPoly4_sub (nodeBinAt j) hmem.1 hmem.2)

theorem endpointCheck_0 : EndpointCheck 0 := by
  exact endpointCheck_of_quartic 0
    ((capQ_binHi_le_endpointUBin 0).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointCheck_1 : EndpointCheck 1 := by
  exact endpointCheck_of_quartic 1
    ((capQ_binHi_le_endpointUBin 1).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointCheck_2 : EndpointCheck 2 := by
  exact endpointCheck_of_quartic 2
    ((capQ_binHi_le_endpointUBin 2).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointCheck_3 : EndpointCheck 3 := by
  exact endpointCheck_of_quartic 3
    ((capQ_binHi_le_endpointUBin 3).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointCheck_4 : EndpointCheck 4 := by
  exact endpointCheck_of_quartic 4
    ((capQ_binHi_le_endpointUBin 4).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointCheck_5 : EndpointCheck 5 := by
  exact endpointCheck_of_quartic 5
    ((capQ_binHi_le_endpointUBin 5).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointCheck_6 : EndpointCheck 6 := by
  exact endpointCheck_of_quartic 6
    ((capQ_binHi_le_endpointUBin 6).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointCheck_7 : EndpointCheck 7 := by
  exact endpointCheck_of_quartic 7
    ((capQ_binHi_le_endpointUBin 7).trans (by
      norm_num [sinPoly4, endpointUBin, nodeBinAt]))

theorem endpointChecks : ∀ j : Fin 8, EndpointCheck j := by
  intro j
  fin_cases j
  · exact endpointCheck_0
  · exact endpointCheck_1
  · exact endpointCheck_2
  · exact endpointCheck_3
  · exact endpointCheck_4
  · exact endpointCheck_5
  · exact endpointCheck_6
  · exact endpointCheck_7

theorem endpointValid : EndpointValid :=
  endpointValid_of_eight endpointChecks

/-- Every node of the 2048-grid satisfies the degree-three node table. -/
theorem allNodeValid : ∀ k : Fin 2049,
    NodeValid (nodeQ RatInterval.piHi 2048 k) (nodeBin k) :=
  all_node_valid_of_grid_cap capMonotoneOnGrid endpointValid

end N11Formalization.SevenClassQ0Deg3EndpointChecks
#print axioms N11Formalization.SevenClassQ0Deg3EndpointChecks.allNodeValid
