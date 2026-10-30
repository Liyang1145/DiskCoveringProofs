import N11Formalization.SevenClassQ0Deg3Bins

/-! Lane A: exact rational endpoint checks for the q0 degree-three node table.

Each proof is a denominator-cleared `norm_num` comparison for one endpoint.
Keeping the eight checks separate makes CI failures local to a table entry. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3EndpointChecks

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3Mono

/-- The degree-seven part of the sine Taylor series, kept rational. -/
def sinPoly4 (a : ℚ) : ℚ :=
  a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040

/-- A degree-seven rational lower bound for `sinLoNLag`, with explicit
degree-nine and degree-29 Lagrange remainders.  On `[0,1]` its loss is below
one millionth, unlike the cubic bound at the final endpoint. -/
theorem sinTaylorPair_le {a : ℚ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    a ^ (n + 2) / ((Nat.factorial (n + 2) : ℕ) : ℚ) ≤
      a ^ n / ((Nat.factorial n : ℕ) : ℚ) := by
  have hpow : a ^ (n + 2) ≤ a ^ n :=
    pow_le_pow_of_le_one ha0 ha1 (by omega)
  calc
    a ^ (n + 2) / ((Nat.factorial (n + 2) : ℕ) : ℚ) ≤
        a ^ n / ((Nat.factorial (n + 2) : ℕ) : ℚ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ a ^ n / ((Nat.factorial n : ℕ) : ℚ) := by
      exact div_le_div_of_nonneg_left (pow_nonneg ha0 n) (by positivity)
        (by exact_mod_cast Nat.factorial_le (by omega))

theorem sinPoly4_le_sinTQ14 (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    sinPoly4 a ≤ sinTQ 14 a := by
  have h9 := sinTaylorPair_le ha0 ha1 9
  have h13 := sinTaylorPair_le ha0 ha1 13
  have h17 := sinTaylorPair_le ha0 ha1 17
  have h21 := sinTaylorPair_le ha0 ha1 21
  have h25 := sinTaylorPair_le ha0 ha1 25
  norm_num [sinPoly4, sinTQ, Finset.sum_range_succ]
  linarith

theorem sinLoNLag_ge_sinPoly4_sub (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    sinPoly4 a - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
        2 / ((Nat.factorial 29 : ℕ) : ℚ) ≤ sinLoNLag a := by
  have hpoly := sinPoly4_le_sinTQ14 a ha ha1
  have hrem : 0 ≤ |a| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ) := by positivity
  have habs : |a| ≤ 1 := by
    rw [abs_of_nonneg ha]
    exact ha1
  have h29 : |a| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ) ≤
      1 / ((Nat.factorial 29 : ℕ) : ℚ) :=
    div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) habs) (by positivity)
  have hmain : sinPoly4 a - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
      2 / ((Nat.factorial 29 : ℕ) : ℚ) ≤
      sinTQ 14 a - |a| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ) := by
    linarith
  simpa [sinLoNLag] using hmain

/-- Matching rational upper bound for `sinHiNLag` on `[0,1]`. -/
theorem sinHiNLag_le_sinPoly4_add (a : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    sinHiNLag a ≤ sinPoly4 a + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
      2 / ((Nat.factorial 29 : ℕ) : ℚ) := by
  have h4 := (abs_le.mp (sin_bound_abs 4 (a : ℝ))).2
  have h14 := (abs_le.mp (sin_bound_abs 14 (a : ℝ))).1
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
    ring
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
    unfold sinPoly4
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
  have h1 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6) (1 - 3 * x ^ 2 / 6) x :=
    (hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)
  have h2 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 120)
      (1 - 3 * x ^ 2 / 6 + 5 * x ^ 4 / 120) x :=
    h1.add ((hasDerivAt_pow 5 x).div_const 120)
  have h3 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040)
      (1 - 3 * x ^ 2 / 6 + 5 * x ^ 4 / 120 - 7 * x ^ 6 / 5040) x :=
    h2.sub ((hasDerivAt_pow 7 x).div_const 5040)
  unfold sinPoly4Real
  convert h3 using 1
  ring

theorem sinPoly4_deriv_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
  have hx2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
  have hx6 : x ^ 6 ≤ 1 := pow_le_one₀ hx0 hx1
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
  have hinner' : min 1 (sinPoly4 (q / 2) + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
      2 / ((Nat.factorial 29 : ℕ) : ℚ)) ≤
      min 1 (sinPoly4 u + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
        2 / ((Nat.factorial 29 : ℕ) : ℚ)) := by
    simpa [add_comm, add_left_comm, add_assoc] using hinner
  exact mul_le_mul_of_nonneg_left (max_le_max_left (1 / 2) hinner') (by norm_num)

/-- Coarse low-denominator upper caps for `q / 2`, one per endpoint bin.
Their exact slack is recorded by `audit_endpoint_low_denom.py`. -/
def endpointUBin : Fin 8 → ℚ
  | 0 => 1956 / 10000
  | 1 => 3920 / 10000
  | 2 => 5883 / 10000
  | 3 => 7847 / 10000
  | 4 => 9810 / 10000
  | 5 => 11774 / 10000
  | 6 => 13737 / 10000
  | 7 => 15708 / 10000

/-- The upper endpoint bound with both Taylor remainders kept.  Bins 5 and 6
lie outside the `[0,1]` domain of the monotone degree-seven reduction. -/
def endpointUpperBin (j : Fin 8) : ℚ :=
  sinPoly4 (endpointUBin j) + |endpointUBin j| ^ 9 /
      ((Nat.factorial 9 : ℕ) : ℚ) +
    2 * (|endpointUBin j| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ))

@[simp] theorem nodeBinAt_zero : nodeBinAt 0 = 239 / 1250 := by rfl
@[simp] theorem nodeBinAt_one : nodeBinAt 1 = 239 / 1250 := by rfl
@[simp] theorem nodeBinAt_two : nodeBinAt 2 = 133 / 625 := by rfl
@[simp] theorem nodeBinAt_three : nodeBinAt 3 = 2721 / 10000 := by rfl
@[simp] theorem nodeBinAt_four : nodeBinAt 4 = 643 / 2000 := by rfl
@[simp] theorem nodeBinAt_five : nodeBinAt 5 = 897 / 2500 := by rfl
@[simp] theorem nodeBinAt_six : nodeBinAt 6 = 191 / 500 := by rfl
@[simp] theorem nodeBinAt_seven : nodeBinAt 7 = 1949 / 5000 := by rfl

@[simp] theorem endpointUBin_zero : endpointUBin 0 = 1956 / 10000 := by rfl
@[simp] theorem endpointUBin_one : endpointUBin 1 = 3920 / 10000 := by rfl
@[simp] theorem endpointUBin_two : endpointUBin 2 = 5883 / 10000 := by rfl
@[simp] theorem endpointUBin_three : endpointUBin 3 = 7847 / 10000 := by rfl
@[simp] theorem endpointUBin_four : endpointUBin 4 = 9810 / 10000 := by rfl
@[simp] theorem endpointUBin_five : endpointUBin 5 = 11774 / 10000 := by rfl
@[simp] theorem endpointUBin_six : endpointUBin 6 = 13737 / 10000 := by rfl
@[simp] theorem endpointUBin_seven : endpointUBin 7 = 15708 / 10000 := by rfl

theorem capQ_le_mul_of_sinHiNLag_le (q y : ℚ) (hy0 : 1 / 2 ≤ y)
    (hy : sinHiNLag (q / 2) ≤ y) : capQ q ≤ 19 / 50 * y := by
  unfold capQ
  have hm : max (1 / 2 : ℚ) (min 1 (sinHiNLag (q / 2))) ≤ y :=
    max_le hy0 ((min_le_right 1 (sinHiNLag (q / 2))).trans hy)
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

theorem endpointUBin_nonneg (j : Fin 8) : 0 ≤ endpointUBin j := by
  fin_cases j <;> norm_num [endpointUBin]

theorem endpointUBin_le_one_of_lt5 (j : Fin 8) (hj : j.val < 5) :
    endpointUBin j ≤ 1 := by
  fin_cases j
  · norm_num [endpointUBin]
  · norm_num [endpointUBin]
  · norm_num [endpointUBin]
  · norm_num [endpointUBin]
  · norm_num [endpointUBin]
  · omega
  · omega
  · omega

theorem nodeQ_binHi_div_two_le_endpointUBin (j : Fin 8) :
    nodeQ RatInterval.piHi 2048 (binHi j) / 2 ≤ endpointUBin j := by
  fin_cases j <;> norm_num [nodeQ, binHi, endpointUBin, RatInterval.piHi]

theorem nodeQ_binHi_nonneg (j : Fin 8) :
    0 ≤ nodeQ RatInterval.piHi 2048 (binHi j) := by
  fin_cases j <;> norm_num [nodeQ, binHi, RatInterval.piHi]

theorem nodeQ_binHi_le_two_of_lt5 (j : Fin 8) (hj : j.val < 5) :
    nodeQ RatInterval.piHi 2048 (binHi j) ≤ 2 := by
  fin_cases j
  · norm_num [nodeQ, binHi, RatInterval.piHi]
  · norm_num [nodeQ, binHi, RatInterval.piHi]
  · norm_num [nodeQ, binHi, RatInterval.piHi]
  · norm_num [nodeQ, binHi, RatInterval.piHi]
  · norm_num [nodeQ, binHi, RatInterval.piHi]
  · omega
  · omega
  · omega

theorem capQ_binHi_le_endpointUBin_of_lt5 (j : Fin 8) (hj : j.val < 5) :
    capQ (nodeQ RatInterval.piHi 2048 (binHi j)) ≤
      19 / 50 * max (1 / 2) (min 1
        (sinPoly4 (endpointUBin j) + 1 / ((Nat.factorial 9 : ℕ) : ℚ) +
          2 / ((Nat.factorial 29 : ℕ) : ℚ))) :=
  capQ_le_sinPoly4_of_u_le _ _ (nodeQ_binHi_nonneg j)
    (nodeQ_binHi_le_two_of_lt5 j hj)
    (endpointUBin_nonneg j) (nodeQ_binHi_div_two_le_endpointUBin j)
    (endpointUBin_le_one_of_lt5 j hj)

theorem capQ_binHi_le_endpointUpperBin_5 :
    capQ (nodeQ RatInterval.piHi 2048 (binHi 5)) ≤
      19 / 50 * endpointUpperBin 5 := by
  have hx0 : 0 ≤ nodeQ RatInterval.piHi 2048 (binHi 5) / 2 :=
    div_nonneg (nodeQ_binHi_nonneg 5) (by norm_num)
  have hxu := nodeQ_binHi_div_two_le_endpointUBin 5
  have huPi : (endpointUBin 5 : ℝ) ≤ Real.pi / 2 := by
    rw [endpointUBin_five]
    norm_num
    linarith [Real.pi_gt_three]
  have hmono := sinHiNLag_mono hx0 hxu huPi
  have hend : sinHiNLag (endpointUBin 5) ≤ endpointUpperBin 5 := by
    rw [endpointUpperBin, endpointUBin_five]
    norm_num [sinHiNLag, sinTQ, Finset.sum_range_succ, sinPoly4]
  exact capQ_le_mul_of_sinHiNLag_le _ _ (by
    rw [endpointUpperBin, endpointUBin_five]
    norm_num [sinPoly4]) (hmono.trans hend)

theorem capQ_binHi_le_endpointUpperBin_6 :
    capQ (nodeQ RatInterval.piHi 2048 (binHi 6)) ≤
      19 / 50 * endpointUpperBin 6 := by
  have hx0 : 0 ≤ nodeQ RatInterval.piHi 2048 (binHi 6) / 2 :=
    div_nonneg (nodeQ_binHi_nonneg 6) (by norm_num)
  have hxu := nodeQ_binHi_div_two_le_endpointUBin 6
  have huPi : (endpointUBin 6 : ℝ) ≤ Real.pi / 2 := by
    rw [endpointUBin_six]
    norm_num
    linarith [Real.pi_gt_three]
  have hmono := sinHiNLag_mono hx0 hxu huPi
  have hend : sinHiNLag (endpointUBin 6) ≤ endpointUpperBin 6 := by
    rw [endpointUpperBin, endpointUBin_six]
    norm_num [sinHiNLag, sinTQ, Finset.sum_range_succ, sinPoly4]
  exact capQ_le_mul_of_sinHiNLag_le _ _ (by
    rw [endpointUpperBin, endpointUBin_six]
    norm_num [sinPoly4]) (hmono.trans hend)

/-- Combine the cap upper bound with the polynomial lower bound. -/
theorem endpointCheck_of_quartic (j : Fin 8)
    (h : capQ (nodeQ RatInterval.piHi 2048 (binHi j)) ≤
      sinPoly4 (nodeBinAt j) - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
        2 / ((Nat.factorial 29 : ℕ) : ℚ)) : EndpointCheck j := by
  have hmem := nodeBinAt_mem j
  exact h.trans (sinLoNLag_ge_sinPoly4_sub (nodeBinAt j) hmem.1 hmem.2)

theorem endpointCheck_0 : EndpointCheck 0 := by
  exact endpointCheck_of_quartic 0
    ((capQ_binHi_le_endpointUBin_of_lt5 0 (by decide)).trans (by
      rw [endpointUBin_zero, nodeBinAt_zero]
      norm_num [sinPoly4, max_def, min_def]))

theorem endpointCheck_1 : EndpointCheck 1 := by
  exact endpointCheck_of_quartic 1
    ((capQ_binHi_le_endpointUBin_of_lt5 1 (by decide)).trans (by
      rw [endpointUBin_one, nodeBinAt_one]
      norm_num [sinPoly4, max_def, min_def]))

theorem endpointCheck_2 : EndpointCheck 2 := by
  exact endpointCheck_of_quartic 2
    ((capQ_binHi_le_endpointUBin_of_lt5 2 (by decide)).trans (by
      rw [endpointUBin_two, nodeBinAt_two]
      norm_num [sinPoly4, max_def, min_def]))

theorem endpointCheck_3 : EndpointCheck 3 := by
  exact endpointCheck_of_quartic 3
    ((capQ_binHi_le_endpointUBin_of_lt5 3 (by decide)).trans (by
      rw [endpointUBin_three, nodeBinAt_three]
      norm_num [sinPoly4, max_def, min_def]))

theorem endpointCheck_4 : EndpointCheck 4 := by
  exact endpointCheck_of_quartic 4
    ((capQ_binHi_le_endpointUBin_of_lt5 4 (by decide)).trans (by
      rw [endpointUBin_four, nodeBinAt_four]
      norm_num [sinPoly4, max_def, min_def]))

theorem endpointCheck_5 : EndpointCheck 5 := by
  have hpoly :
      (19 / 50 : ℚ) * endpointUpperBin 5 ≤
        sinPoly4 (nodeBinAt 5) - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
          2 / ((Nat.factorial 29 : ℕ) : ℚ) := by
    rw [endpointUpperBin, endpointUBin_five, nodeBinAt_five]
    norm_num [sinPoly4]
  exact (capQ_binHi_le_endpointUpperBin_5).trans (hpoly.trans
    (sinLoNLag_ge_sinPoly4_sub (nodeBinAt 5) (nodeBinAt_mem 5).1
      (nodeBinAt_mem 5).2))

theorem endpointCheck_6 : EndpointCheck 6 := by
  have hpoly :
      (19 / 50 : ℚ) * endpointUpperBin 6 ≤
        sinPoly4 (nodeBinAt 6) - 1 / ((Nat.factorial 9 : ℕ) : ℚ) -
          2 / ((Nat.factorial 29 : ℕ) : ℚ) := by
    rw [endpointUpperBin, endpointUBin_six, nodeBinAt_six]
    norm_num [sinPoly4]
  exact (capQ_binHi_le_endpointUpperBin_6).trans (hpoly.trans
    (sinLoNLag_ge_sinPoly4_sub (nodeBinAt 6) (nodeBinAt_mem 6).1
      (nodeBinAt_mem 6).2))

theorem endpointCheck_7 : EndpointCheck 7 := by
  have hnode : nodeQ RatInterval.piHi 2048 (binHi 7) = RatInterval.piHi := by
    norm_num [nodeQ, binHi]
  have hcap : capQ (nodeQ RatInterval.piHi 2048 (binHi 7)) = 19 / 50 := by
    rw [hnode]
    exact piHiCapSaturated
  unfold EndpointCheck
  rw [hcap]
  exact (by
    rw [nodeBinAt_seven]
    norm_num [sinPoly4] :
      (19 / 50 : ℚ) ≤ sinPoly4 (nodeBinAt 7) -
        1 / ((Nat.factorial 9 : ℕ) : ℚ) -
          2 / ((Nat.factorial 29 : ℕ) : ℚ)).trans
    (sinLoNLag_ge_sinPoly4_sub (nodeBinAt 7) (nodeBinAt_mem 7).1
      (nodeBinAt_mem 7).2)

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
