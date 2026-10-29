import N11Formalization.IntervalsHighLag
import N11Formalization.MetricAreaRationalCertificate

/-! Lane A: monotonicity of the factorial Taylor upper sine bracket.

This is the analytic ingredient behind `CapMonotoneOnGrid` in
`SevenClassQ0Deg3Bins`.  The key point is that the derivative of
`x ↦ sinT 14 x + x^29/29!` is `cosT 14 x + x^28/28!`, and this is at least
`cos x` because `|cos x - cosT 14 x| ≤ x^28/28!`.  Hence the bracket is
nondecreasing on `[0, π/2]`, where `cos ≥ 0`. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3Mono

open N11Formalization
open N11Formalization.MetricAreaRationalCertificate

/-- The real factorial Taylor upper bracket, for nonnegative arguments. -/
def sinHiReal (x : ℝ) : ℝ :=
  sinT 14 x + x ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ)

theorem hasDerivAt_sinHiReal (x : ℝ) :
    HasDerivAt sinHiReal (cosT 14 x + x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => sinT 14 y) (cosT 14 x) x := hasDerivAt_sinT 14 x
  have h2 : HasDerivAt (fun y : ℝ => y ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ))
      (29 * x ^ 28 / ((Nat.factorial 29 : ℕ) : ℝ)) x := by
    have h := (hasDerivAt_pow 29 x).div_const ((Nat.factorial 29 : ℕ) : ℝ)
    simpa using h
  refine (h1.add h2).congr_deriv ?_
  have hfac : ((Nat.factorial 29 : ℕ) : ℝ) = 29 * ((Nat.factorial 28 : ℕ) : ℝ) := by
    rw [show (29 : ℕ) = 28 + 1 by norm_num, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac, mul_div_mul_left _ _ (by norm_num : (29 : ℝ) ≠ 0)]

theorem cos_le_deriv_sinHiReal {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    Real.cos x ≤ deriv sinHiReal x := by
  have hb := cos_bound_abs 14 x
  have hlow : Real.cos x - cosT 14 x ≤ |x| ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) :=
    (abs_le.mp hb).2
  rw [abs_of_nonneg hx0] at hlow
  rw [(hasDerivAt_sinHiReal x).deriv]
  have hc : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) hx
  calc
    Real.cos x = Real.cos x - cosT 14 x + cosT 14 x := by ring
    _ ≤ x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) + cosT 14 x :=
      add_le_add_right hlow _
    _ = cosT 14 x + x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by ring

theorem sinHiReal_monotoneOn : MonotoneOn sinHiReal (Set.Icc 0 (Real.pi / 2)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · exact (fun x _ => (hasDerivAt_sinHiReal x).continuousAt.continuousWithinAt)
  · intro x _
    exact (hasDerivAt_sinHiReal x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hneg : -(Real.pi / 2) ≤ x :=
      (neg_nonpos.mpr (by positivity)).trans (le_of_lt hx.1)
    have hc : 0 ≤ Real.cos x :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le hneg (le_of_lt hx.2)
    exact hc.trans (cos_le_deriv_sinHiReal (le_of_lt hx.1) (le_of_lt hx.2))

theorem sinHiNLag_cast (q : ℚ) :
    ((sinHiNLag q : ℚ) : ℝ) = sinT 14 (q : ℝ) + |(q : ℝ)| ^ 29 /
      ((Nat.factorial 29 : ℕ) : ℝ) := by
  simp only [sinHiNLag]
  push_cast
  rw [sinTQ_cast]

/-- Rational monotonicity of `sinHiNLag` on `[0, π/2]`. -/
theorem sinHiNLag_mono {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : (b : ℝ) ≤ Real.pi / 2) : sinHiNLag a ≤ sinHiNLag b := by
  have hR : ((sinHiNLag a : ℚ) : ℝ) ≤ ((sinHiNLag b : ℚ) : ℝ) := by
    rw [sinHiNLag_cast, sinHiNLag_cast]
    have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hmem_a : (a : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨haR, habR.trans hb⟩
    have hmem_b : (b : ℝ) ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨haR.trans habR, hb⟩
    have h := sinHiReal_monotoneOn hmem_a hmem_b habR
    simpa [sinHiReal, abs_of_nonneg haR, abs_of_nonneg (haR.trans habR)] using h
  exact_mod_cast hR

/-- `capQ` is monotone in its argument, provided the upper sine bracket is. -/
theorem capQ_mono {q₁ q₂ : ℚ} (h : sinHiNLag (q₁ / 2) ≤ sinHiNLag (q₂ / 2)) :
    capQ q₁ ≤ capQ q₂ := by
  unfold capQ
  have hm : max (1 / 2 : ℚ) (min 1 (sinHiNLag (q₁ / 2))) ≤
      max (1 / 2 : ℚ) (min 1 (sinHiNLag (q₂ / 2))) :=
    max_le_max le_rfl (min_le_min le_rfl h)
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

end N11Formalization.SevenClassQ0Deg3Mono
#check @N11Formalization.SevenClassQ0Deg3Mono.sinHiNLag_mono
#print axioms N11Formalization.SevenClassQ0Deg3Mono.sinHiReal_monotoneOn
