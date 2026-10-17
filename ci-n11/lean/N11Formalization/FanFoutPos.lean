import Mathlib
import N11Formalization.SourceExactRoot
import N11Formalization.NondegProof
set_option autoImplicit false
namespace N11Formalization.FanFoutPos
noncomputable section

/-- Exact rational bounds reuse the already kernel-bound literal identities. -/
theorem hub0_box : -(3 / 10 : ℝ) ≤ (boxLoCert 4 : ℝ) ∧
    (boxHiCert 4 : ℝ) ≤ 3 / 10 := by
  rw [ndBoxLo_4, ndBoxHi_4]
  norm_num

theorem hub1_box : -(3 / 10 : ℝ) ≤ (boxLoCert 5 : ℝ) ∧
    (boxHiCert 5 : ℝ) ≤ 3 / 10 := by
  rw [ndBoxLo_5, ndBoxHi_5]
  norm_num

theorem radius_box : (0 : ℝ) < (boxLoCert 6 : ℝ) ∧
    (boxHiCert 6 : ℝ) < 2 / 5 := by
  rw [ndBoxLo_6, ndBoxHi_6]
  norm_num

theorem norm_two (a b : ℝ) : ‖(!₂[a,b] : Point)‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

theorem norm_arcEnd (u : Fin 12 → ℝ) (k : Fin 9) : ‖arcEnd u k‖ = 1 := by
  rw [arcEnd, norm_two, Real.cos_sq_add_sin_sq, Real.sqrt_one]

theorem norm_hub0 (u : Fin 12 → ℝ) : ‖hub0 u‖ = |u 4| := by
  rw [hub0, norm_two]
  simp [Real.sqrt_sq_eq_abs]

theorem norm_hub1 (u : Fin 12 → ℝ) : ‖hub1 u‖ = |u 5| := by
  rw [hub1, norm_two]
  simp [Real.sqrt_sq_eq_abs]

theorem hub_norm_le (u : Fin 12 → ℝ) (hu : SourceExactRoot.RootPredicate u)
    {Hub : Point} (hHub : Hub = hub0 u ∨ Hub = hub1 u) : ‖Hub‖ ≤ 3 / 10 := by
  rcases hHub with rfl | rfl
  · rw [norm_hub0, abs_le]
    exact ⟨hub0_box.1.trans (hu.1 4).1, (hu.1 4).2.trans hub0_box.2⟩
  · rw [norm_hub1, abs_le]
    exact ⟨hub1_box.1.trans (hu.1 5).1, (hu.1 5).2.trans hub1_box.2⟩

theorem radius_sq_lt (u : Fin 12 → ℝ) (hu : SourceExactRoot.RootPredicate u) :
    (u 6) ^ 2 < 4 / 25 := by
  have h0 : 0 < u 6 := lt_of_lt_of_le radius_box.1 (hu.1 6).1
  have h1 : u 6 < 2 / 5 := lt_of_le_of_lt (hu.1 6).2 radius_box.2
  nlinarith

theorem dist_hub_arcEnd_ge (u : Fin 12 → ℝ) (hu : SourceExactRoot.RootPredicate u)
    (k : Fin 9) {Hub : Point} (hHub : Hub = hub0 u ∨ Hub = hub1 u) :
    (7 / 10 : ℝ) ≤ ‖Hub - arcEnd u k‖ := by
  have hh := hub_norm_le u hu hHub
  have ht := abs_norm_sub_norm_le Hub (arcEnd u k)
  rw [norm_arcEnd, abs_le] at ht
  linarith [ht.1]

/-- All fan exterior points are on the unit circle; no root contact equation is needed. -/
theorem fan_Fout_pos (u : Fin 12 → ℝ) (hu : SourceExactRoot.RootPredicate u)
    (k : Fin 9) {Hub : Point} (hHub : Hub = hub0 u ∨ Hub = hub1 u) :
    0 < ‖Hub - arcEnd u k‖ ^ 2 - (u 6) ^ 2 := by
  have hge := dist_hub_arcEnd_ge u hu k hHub
  have hr := radius_sq_lt u hu
  nlinarith

theorem fan_Fout_pos_root (k : Fin 9) {Hub : Point}
    (hHub : Hub = hub0 SourceExactRoot.sourceRoot ∨ Hub = hub1 SourceExactRoot.sourceRoot) :
    0 < ‖Hub - arcEnd SourceExactRoot.sourceRoot k‖ ^ 2 -
      (SourceExactRoot.sourceRoot 6) ^ 2 :=
  fan_Fout_pos _ SourceExactRoot.sourceRoot_mem k hHub

end
end N11Formalization.FanFoutPos
#print axioms N11Formalization.FanFoutPos.hub0_box
#print axioms N11Formalization.FanFoutPos.hub1_box
#print axioms N11Formalization.FanFoutPos.fan_Fout_pos_root
#check @N11Formalization.FanFoutPos.fan_Fout_pos_root
