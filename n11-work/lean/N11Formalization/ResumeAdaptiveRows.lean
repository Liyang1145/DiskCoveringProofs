import N11Formalization.ResumeAnchorFlux

noncomputable section
namespace N11Formalization.ResumeAdaptiveRows
open ResumeNetwork ResumeDirichlet FlashLocal

/-- Euclidean finite-row Cauchy-Schwarz, including zero rows. -/
theorem abs_dot_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    |∑ i, u i*v i| ≤ Real.sqrt (∑ i, u i^2) * Real.sqrt (∑ i, v i^2) := by
  calc
    |∑ i, u i*v i| ≤ ∑ i, |u i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |v i| := by simp_rw [abs_mul]
    _ ≤ Real.sqrt (∑ i, u i^2) * Real.sqrt (∑ i, v i^2) := by
      simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |u i|) (fun i => |v i|)

/-- Row certificates imply the actual relative adaptive stress estimate;
no division by a weight, hence zero-weight edges are included. -/
theorem Qx_relative (s : Edge → Fin 9 → ℝ) (D : Edge → Point)
    (tang : Fin 9 → Point) (N : Edge → Fin 4 → ℝ) (x : Fin 9 → ℝ)
    (α : Edge → ℝ) {τ B p : ℝ} (hτ : 0 ≤ τ) (hp : 0 ≤ p)
    (hp2 : p^2 = ∑ a, (GtX s D tang N x a)^2)
    (hrow : ∀ e, Real.sqrt (∑ a, (N e a)^2) ≤ B*α e) :
    ∀ e, |Qx s D tang N τ x e| ≤ (τ*B*p)*α e := by
  intro e
  have hnorm : Real.sqrt (∑ a, (GtX s D tang N x a)^2) = p := by
    rw [← hp2, Real.sqrt_sq hp]
  have hc := abs_dot_le (N e) (GtX s D tang N x)
  rw [hnorm] at hc
  have hr := mul_le_mul_of_nonneg_right (hrow e) hp
  have hh := mul_le_mul_of_nonneg_left (hc.trans hr) hτ
  simpa only [Qx, abs_mul, abs_of_nonneg hτ] using hh.trans_eq (by ring)

/-- A zero-sum column certificate makes every adaptive stress zero-sum. -/
theorem Qx_sum_zero (s : Edge → Fin 9 → ℝ) (D : Edge → Point)
    (tang : Fin 9 → Point) (N : Edge → Fin 4 → ℝ) (x : Fin 9 → ℝ) (τ : ℝ)
    (hN : ∀ a, ∑ e, N e a = 0) : ∑ e, Qx s D tang N τ x e = 0 := by
  simp only [Qx, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hN, zero_mul]
  simp

#print axioms Qx_relative
#print axioms Qx_sum_zero
end N11Formalization.ResumeAdaptiveRows
