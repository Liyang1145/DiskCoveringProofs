import N11Formalization.ResumeAnchorFlux

noncomputable section
namespace N11Formalization.ResumeAdaptiveBalance
open ResumeNetwork ResumeDirichlet FlashLocal

/-- Each column of N is a genuine zero-force stress on the actual network.
Linear combinations remain balanced; no rounded residual or rank test. -/
theorem Qx_balance (s : Edge → Fin 9 → ℝ) (D : Edge → Point)
    (tang : Fin 9 → Point) (N : Edge → Fin 4 → ℝ) (x : Fin 9 → ℝ) (τ : ℝ)
    (hN : ∀ a v, ∑ e, (N e a * incidence e v) • D e = 0) (v : Free) :
    ∑ e, (Qx s D tang N τ x e * incidence e v) • D e = 0 := by
  have ht : ∀ e, (Qx s D tang N τ x e * incidence e v) • D e =
      ∑ a, (τ * GtX s D tang N x a) • ((N e a * incidence e v) • D e) := by
    intro e
    simp only [Qx, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul, smul_smul]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  simp_rw [ht]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, hN, smul_zero]
  simp

#print axioms Qx_balance
end N11Formalization.ResumeAdaptiveBalance
