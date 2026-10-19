import N11Formalization.ResumeAnchorFlux
import N11Formalization.FlashLocalH0

noncomputable section
namespace N11Formalization.ResumeFluxRemainder
open ResumeNetwork ResumeDirichletShift ResumeAnchorFlux FlashLocal

/-- Cauchy-Schwarz in the Euclidean family norm, not the Pi sup norm. -/
theorem sum_inner_abs_le {ι : Type*} [Fintype ι] (A W : ι → Point) :
    |∑ i, inner ℝ (A i) (W i)| ≤ frob A * frob W := by
  calc
    |∑ i, inner ℝ (A i) (W i)| ≤ ∑ i, |inner ℝ (A i) (W i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖A i‖ * ‖W i‖ := Finset.sum_le_sum (fun i _ => abs_real_inner_le_norm _ _)
    _ ≤ frob A * frob W := by
      simpa [frob] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖A i‖) (fun i => ‖W i‖)

/-- Directional adaptive remainder: a bound on the actual anchor flux yields
loss τ A p q². No assertion that p is O(q²) is made. -/
theorem adaptive_remainder_lower {δ : Edge → ℝ} {U W : Fin 9 → Point}
    {C Z : Fin 11 → Point} {τ A p q : ℝ}
    (ht : 0 ≤ τ) (hA : 0 ≤ A) (hp : 0 ≤ p)
    (hf : frob (flux δ U C Z) ≤ τ*A*p) (hW : frob W ≤ q^2/2) :
    -(τ*A*p*q^2) ≤ 2 * baseCross δ U C Z W := by
  rw [baseCross_eq_flux]
  have hcs := sum_inner_abs_le (flux δ U C Z) W
  have hprod : frob (flux δ U C Z) * frob W ≤ (τ*A*p)*(q^2/2) :=
    mul_le_mul hf hW (Real.sqrt_nonneg _) (by positivity)
  have hab := (abs_le.mp (hcs.trans hprod)).1
  nlinarith

#check @adaptive_remainder_lower
#print axioms adaptive_remainder_lower
end N11Formalization.ResumeFluxRemainder
