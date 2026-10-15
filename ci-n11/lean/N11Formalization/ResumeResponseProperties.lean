import N11Formalization.ResumeResponseGram

noncomputable section
namespace N11Formalization.ResumeResponseProperties
open ResumeNetwork ResumeDirichlet ResumeResponseGram FlashLocal

theorem response_symm (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ) (i j : Fin 9) :
    response α K i j = response α K j i := by
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem response_psd (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ)
    (hα : ∀ e, 0 ≤ α e) (W : Fin 9 → Point) : 0 ≤ Eform (response α K) W W := by
  rw [gram_energy]
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (hα e) (sq_nonneg _))

#print axioms response_symm
#print axioms response_psd
end N11Formalization.ResumeResponseProperties
