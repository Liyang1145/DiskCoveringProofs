import N11Formalization.LaplacianSchurBridge
import N11Formalization.ResumeSchurEnergy
import N11Formalization.ResumeAnchorFlux

noncomputable section
namespace N11Formalization.NetworkSchurBinding
open ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeAnchorFlux

/-- Bind both signed incidences to the existing geometric coefficient, not a new convention. -/
theorem coeff_eq (H : Free → Fin 9 → ℝ) (e : Edge) (j : Fin 9) :
    LaplacianSchurBridge.edgeCoeff incidence anchorIncidence H e j = coeff H e j := by
  rcases e with ⟨i, side⟩ | ⟨f, k⟩
  · simp [LaplacianSchurBridge.edgeCoeff, incidence, anchorIncidence, coeff]
    split <;> rename_i h
    · simp [h.symm]; ring
    · simp [Ne.symm h]
  · simp [LaplacianSchurBridge.edgeCoeff, incidence, anchorIncidence, coeff,
      sub_mul, Finset.sum_sub_distrib]

theorem source_solve_balance (α : Edge → ℝ) (Y : Free → Fin 9 → ℝ)
    (hY : ∀ v j, ∑ w, LaplacianSchurBridge.freeBlock α incidence v w * Y w j =
      LaplacianSchurBridge.crossBlock α incidence anchorIncidence v j) :
    ∀ v j, ∑ e, (α e * incidence e v) * coeff (fun w k => -Y w k) e j = 0 := by
  have h := LaplacianSchurBridge.balanced_neg_of_source_solve α incidence anchorIncidence Y hY
  simpa only [LaplacianSchurBridge.Balanced, coeff_eq] using h

/-- Actual 51-edge Gram equals the signed Schur form on all mixed entries.
The source's 20-free-node reindex is NOT assumed discharged here. -/
theorem source_schur_gram (α : Edge → ℝ) (Y : Free → Fin 9 → ℝ)
    (hY : ∀ v j, ∑ w, LaplacianSchurBridge.freeBlock α incidence v w * Y w j =
      LaplacianSchurBridge.crossBlock α incidence anchorIncidence v j) (i j : Fin 9) :
    LaplacianSchurBridge.anchorBlock α anchorIncidence i j -
      ∑ v, LaplacianSchurBridge.crossBlock α incidence anchorIncidence v i * Y v j =
      ResumeSchurEnergy.gram α (fun v k => -Y v k) i j := by
  simpa only [LaplacianSchurBridge.gram, coeff_eq, ResumeSchurEnergy.gram] using
    LaplacianSchurBridge.source_schur_eq_gram α incidence anchorIncidence Y hY i j

#print source_solve_balance
#print source_schur_gram
#print axioms coeff_eq
#print axioms source_solve_balance
#print axioms source_schur_gram
end N11Formalization.NetworkSchurBinding
