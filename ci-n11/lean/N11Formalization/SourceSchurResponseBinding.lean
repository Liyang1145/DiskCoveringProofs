import N11Formalization.SourceHarmonicUniqueness
import N11Formalization.NetworkSchurBinding

/-! Exact Schur/response binding for the ACTUAL canonical stress. The constructed
sourceH supplies the balanced representative; its negative solves the signed
freeBlock equation. Existing algebra then identifies the actual Schur expression
with the actual response Gram matrix, with no inverse/connectivity premise. -/
set_option autoImplicit false
namespace N11Formalization.SourceSchurResponseBinding
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeAnchorFlux
open SourceCentreB2Readout SourcePositiveHarmonicConsumer SourceBoundaryStressPositive
open NetworkSchurBinding LaplacianSchurBridge
noncomputable section

def sourceY : Free → Fin 9 → ℝ := fun v j => -sourceH v j

theorem source_balanced :
    LaplacianSchurBridge.Balanced canonicalStress incidence anchorIncidence sourceH := by
  intro v j
  simpa only [NetworkSchurBinding.coeff_eq] using sourceH_columns v j

theorem sourceY_solve (v : Free) (j : Fin 9) :
    ∑ w : Free,
      LaplacianSchurBridge.freeBlock canonicalStress incidence v w * sourceY w j =
        LaplacianSchurBridge.crossBlock canonicalStress incidence anchorIncidence v j := by
  have hn := (LaplacianSchurBridge.balanced_iff_normal_eq
    canonicalStress incidence anchorIncidence sourceH).mp source_balanced v j
  unfold sourceY
  simp only [mul_neg,Finset.sum_neg_distrib]
  linarith

theorem schur_eq_response (i j : Fin 9) :
    LaplacianSchurBridge.anchorBlock canonicalStress anchorIncidence i j -
      ∑ v : Free,
        LaplacianSchurBridge.crossBlock canonicalStress incidence anchorIncidence v i *
          sourceY v j =
      ResumeResponseGram.response canonicalStress (ResumeHarmonic.coeff sourceH) i j := by
  have h := NetworkSchurBinding.source_schur_gram canonicalStress sourceY
    sourceY_solve i j
  simpa [sourceY,ResumeSchurEnergy.gram,ResumeResponseGram.response,
    ResumeHarmonic.coeff] using h

theorem schur_eq_sourceResponse (i j : Fin 9) :
    LaplacianSchurBridge.anchorBlock canonicalStress anchorIncidence i j -
      ∑ v : Free,
        LaplacianSchurBridge.crossBlock canonicalStress incidence anchorIncidence v i *
          sourceY v j =
      SourceResponseFluxIdentity.sourceResponse i j := by
  exact schur_eq_response i j

end
end N11Formalization.SourceSchurResponseBinding
#check @N11Formalization.SourceSchurResponseBinding.sourceY_solve
#check @N11Formalization.SourceSchurResponseBinding.schur_eq_response
#check @N11Formalization.SourceSchurResponseBinding.schur_eq_sourceResponse
#print axioms N11Formalization.SourceSchurResponseBinding.sourceY_solve
#print axioms N11Formalization.SourceSchurResponseBinding.schur_eq_response
