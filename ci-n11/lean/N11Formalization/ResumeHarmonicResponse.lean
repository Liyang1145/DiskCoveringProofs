import N11Formalization.ResumeResponseGram
import N11Formalization.ResumeHarmonic

noncomputable section
namespace N11Formalization.ResumeHarmonicResponse
open ResumeNetwork ResumeDirichlet ResumeResponseGram FlashLocal

/-- Reuse the established actual-network lift and its column balance theorem.
The new conclusion is equality with the minimized energy (not just ≤ oracle). -/
theorem response_identity (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hα : ∀ e, 0 ≤ α e)
    (hc : ∀ v j, ∑ e, (α e * incidence e v) * ResumeHarmonic.coeff H e j = 0)
    (W : Fin 9 → Point) :
    Eform (response α (ResumeHarmonic.coeff H)) W W = dirichletEnergy α W :=
  response_eq_dirichlet α (ResumeHarmonic.coeff H)
    (fun W i => ResumeHarmonic.lift H W (.inl i))
    (fun W f => ResumeHarmonic.lift H W (.inr f)) hα
    (ResumeHarmonic.edge_lift H) (ResumeHarmonic.balance_of_columns α H hc) W

#print axioms response_identity
end N11Formalization.ResumeHarmonicResponse
