import N11Formalization.SourceSchurResponseBinding
import N11Formalization.FlashLocalFrobeniusLeaf

/-! Actual response positivity/symmetry consumers. These are exact Gram facts
for the SAME canonical stress/sourceH and are useful prerequisites for any
future coercivity certificate. They do not claim strict positivity or mixed
coercivity. -/
set_option autoImplicit false
namespace N11Formalization.SourceResponsePSDConsumer
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic
open SourceCentreB2Readout SourcePositiveHarmonicConsumer SourceResponseFluxIdentity
open SourceRadialFluxConsumer
noncomputable section

def Λ : Fin 9 → Fin 9 → ℝ := sourceResponse

theorem Λ_symm (i j : Fin 9) : Λ i j=Λ j i :=
  ResumeResponseProperties.response_symm canonicalStress (coeff sourceH) i j

theorem Λ_psd (W : Fin 9 → Point) :
    0≤FlashLocal.Eform Λ W W :=
  ResumeResponseProperties.response_psd canonicalStress (coeff sourceH)
    SourceBoundaryStressPositive.canonical_nonneg W

theorem Λ_energy_eq_source (W : Fin 9 → Point) :
    FlashLocal.Eform Λ W W=
      dirichletEnergy canonicalStress W :=
  ResumeHarmonicResponse.response_identity canonicalStress sourceH
    SourceBoundaryStressPositive.canonical_nonneg sourceH_columns W

theorem H0_symm (i j : Fin 9) :
    FlashLocal.H0mat Λ sourceLoad
      (fun i => FlashLocal.circleTangent (sourceAngle i)) i j =
    FlashLocal.H0mat Λ sourceLoad
      (fun i => FlashLocal.circleTangent (sourceAngle i)) j i :=
  FlashLocal.H0mat_symm Λ sourceLoad
    (fun i => FlashLocal.circleTangent (sourceAngle i)) Λ_symm i j

end
end N11Formalization.SourceResponsePSDConsumer
#check @N11Formalization.SourceResponsePSDConsumer.Λ_psd
#check @N11Formalization.SourceResponsePSDConsumer.Λ_energy_eq_source
#check @N11Formalization.SourceResponsePSDConsumer.H0_symm
#print axioms N11Formalization.SourceResponsePSDConsumer.Λ_psd
