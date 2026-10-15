import N11Formalization.SourceBoundaryStressPositive
import N11Formalization.ResumeHarmonicResponse

/-! The SAME actual positive normalized source stress consumes ALL40 actual
B2 rows. A harmonic extension is produced, rather than assumed or identified
with the centres. It minimizes for every boundary datum, reproduces the
source flux/energy, and gives the actual all-datum oracle lower-bound consumer.
No unrestricted-cover topology or global sharp conclusion is inferred. -/
set_option autoImplicit false
namespace N11Formalization.SourcePositiveHarmonicConsumer
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeAnchorFlux
open SourceCentreB2Readout SourceBoundaryStressPositive
open FlashRootNetwork LocalSharpAuxZ
noncomputable section

def sourceAnchors : Fin 9 → Point := canonAnchors SourceExactRoot.sourceRoot
def sourceCenters : Fin 11 → Point := canonCenters SourceExactRoot.sourceRoot
def sourceAux : Fin 11 → Point := canonFaceZ SourceExactRoot.sourceRoot

def HarmonicCertificate (H : Free → Fin 9 → ℝ) : Prop :=
  (∀ v j, ∑ e : Edge,(canonicalStress e*incidence e v)*coeff H e j=0) ∧
  (∀ W : Fin 9 → Point,
    energy canonicalStress W (fun i => lift H W (.inl i)) (fun f => lift H W (.inr f))=
      dirichletEnergy canonicalStress W) ∧
  (∀ i : Fin 9,
    flux canonicalStress sourceAnchors
      (fun i => lift H sourceAnchors (.inl i)) (fun f => lift H sourceAnchors (.inr f)) i=
      flux canonicalStress sourceAnchors sourceCenters sourceAux i) ∧
  energy canonicalStress sourceAnchors
    (fun i => lift H sourceAnchors (.inl i)) (fun f => lift H sourceAnchors (.inr f))=
    energy canonicalStress sourceAnchors sourceCenters sourceAux

/-- Genuine actual-root synthesis: no hα/hzero/hrows/H premise remains. -/
theorem exists_source_harmonic : ∃ H : Free → Fin 9 → ℝ,HarmonicCertificate H :=
  HarmonicSourceGeomConsumer.exists_lift_of_source_B2force
    (α := canonicalStress) (u := SourceExactRoot.sourceRoot)
    canonical_nonneg canonical_slack_zero canonical_source_rows

def sourceH : Free → Fin 9 → ℝ := Classical.choose exists_source_harmonic

theorem sourceH_certificate : HarmonicCertificate sourceH :=
  Classical.choose_spec exists_source_harmonic

theorem sourceH_columns (v : Free) (j : Fin 9) :
    ∑ e : Edge,(canonicalStress e*incidence e v)*coeff sourceH e j=0 :=
  sourceH_certificate.1 v j

theorem sourceH_minimizes (W : Fin 9 → Point) :
    energy canonicalStress W
      (fun i => lift sourceH W (.inl i)) (fun f => lift sourceH W (.inr f))=
      dirichletEnergy canonicalStress W :=
  sourceH_certificate.2.1 W

theorem sourceH_flux_reproduces (i : Fin 9) :
    flux canonicalStress sourceAnchors
      (fun i => lift sourceH sourceAnchors (.inl i))
      (fun f => lift sourceH sourceAnchors (.inr f)) i=
      flux canonicalStress sourceAnchors sourceCenters sourceAux i :=
  sourceH_certificate.2.2.1 i

theorem sourceH_energy_reproduces :
    energy canonicalStress sourceAnchors
      (fun i => lift sourceH sourceAnchors (.inl i))
      (fun f => lift sourceH sourceAnchors (.inr f))=
      energy canonicalStress sourceAnchors sourceCenters sourceAux :=
  sourceH_certificate.2.2.2

theorem source_dirichlet_energy :
    dirichletEnergy canonicalStress sourceAnchors=
      energy canonicalStress sourceAnchors sourceCenters sourceAux :=
  (sourceH_minimizes sourceAnchors).symm.trans sourceH_energy_reproduces

/-- Universal datum consumer for the actual normalized stress/H. This pays
harmonic oracle semantics, NOT arbitrary Covers→legal network or sharpness. -/
theorem source_harmonic_le_oracle (W : Fin 9 → Point) (hW : ∀ j,‖W j‖≤1) :
    (∑ e : Edge,canonicalStress e*‖∑ j : Fin 9,coeff sourceH e j • W j‖^2)≤V2 W :=
  harmonic_energy_le_oracle canonicalStress sourceH canonical_nonneg
    canonical_mass_one sourceH_columns W hW

theorem source_response_identity (W : Fin 9 → Point) :
    FlashLocal.Eform (ResumeResponseGram.response canonicalStress (coeff sourceH)) W W=
      dirichletEnergy canonicalStress W :=
  ResumeHarmonicResponse.response_identity canonicalStress sourceH
    canonical_nonneg sourceH_columns W

end
end N11Formalization.SourcePositiveHarmonicConsumer
#check @N11Formalization.SourcePositiveHarmonicConsumer.exists_source_harmonic
#check @N11Formalization.SourcePositiveHarmonicConsumer.source_harmonic_le_oracle
#check @N11Formalization.SourcePositiveHarmonicConsumer.source_response_identity
#print axioms N11Formalization.SourcePositiveHarmonicConsumer.exists_source_harmonic
#print axioms N11Formalization.SourcePositiveHarmonicConsumer.source_harmonic_le_oracle
