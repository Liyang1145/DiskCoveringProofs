import N11Formalization.SourceSharpEnergyCalibration
import N11Formalization.HarmonicResponseConsumer

/-! Uniqueness of the ACTUAL harmonic representative on carrying edges.
The constructed sourceH is not identified pointwise with source centres or face
auxiliaries; nevertheless any other zero-force configuration with the SAME
nonnegative canonical stress and datum has identical carrying edge vectors,
lengths, flux and weighted energy. This is the precise interface needed before
any Schur/response enclosure, with no connectivity or matrix inverse premise. -/
set_option autoImplicit false
namespace N11Formalization.SourceHarmonicUniqueness
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeAnchorFlux
open SourceCentreB2Readout SourcePositiveHarmonicConsumer SourceRadialFluxConsumer
open SourceBoundaryStressPositive
open HarmonicResponseConsumer
noncomputable section

def harmonicCenters (H : Free → Fin 9 → ℝ) : Fin 11 → Point :=
  fun i => lift H sourceAnchors (.inl ⟨i.val,by omega⟩)

def harmonicFaces (H : Free → Fin 9 → ℝ) : Fin 11 → Point :=
  fun f => lift H sourceAnchors (.inr f)

theorem harmonic_vector_balance (H : Free → Fin 9 → ℝ)
    (hH : ∀ v j, ∑ e : Edge,(canonicalStress e*incidence e v)*coeff H e j=0) :
    ∀ v : Free, ∑ e : Edge,
      (canonicalStress e*incidence e v) •
        ResumeDirichlet.edgeVector sourceAnchors
          (harmonicCenters H) (harmonicFaces H) e=0 := by
  intro v
  exact ResumeHarmonic.balance_of_columns canonicalStress H hH sourceAnchors v

theorem sourceH_edgeVector_eq
    {C Z : Fin 11 → Point}
    (hCZ : ∀ v : Free, ∑ e : Edge,
      (canonicalStress e*incidence e v) •
        ResumeDirichlet.edgeVector sourceAnchors C Z e=0) (e : Edge)
    (he : canonicalStress e≠0) :
    ResumeDirichlet.edgeVector sourceAnchors C Z e=
      ResumeDirichlet.edgeVector sourceAnchors
        (harmonicCenters sourceH) (harmonicFaces sourceH) e := by
  apply (edgeVector_eq_of_balance SourceBoundaryStressPositive.canonical_nonneg hCZ
    (harmonic_vector_balance sourceH sourceH_columns) e)
  exact he

theorem sourceH_edgeLength_eq
    {C Z : Fin 11 → Point}
    (hCZ : ∀ v : Free, ∑ e : Edge,
      (canonicalStress e*incidence e v) •
        ResumeDirichlet.edgeVector sourceAnchors C Z e=0) (e : Edge)
    (he : canonicalStress e≠0) :
    edgeLength sourceAnchors C Z e=
      edgeLength sourceAnchors
        (harmonicCenters sourceH) (harmonicFaces sourceH) e :=
  edgeLength_eq_of_balance SourceBoundaryStressPositive.canonical_nonneg hCZ
    (harmonic_vector_balance sourceH sourceH_columns) e he

theorem sourceH_flux_eq
    {C Z : Fin 11 → Point}
    (hCZ : ∀ v : Free, ∑ e : Edge,
      (canonicalStress e*incidence e v) •
        ResumeDirichlet.edgeVector sourceAnchors C Z e=0) :
    ∀ i, flux canonicalStress sourceAnchors C Z i=
      flux canonicalStress sourceAnchors
        (harmonicCenters sourceH) (harmonicFaces sourceH) i :=
  flux_eq_of_balance SourceBoundaryStressPositive.canonical_nonneg hCZ
    (harmonic_vector_balance sourceH sourceH_columns)

theorem sourceH_energy_eq
    {C Z : Fin 11 → Point}
    (hCZ : ∀ v : Free, ∑ e : Edge,
      (canonicalStress e*incidence e v) •
        ResumeDirichlet.edgeVector sourceAnchors C Z e=0) :
    energy canonicalStress sourceAnchors C Z=
      energy canonicalStress sourceAnchors
        (harmonicCenters sourceH) (harmonicFaces sourceH) :=
  energy_eq_of_balance SourceBoundaryStressPositive.canonical_nonneg hCZ
    (harmonic_vector_balance sourceH sourceH_columns)

theorem any_zero_force_source_energy :
    ∀ {C Z : Fin 11 → Point},
      (∀ v : Free, ∑ e : Edge,
        (canonicalStress e*incidence e v) •
          ResumeDirichlet.edgeVector sourceAnchors C Z e=0) →
      energy canonicalStress sourceAnchors C Z=SourceExactRoot.sourceRadius^2 := by
  intro C Z hCZ
  have hrep := SourcePositiveHarmonicConsumer.sourceH_energy_reproduces
  change energy canonicalStress sourceAnchors
      (harmonicCenters sourceH) (harmonicFaces sourceH)=
    energy canonicalStress sourceAnchors sourceCenters sourceAux at hrep
  exact (sourceH_energy_eq hCZ).trans
    (hrep.trans SourceSharpEnergyCalibration.actual_source_energy)

end
end N11Formalization.SourceHarmonicUniqueness
#check @N11Formalization.SourceHarmonicUniqueness.sourceH_edgeVector_eq
#check @N11Formalization.SourceHarmonicUniqueness.sourceH_flux_eq
#check @N11Formalization.SourceHarmonicUniqueness.sourceH_energy_eq
#check @N11Formalization.SourceHarmonicUniqueness.any_zero_force_source_energy
#print axioms N11Formalization.SourceHarmonicUniqueness.sourceH_edgeVector_eq
#print axioms N11Formalization.SourceHarmonicUniqueness.any_zero_force_source_energy
