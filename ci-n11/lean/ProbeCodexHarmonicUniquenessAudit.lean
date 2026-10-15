import N11Formalization
open N11Formalization
open SourceHarmonicUniqueness SourcePositiveHarmonicConsumer
open SourceBoundaryStressPositive ResumeNetwork ResumeDirichlet
open SourceCentreB2Readout

#check @SourceHarmonicUniqueness.harmonic_vector_balance
#check @SourceHarmonicUniqueness.sourceH_edgeVector_eq
#check @SourceHarmonicUniqueness.sourceH_edgeLength_eq
#check @SourceHarmonicUniqueness.sourceH_flux_eq
#check @SourceHarmonicUniqueness.sourceH_energy_eq
#check @SourceHarmonicUniqueness.any_zero_force_source_energy
#print axioms SourceHarmonicUniqueness.sourceH_edgeVector_eq
#print axioms SourceHarmonicUniqueness.sourceH_flux_eq
#print axioms SourceHarmonicUniqueness.any_zero_force_source_energy

example {C Z : Fin 11 → Point}
    (hCZ : ∀ v : Free, ∑ e : Edge,
      (canonicalStress e*incidence e v) •
        edgeVector sourceAnchors C Z e=0) (e : Edge)
    (he : canonicalStress e≠0) :
    edgeVector sourceAnchors C Z e=
      edgeVector sourceAnchors
        (harmonicCenters sourceH) (harmonicFaces sourceH) e :=
  SourceHarmonicUniqueness.sourceH_edgeVector_eq hCZ e he

example {C Z : Fin 11 → Point}
    (hCZ : ∀ v : Free, ∑ e : Edge,
      (canonicalStress e*incidence e v) •
        edgeVector sourceAnchors C Z e=0) :
    energy canonicalStress sourceAnchors C Z=SourceExactRoot.sourceRadius^2 :=
  SourceHarmonicUniqueness.any_zero_force_source_energy hCZ
