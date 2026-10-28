import N11Formalization
open N11Formalization
open SourceBoundaryStressPositive SourcePositiveHarmonicConsumer SourceCentreB2Readout
open ResumeNetwork ResumeDirichlet ResumeHarmonic

#print SourceExactRoot.sourceRadius
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print PhysicalBoundaryStationarity.boundaryMultiplier
#print PhysicalBoundaryStationarity.tieWeight
#print SourceBoundaryMultiplierFormula.numerator
#print SourceBoundaryMultiplierIntervals.rounded
#check @SourceBoundaryMultiplierFormula.multiplier_numerator
#check @SourceBoundaryMultiplierIntervals.rounded_contains
#check @SourceBoundaryMultiplierIntervals.numeratorBox_mem
#check @SourceBoundaryStressPositive.boundaryMultiplier_neg
#check @SourceBoundaryStressPositive.tieWeight_pos
#check @SourceBoundaryStressPositive.stress_pos
#check @SourceBoundaryStressPositive.canonical_nonneg
#print SourcePositiveHarmonicConsumer.HarmonicCertificate
#check @SourcePositiveHarmonicConsumer.exists_source_harmonic
#check @SourcePositiveHarmonicConsumer.sourceH_columns
#check @SourcePositiveHarmonicConsumer.sourceH_minimizes
#check @SourcePositiveHarmonicConsumer.sourceH_flux_reproduces
#check @SourcePositiveHarmonicConsumer.source_dirichlet_energy
#check @SourcePositiveHarmonicConsumer.source_harmonic_le_oracle
#check @SourcePositiveHarmonicConsumer.source_response_identity
#print axioms SourceBoundaryMultiplierFormula.multiplier_numerator
#print axioms SourceBoundaryMultiplierIntervals.numeratorBox_mem
#print axioms SourceBoundaryStressPositive.boundaryMultiplier_neg
#print axioms SourceBoundaryStressPositive.stress_pos
#print axioms SourcePositiveHarmonicConsumer.exists_source_harmonic
#print axioms SourcePositiveHarmonicConsumer.source_harmonic_le_oracle
#print axioms SourcePositiveHarmonicConsumer.source_response_identity

example (s : ResumeLocalIncidence.SourceEdge) :
    0<canonicalStress (ResumeLocalIncidence.edgeMap s) := by
  simpa only [canonicalStress,SourceAlphaOf.alphaEdge_edgeMap] using stress_pos s

example : (∀ e : Edge,0≤canonicalStress e) ∧ (∑ e : Edge,canonicalStress e)=1 :=
  ⟨canonical_nonneg,canonical_mass_one⟩

example (W : Fin 9 → Point) (hW : ∀ j,‖W j‖≤1) :
    (∑ e : Edge,canonicalStress e*‖∑ j : Fin 9,coeff sourceH e j • W j‖^2)≤V2 W :=
  source_harmonic_le_oracle W hW

example :
    dirichletEnergy canonicalStress sourceAnchors=
      energy canonicalStress sourceAnchors sourceCenters sourceAux :=
  source_dirichlet_energy

example (w : HarmonicSourceTransport.SrcFree) (c : Fin 2) :
    ∑ e : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot (HarmonicSourceGeometryV2.rowIdx w c)
        (HarmonicSourceTransport.srcFlat e)*SourceSignedStressAssembly.stress e=0 :=
  all_B2_rows w c
