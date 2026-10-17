import N11Formalization
set_option autoImplicit false
open N11Formalization
#print SourceCentreB2Readout.canonicalStress
#check @SourceCentreCovector.representative_radius_force
#check @SourceSelfFaceSymmetry.beta8_symmetry
#check @SourceFaceForceTransport.totalFaceForce_actual
#check @SourceFaceForceTransport.totalFaceForce_average
#check @SourceTieForceTransport.totalTieForce_average
#check @SourceTotalCentreForce.totalCentreForce_zero
#check @SourceCentreB2Readout.coordinate_velocity_inner
#check @SourceCentreB2Readout.centre_B2_entry
#check @SourceCentreB2Readout.full_centre_B2_rows
#check @SourceCentreB2Readout.all_B2_rows
#check @SourceCentreB2Readout.canonical_source_rows
#check @SourceCentreB2Readout.canonical_free_balance
#check @SourceCentreB2Readout.canonical_mass_one
#check @SourceCentreB2Readout.canonical_slack_zero
#print axioms SourceSelfFaceSymmetry.beta8_symmetry
#print axioms SourceTotalCentreForce.totalCentreForce_zero
#print axioms SourceCentreB2Readout.full_centre_B2_rows
#print axioms SourceCentreB2Readout.all_B2_rows
#print axioms SourceCentreB2Readout.canonical_free_balance
#print axioms SourceCentreB2Readout.canonical_mass_one

example (w : HarmonicSourceTransport.SrcFree) (c : Fin 2) :
    ∑ e : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot (HarmonicSourceGeometryV2.rowIdx w c)
        (HarmonicSourceTransport.srcFlat e)*SourceSignedStressAssembly.stress e=0 :=
  SourceCentreB2Readout.all_B2_rows w c

-- Actual correct hub9/hub10 centre rows, not legacy Fin9 wrap-around rows.
example (c : Fin 2) :
    ∑ e : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot (⟨18+c.val,by omega⟩ : Fin 41)
        (HarmonicSourceTransport.srcFlat e)*SourceSignedStressAssembly.stress e=0 :=
  SourceCentreB2Readout.full_centre_B2_rows 9 c
example (c : Fin 2) :
    ∑ e : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot (⟨20+c.val,by omega⟩ : Fin 41)
        (HarmonicSourceTransport.srcFlat e)*SourceSignedStressAssembly.stress e=0 :=
  SourceCentreB2Readout.full_centre_B2_rows 10 c

example (v : ResumeDirichlet.Free) :
    ∑ e : ResumeNetwork.Edge,
      (SourceCentreB2Readout.canonicalStress e*ResumeDirichlet.incidence e v) •
        ResumeDirichlet.edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
          (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
          (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e=0 :=
  SourceCentreB2Readout.canonical_free_balance v

example : ∑ e : ResumeNetwork.Edge,SourceCentreB2Readout.canonicalStress e=1 :=
  SourceCentreB2Readout.canonical_mass_one
-- Sign gap remains explicitly exposed: this equivalence does not pay its RHS.
#check @SourceSignedStressAssembly.stress_positive_iff
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
