import N11Formalization
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic
open SourceCentreB2Readout SourcePositiveHarmonicConsumer
open SourceRadialFluxGeometry SourceRadialFluxConsumer SourceResponseFluxIdentity
open SourceSharpEnergyCalibration

#print SourceExactRoot.sourceRadius
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print SourceRadialFluxGeometry.rawLoad
#print SourceRadialFluxConsumer.sourceLoad
#print SourceResponseFluxIdentity.sourceResponse
#print SourceResponseFluxIdentity.sourceAngle
#check @SourceRadialFluxGeometry.source_ring_norm_lt_one
#check @SourceRadialFluxGeometry.source_tangent_rank_all
#check @SourceRadialFluxGeometry.normalCombination_radial
#check @SourceRadialFluxGeometry.radialCoefficient_pos
#check @SourceRadialFluxGeometry.raw_spoke_resultant
#check @SourceRadialFluxConsumer.incidence_source_spoke
#check @SourceRadialFluxConsumer.flux_source_spokes
#check @SourceRadialFluxConsumer.canonical_flux_radial
#check @SourceRadialFluxConsumer.harmonic_flux_radial
#check @SourceRadialFluxConsumer.sourceLoad_pos
#check @SourceResponseFluxIdentity.anchorIncidence_same
#check @SourceResponseFluxIdentity.sourceResponse_rowsum
#check @SourceResponseFluxIdentity.sourceResponse_rowsum_pos
#check @SourceResponseFluxIdentity.actual_hsrc_eq_H0mat
#check @SourceSharpEnergyCalibration.all_face_lengths
#check @SourceSharpEnergyCalibration.carrying_edge_length
#check @SourceSharpEnergyCalibration.actual_source_energy
#check @SourceSharpEnergyCalibration.source_dirichlet_radius_sq
#check @SourceSharpEnergyCalibration.source_oracle_lower
#check @SourceSharpEnergyCalibration.source_oracle_upper
#check @SourceSharpEnergyCalibration.source_oracle_eq
#print axioms SourceRadialFluxGeometry.raw_spoke_resultant
#print axioms SourceRadialFluxGeometry.rawLoad_pos
#print axioms SourceRadialFluxConsumer.canonical_flux_radial
#print axioms SourceRadialFluxConsumer.harmonic_flux_radial
#print axioms SourceResponseFluxIdentity.sourceResponse_rowsum
#print axioms SourceResponseFluxIdentity.actual_hsrc_eq_H0mat
#print axioms SourceSharpEnergyCalibration.actual_source_energy
#print axioms SourceSharpEnergyCalibration.source_oracle_eq

example :
    (∀ j : Fin 9,0<sourceLoad j) ∧
    (∀ j : Fin 9,
      ResumeAnchorFlux.flux canonicalStress sourceAnchors sourceCenters sourceAux j=
        sourceLoad j • sourceAnchors j) :=
  ⟨sourceLoad_pos,canonical_flux_radial⟩

example (j : Fin 9) :
    0 < inner ℝ (sourceAnchors j)
      (ResumeAnchorFlux.flux canonicalStress sourceAnchors sourceCenters sourceAux j) := by
  rw [canonical_flux_radial,real_inner_smul_right,real_inner_self_eq_norm_sq,
    sourceAnchors_unit,one_pow,mul_one]
  exact sourceLoad_pos j

example (j : Fin 9) :
    ∑ k : Fin 9,sourceResponse j k*inner ℝ (sourceAnchors j) (sourceAnchors k)=sourceLoad j :=
  sourceResponse_rowsum j

example :
    FlashResponseHessian.hsrc sourceResponse (fun i => FlashLocal.circleTangent (sourceAngle i))=
      FlashLocal.H0mat sourceResponse sourceLoad (fun i => FlashLocal.circleTangent (sourceAngle i)) :=
  actual_hsrc_eq_H0mat

example : V2 sourceAnchors=SourceExactRoot.sourceRadius^2 := source_oracle_eq
example : energy canonicalStress sourceAnchors sourceCenters sourceAux=SourceExactRoot.sourceRadius^2 :=
  actual_source_energy

-- Scope calibration: the full51 source-datum oracle upper (not a 45-edge
-- feasibility assertion) is the existing attainment/network consumer.
#check @FlashRootNetwork.oracle_le_sq_root
