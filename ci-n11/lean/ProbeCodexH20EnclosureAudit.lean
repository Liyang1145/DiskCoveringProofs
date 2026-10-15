import N11Formalization
set_option autoImplicit false
open N11Formalization RatInterval
open SourceActiveFiniteSystem SourceH20ResidualProposal SourceH20CertifiedEnclosure
open SourceResponseCertifiedIntervals

#print SourceExactRoot.sourceRadius
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print SourceH20ResidualProposal.coefficientN
#print SourceH20ResidualProposal.projectionN
#print SourceH20ResidualProposal.EL
#print SourceH20ResidualProposal.EH
#print SourceH20CertifiedEnclosure.centre
#print SourceH20CertifiedEnclosure.actualResidual
#print SourceH20CertifiedEnclosure.HBox
#print SourceResponseCertifiedIntervals.responseBox
#print SourceResponseCertifiedIntervals.H0Box
#check @SourceActualContraction.actual_contraction
#check @SourceH20ResidualProposal.all_columns
#check @SourceH20CertifiedEnclosure.actualResidual_bounds
#check @SourceH20CertifiedEnclosure.actualResidual_norm
#check @SourceH20CertifiedEnclosure.H20_error_certified
#check @SourceH20CertifiedEnclosure.H20_coordinate_certified
#check @SourceH20CertifiedEnclosure.HBox_mem
#check @SourceResponseCertifiedIntervals.coefficientBox_mem
#check @SourceResponseCertifiedIntervals.responseBox_mem
#check @SourceResponseCertifiedIntervals.H0Box_mem
#print axioms SourceH20ResidualProposal.all_columns
#print axioms SourceH20CertifiedEnclosure.actualResidual_norm
#print axioms SourceH20CertifiedEnclosure.H20_error_certified
#print axioms SourceH20CertifiedEnclosure.HBox_mem
#print axioms SourceResponseCertifiedIntervals.responseBox_mem
#print axioms SourceResponseCertifiedIntervals.H0Box_mem

example (i : Fin 20) (j : Fin 9) : (HBox i j).Mem (H20 j i) := HBox_mem i j
example (i j : Fin 9) :
    (responseBox i j).Mem (SourceResponseFluxIdentity.sourceResponse i j) :=
  responseBox_mem i j
example (i j : Fin 9) :
    (H0Box i j).Mem (SourceResponseKernelConsumer.H0 i j) := H0Box_mem i j

-- Real hub9/10 and source face auxiliary coordinate consumers, not Fin9 wrap.
example (j : Fin 9) :
    (HBox (Fin.castAdd 9 (9 : Fin 11)) j).Mem
      (SourcePositiveHarmonicConsumer.sourceH (HarmonicSourceTransport.srcNode (.inl 9)) j) := by
  rw [← H20_actual_site]
  exact HBox_mem _ j
example (j : Fin 9) :
    (HBox (Fin.castAdd 9 (10 : Fin 11)) j).Mem
      (SourcePositiveHarmonicConsumer.sourceH (HarmonicSourceTransport.srcNode (.inl 10)) j) := by
  rw [← H20_actual_site]
  exact HBox_mem _ j
example (j f : Fin 9) :
    (HBox (Fin.natAdd 11 f) j).Mem
      (SourcePositiveHarmonicConsumer.sourceH (HarmonicSourceTransport.srcNode (.inr f)) j) := by
  rw [← H20_actual_face]
  exact HBox_mem _ j
example (j : Fin 9) : ‖H20 j-centre j‖ ≤ (3 : ℝ)/980 := H20_error_certified j
