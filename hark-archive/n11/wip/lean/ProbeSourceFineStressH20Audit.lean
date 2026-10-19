import N11Formalization

/-! Real imported consumers and controls. No standalone import shortcuts. -/
set_option autoImplicit false
open N11Formalization

#eval Lean.versionString
#check @SourceFineStressIntervals.stressI_mem
#check @SourceFineCompactStressIntervals.compact_mem
#check @SourceFineCompactStressIntervals.refines_old
#check @SourceFineCompactStressIntervals.width_bound
#check @SourceFineCompactStressIntervals.actual_anchor_diagonal
#check @SourceFineH20ResidualProposal.all_columns
#check @SourceFineH20CertifiedEnclosure.correlated_residual
#check @SourceFineH20CertifiedEnclosure.actualResidual_norm
#check @SourceFineH20CertifiedEnclosure.H20_error_certified
#check @SourceFineH20CertifiedEnclosure.HBox_mem
#check @SourceFineResponseIntervals.jointResponseBox_mem
#check @SourceFineResponseIntervals.response_refines_old
#check @SourceFineResponseIntervals.H0Box_mem
#print SourceH20CertifiedEnclosure.centre
#print SourceH20CertifiedEnclosure.actualResidual
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceFineCompactStressIntervals.compact_mem
#print axioms SourceFineCompactStressIntervals.actual_anchor_diagonal
#print axioms SourceFineH20CertifiedEnclosure.actualResidual_norm
#print axioms SourceFineH20CertifiedEnclosure.H20_error_certified
#print axioms SourceFineH20CertifiedEnclosure.HBox_mem
#print axioms SourceFineResponseIntervals.jointResponseBox_mem
#print axioms SourceFineResponseIntervals.H0Box_mem

example (e : ResumeLocalIncidence.SourceEdge) :
    (SourceFineCompactStressIntervals.compact e).Mem
      (SourceSignedStressAssembly.stress e) :=
  SourceFineCompactStressIntervals.compact_mem e

example (k : Fin 9) :
    SourceSignedStressAssembly.stress (.inl (k,0))+
      SourceSignedStressAssembly.stress (.inl (k,1)) ≤ (2 : ℝ)/25 :=
  SourceFineCompactStressIntervals.actual_anchor_diagonal k

example (j : Fin 9) (i : Fin 11) :
    (SourceFineH20CertifiedEnclosure.HBox (Fin.castAdd 9 i) j).Mem
      (SourcePositiveHarmonicConsumer.sourceH
        (HarmonicSourceTransport.srcNode (.inl i)) j) := by
  rw [← SourceActiveFiniteSystem.H20_actual_site]
  exact SourceFineH20CertifiedEnclosure.HBox_mem _ _

example (j : Fin 9) (f : Fin 9) :
    (SourceFineH20CertifiedEnclosure.HBox (Fin.natAdd 11 f) j).Mem
      (SourcePositiveHarmonicConsumer.sourceH
        (HarmonicSourceTransport.srcNode (.inr f)) j) := by
  rw [← SourceActiveFiniteSystem.H20_actual_face]
  exact SourceFineH20CertifiedEnclosure.HBox_mem _ _

example (i j : Fin 9) :
    (SourceFineResponseIntervals.H0Box i j).Mem (SourceResponseKernelConsumer.H0 i j) :=
  SourceFineResponseIntervals.H0Box_mem i j

example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
example : (3/980 : ℚ)=48*(1/15680) := by norm_num

-- Correct source graph: real hubs9/10 are not Fin9 aliases.
example : (ResumeLocalIncidence.sourceFaces 0 1).val=9 := by decide
example : (ResumeLocalIncidence.sourceFaces 0 2).val=10 := by decide
-- Refinement is not a silent reuse of old rounded stress endpoints.
example : SourceFineCompactStressIntervals.loN 3 ≠
    SourceCompactStressIntervals.loN 3 := by decide
example : (SourceFineCompactStressIntervals.compact (.inl (1,1))).hi-
    (SourceFineCompactStressIntervals.compact (.inl (1,1))).lo=(258 : ℚ)/100000000 := by
  norm_num [SourceFineCompactStressIntervals.compact,
    SourceFineCompactStressIntervals.loN,SourceFineCompactStressIntervals.hiN,
    HarmonicSourceTransport.srcFlat,SourceN2.spokeFlat,RatInterval.intv]
