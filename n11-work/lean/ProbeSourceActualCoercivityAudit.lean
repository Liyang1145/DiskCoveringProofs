import N11Formalization

/-! Imported actual source consumers, full types/axioms and calibration.
Coercivity is now unconditional on its stated pin domain; hdir remains unpaid. -/
set_option autoImplicit false
open N11Formalization
#check @SourceRawResponseIntervals.rawResponse_two_spokes
#check @SourceRawResponsePacket.RB_mem
#check @SourceRawResponsePacket.HB_mem
#check @StructuredCongruence.pair_bilinear
#check @StructuredCongruence.augmented_structured_entry
#check @SourceStructuredIntervals.structuredBox_mem
#check @SourceStructuredIntervals.coercivity_of_certificate
#check @SourceStructuredCoercivityPacket.T_contains
#check @SourceStructuredCoercivityPacket.Q_contains
#check @SourceStructuredCoercivityPacket.strict_rows
#check @SourceStructuredCoercivityPacket.actual_coercivity
#check @SourceActualCoercivity.canonical_coercivity
#check @SourceActualCoercivity.adaptive_coercivity
#check @SourceActualCoercivity.gain_of_directional
#print SourceStructuredIntervals.actualAugmented
#print SourceStructuredIntervals.rawG
#print SourceRawResponseIntervals.rawH0
#print SourceRelativeMetric.R
#print SourceRelativeAdaptiveConsumer.power
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceRawResponseIntervals.rawResponse_two_spokes
#print axioms SourceRawResponsePacket.HB_mem
#print axioms StructuredCongruence.augmented_structured_entry
#print axioms SourceStructuredIntervals.coercivity_of_certificate
#print axioms SourceStructuredCoercivityPacket.T_contains
#print axioms SourceStructuredCoercivityPacket.Q_contains
#print axioms SourceStructuredCoercivityPacket.strict_rows
#print axioms SourceStructuredCoercivityPacket.actual_coercivity
#print axioms SourceActualCoercivity.canonical_coercivity
#print axioms SourceActualCoercivity.adaptive_coercivity
#print axioms SourceActualCoercivity.gain_of_directional

example (x : Fin 8 → ℝ) :
    (9/5000 : ℝ)*(∑ i : Fin 8,x i^2)≤
      (∑ i : Fin 8,∑ j : Fin 8,SourceRawResponseIntervals.rawH0 i.castSucc j.castSucc*x i*x j)+
        1468*(∑ a : Fin 4,(∑ i : Fin 8,SourceStructuredIntervals.rawG i.castSucc a*x i)^2) :=
  SourceStructuredCoercivityPacket.actual_coercivity x

example (x : Fin 9 → ℝ) (hp : x 6=0) :
    (9/5000 : ℝ)*(∑ j : Fin 9,x j^2)≤
      (∑ i : Fin 9,∑ j : Fin 9,SourceResponseKernelConsumer.H0 i j*x i*x j)+
        1468*(SourceRelativeAdaptiveConsumer.power x)^2 :=
  SourceActualCoercivity.adaptive_coercivity x hp

-- Pin transport is a true relabelling, not an assumed rotation symmetry.
example : ResumeLocalIncidence.siteMap 8=(6 : Fin 9) := by decide
example : ResumeLocalIncidence.siteMap 8≠(8 : Fin 9) := by decide
example : (ResumeLocalIncidence.sourceFaces 0 1).val=9 := by decide
example : (ResumeLocalIncidence.sourceFaces 0 2).val=10 := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment

-- Independent representation calibration of pair bilinear/Gram factors:
-- H0 may have signed off-diagonals; pair identity is algebraic, not H0-PSD.
example : (3 : ℝ)*(2-(-1))*(4-1)=27 := by norm_num
example : (2 : ℝ)*734=1468 := by norm_num
example : (9/5000 : ℚ)>(1/1000 : ℚ) := by norm_num
example : SourceStructuredCoercivityPacket.CN 0 0≠1000000 := by decide +kernel
example : (SourceStructuredCoercivityPacket.TB 0 0).lo<
    (SourceStructuredCoercivityPacket.TB 0 0).hi := by decide +kernel
-- All8 strict rows are paid for the true arithmetic input, not an eigenvalue.
example (i : Fin 8) : (1/2 : ℚ)+
    (∑ j : Fin 8,if j=i then 0 else (SourceStructuredCoercivityPacket.QB i j).abs.hi)≤
      (SourceStructuredCoercivityPacket.QB i i).lo :=
  SourceStructuredCoercivityPacket.strict_rows i
