import N11Formalization
set_option autoImplicit false
open N11Formalization ResumeNetwork ResumeDirichlet ResumeLocalIncidence
open SourceRelativeMetric SourceRelativeNormConsumer SourceRelativeAdaptiveConsumer

#print SourceRelativeMetric.R
#print SourceRelativeMetric.RM
#print SourceRelativeMetric.sourceN
#print SourceRelativeMetric.canonicalN
#print SourceRelativeNormConsumer.canonicalNB
#print SourceRelativeAdaptiveConsumer.delta
#check @SourceRelativeMetric.columnSlot_inverse
#check @SourceRelativeMetric.canonical_mass_zero
#check @SourceRelativeMetric.canonical_force_zero
#check @SourceRelativeNormPacket.NB_contains
#check @SourceRelativeNormPacket.all_rows
#check @SourceRelativeNormConsumer.source_row_bound
#check @SourceRelativeNormConsumer.canonical_row_bound
#check @SourceRelativeNormConsumer.canonicalNB_mem
#check @SourceRelativeAdaptiveConsumer.delta_relative
#check @SourceRelativeAdaptiveConsumer.delta_mass_zero
#check @SourceRelativeAdaptiveConsumer.delta_force_zero
#print axioms SourceRelativeMetric.canonical_force_zero
#print axioms SourceRelativeNormPacket.NB_contains
#print axioms SourceRelativeNormPacket.all_rows
#print axioms SourceRelativeNormConsumer.canonical_row_bound
#print axioms SourceRelativeNormConsumer.canonicalNB_mem
#print axioms SourceRelativeAdaptiveConsumer.delta_relative
#print axioms SourceRelativeAdaptiveConsumer.delta_mass_zero
#print axioms SourceRelativeAdaptiveConsumer.delta_force_zero

example (e : Edge) :
    Real.sqrt (∑ a : Fin 4,(canonicalN e a)^2) ≤
      (99/200 : ℝ)*SourceCentreB2Readout.canonicalStress e :=
  canonical_row_bound e

example (e : Edge) (a : Fin 4) : (canonicalNB e a).Mem (canonicalN e a) :=
  canonicalNB_mem e a

-- All angles, actual Qx, no hrow/hNcol/hNbal assumption.
example (x : Fin 9 → ℝ) (e : Edge) :
    |delta x e| ≤ (1468*(99/200)*(power x))*
      SourceCentreB2Readout.canonicalStress e := delta_relative x e

example (x : Fin 9 → ℝ) :
    ∑ e : Edge, (SourceCentreB2Readout.canonicalStress e+delta x e) = 1 := by
  rw [Finset.sum_add_distrib,SourceCentreB2Readout.canonical_mass_one,
    delta_mass_zero,add_zero]

-- Honest domain of the update's sign: its amplitude gate remains explicit,
-- not claimed to follow from an unproved G/radius bound.
example (x : Fin 9 → ℝ) (hgate : 1468*(99/200)*(power x) < 1) (e : Edge) :
    0 ≤ SourceCentreB2Readout.canonicalStress e+delta x e := by
  have hr := (abs_le.mp (delta_relative x e)).1
  have ha := SourceBoundaryStressPositive.canonical_nonneg e
  have hslack : 0 ≤ (1-1468*(99/200)*(power x))*
      SourceCentreB2Readout.canonicalStress e :=
    mul_nonneg (by linarith) ha
  nlinarith only [hr,hslack]

example (x : Fin 9 → ℝ) (v : Free) :
    ∑ e : Edge, (delta x e*incidence e v) • SourceRelativeAdaptiveConsumer.D e = 0 :=
  delta_force_zero x v

example (q : Fin 3) (a : Fin 4) :
    canonicalN (.inr (5,q)) a = 0 ∧ canonicalN (.inr (7,q)) a = 0 :=
  SourceRelativeMetric.canonical_slack_zero q a

-- Fin11 hub rows and all source face constraints remain unchanged.
example : SourceN2.srcFaceSite2 (SourceN2.faceFlat 0 1) = (9 : Fin 11) := by decide
example : SourceN2.srcFaceSite2 (SourceN2.faceFlat 0 2) = (10 : Fin 11) := by decide

-- Countercheck: an arbitrary basis transform need not preserve the old
-- gain/coercivity. R=0 has zero augmentation on a scalar negative-H example.
example : (-1 : ℝ)+2*734*(0:ℝ)^2 < 9/5000 := by norm_num

example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceExactRoot.source_attainment
