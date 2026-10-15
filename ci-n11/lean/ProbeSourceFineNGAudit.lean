import N11Formalization

/-! Imported actual consumers and alternative-representation controls. -/
set_option autoImplicit false
open N11Formalization
#check @SourceFineBPointPacket.pointI_mem
#check @SourceFineNResidualPacket.QN_dep
#check @SourceFineNResidualPacket.QN_free
#check @SourceFineNResidualPacket.force_binding
#check @SourceFineNResidualPacket.all_residuals
#check @SourceFineNEnclosure.actual_entry_bounds
#check @SourceFineNEnclosure.force_identity
#check @SourceFineNEnclosure.correlated_residual
#check @SourceFineNEnclosure.actualResidual_norm
#check @SourceFineNEnclosure.dependentColumn_error
#check @SourceFineNEnclosure.NBox_mem
#check @SourceFineRelativeNIntervals.NB_mem
#check @SourceFineRelativeFluxPacket.FB_mem
#check @SourceFineRelativeFluxPacket.GB_mem
#check @SourceFineRelativeFluxPacket.flux_readout
#check @SourceFineRelativeFluxPacket.G_readout
#print SourceNormalizedKernel.dependentColumn
#print SourceNormalizedKernel.rhs
#print SourceNEnclosure.actualResidual
#print SourceRelativeMetric.sourceN
#print SourceRelativeMetric.R
#check @SourceRelativeFluxGeometry.G_flux
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceFineBPointPacket.pointI_mem
#print axioms SourceFineNEnclosure.force_identity
#print axioms SourceFineNEnclosure.actualResidual_norm
#print axioms SourceFineNEnclosure.dependentColumn_error
#print axioms SourceFineNEnclosure.NBox_mem
#print axioms SourceFineRelativeNIntervals.NB_mem
#print axioms SourceFineRelativeFluxPacket.FB_mem
#print axioms SourceFineRelativeFluxPacket.GB_mem

example (a : Fin 4) : ‖SourceNEnclosure.actualResidual a‖≤(1 : ℝ)/20000 :=
  SourceFineNEnclosure.actualResidual_norm a
example (a : Fin 4) :
    ‖SourceNormalizedKernel.dependentColumn a-SourceNEnclosure.centre a‖≤(1 : ℝ)/19600 :=
  SourceFineNEnclosure.dependentColumn_error a
example (e : Fin 45) (a : Fin 4) :
    (SourceFineRelativeNIntervals.NB e a).Mem (SourceRelativeMetric.sourceN e a) :=
  SourceFineRelativeNIntervals.NB_mem e a
example (k : Fin 9) (a : Fin 4) :
    (SourceFineRelativeFluxPacket.GB k a).Mem
      (SourceRelativeFluxGeometry.G (ResumeLocalIncidence.siteMap k) a) :=
  SourceFineRelativeFluxPacket.GB_mem k a

-- The rational candidate is not the true null stress: its mass defect is2.
example : (∑ e : Fin 45,SourceFineNResidualPacket.QN e 0)=2 := by decide +kernel
example : (1/245 : ℚ)=80*(1/19600) := by norm_num
example : (ResumeLocalIncidence.sourceFaces 0 1).val=9 := by decide
example : (ResumeLocalIncidence.sourceFaces 0 2).val=10 := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment

namespace FineNGControls
/-- Quantified calibration of the published finer G table, no fake norm premise. -/
theorem G_width (k : Fin 9) (a : Fin 4) :
    (SourceFineRelativeFluxPacket.GB k a).hi-
      (SourceFineRelativeFluxPacket.GB k a).lo≤(1449 : ℚ)/1000000000 := by
  fin_cases k <;> fin_cases a <;>
    norm_num [SourceFineRelativeFluxPacket.GB,SourceFineRelativeFluxPacket.GLo,
      SourceFineRelativeFluxPacket.GHi,RatInterval.intv]

theorem G_refines_old (k : Fin 9) (a : Fin 4) :
    RatInterval.Contains (SourceRelativeFluxPacket.GB k a)
      (SourceFineRelativeFluxPacket.GB k a) := by
  fin_cases k <;> fin_cases a <;>
    norm_num [RatInterval.Contains,SourceRelativeFluxPacket.GB,
      SourceFineRelativeFluxPacket.GB,SourceFineRelativeFluxPacket.GLo,
      SourceFineRelativeFluxPacket.GHi,SourceRelativeFluxPacket.GLo,
      SourceRelativeFluxPacket.GHi,RatInterval.intv]
end FineNGControls
#check @FineNGControls.G_width
#check @FineNGControls.G_refines_old
#print axioms FineNGControls.G_width
#print axioms FineNGControls.G_refines_old
