import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedRangesImportedAudit
open C450OuterGeometry C450PolynomialRanges C450GroupedGeometry C450QuadraticBounds

/-- Actual FIRST pilot7 closed geometry packet, not all606/full segment. -/
theorem pilot7_ell (c : Point) (e : ℝ)
    (hr : ‖c‖ ∈ Set.Icc ((31:ℝ)/50) (103/160))
    (he : e ∈ Set.Icc ((1:ℝ)/50) (3/125))
    (hq : c450Cq c e ∈ Set.Icc (-1:ℝ) (-15/16)) :
    ell c e ∈ Set.Icc ((79838867:ℝ)/125000000) (6677500003/10000000000) := by
  apply ell_bounds (eLo := (1:ℝ)/50) (E := (3:ℝ)/125)
    (rLo := (31:ℝ)/50) (rHi := (103:ℝ)/160)
    (qLo := (-1:ℝ)) (qHi := (-15:ℝ)/16)
    (by norm_num) he.1 he.2 (by norm_num) (by norm_num) hr.1 hr.2 hq.1 hq.2
  · norm_num
  · norm_num
  · norm_num [quad]
  · norm_num [quad]
  · norm_num [minimum,vertex,quad]

/-- Actual FIRST max-offset/positive-outer pilot36 packet, not all672. -/
theorem pilot36_ell (c : Point) (e : ℝ)
    (hr : ‖c‖ ∈ Set.Icc ((31:ℝ)/50) (103/160))
    (he : e ∈ Set.Icc ((17:ℝ)/125) (7/50))
    (hq : c450Cq c e ∈ Set.Icc (-1:ℝ) (-15/16)) :
    ell c e ∈ Set.Icc ((745691111:ℝ)/1000000000) (7837500003/10000000000) := by
  apply ell_bounds (eLo := (17:ℝ)/125) (E := (7:ℝ)/50)
    (rLo := (31:ℝ)/50) (rHi := (103:ℝ)/160)
    (qLo := (-1:ℝ)) (qHi := (-15:ℝ)/16)
    (by norm_num) he.1 he.2 (by norm_num) (by norm_num) hr.1 hr.2 hq.1 hq.2
  · norm_num
  · norm_num
  · norm_num [quad]
  · norm_num [quad]
  · norm_num [minimum,vertex,quad]

example : C450NormalizedInterface.SegmentNormalized C450SixthAnalytic.sixth :=
  C450SixthSegment.sixth_paid
example : C450SixthSegment.remainingSegs.length = 30 := C450SixthSegment.remaining_count
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450GroupedRangesImportedAudit
#check @N11Formalization.C450PolynomialRanges.range2
#check @N11Formalization.C450PolynomialRanges.range3
#check @N11Formalization.C450GroupedGeometry.ell_bounds
#check @N11Formalization.C450GroupedGeometry.z_bounds
#check @N11Formalization.C450GroupedGeometry.direction_interval
#check @N11Formalization.C450GroupedGeometry.outer_width_le
#check @N11Formalization.C450GroupedGeometry.inner_width_le
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450PolynomialRanges.range2
#print axioms N11Formalization.C450PolynomialRanges.global3
#print axioms N11Formalization.C450PolynomialRanges.negative_mono3
#print axioms N11Formalization.C450PolynomialRanges.middle_anti3
#print axioms N11Formalization.C450PolynomialRanges.range3_of_checks
#print axioms N11Formalization.C450PolynomialRanges.range3
#print axioms N11Formalization.C450GroupedGeometry.ell_lower_global
#print axioms N11Formalization.C450GroupedGeometry.coordinate_identity
#print axioms N11Formalization.C450GroupedGeometry.ell_bounds
#print axioms N11Formalization.C450GroupedGeometry.z_bounds
#print axioms N11Formalization.C450GroupedGeometry.cosine_beta_bounds
#print axioms N11Formalization.C450GroupedGeometry.direction_interval
#print axioms N11Formalization.C450GroupedGeometry.clipped_direction
#print axioms N11Formalization.C450GroupedGeometry.outer_width_le
#print axioms N11Formalization.C450GroupedGeometry.inner_width_le
#print axioms N11Formalization.C450GroupedRangesImportedAudit.pilot7_ell
#print axioms N11Formalization.C450GroupedRangesImportedAudit.pilot36_ell
