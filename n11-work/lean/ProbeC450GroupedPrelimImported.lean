import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedPrelimImportedAudit
open C450QuadraticBounds C450GroupedAnalytic C450OuterGeometry
example : C450NormalizedInterface.SegmentNormalized C450SixthAnalytic.sixth :=
  C450SixthSegment.sixth_paid
example : C450SixthSegment.remainingSegs.length = 30 := C450SixthSegment.remaining_count
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
theorem all_real_quadratic (B C lo hi x K : ℝ) (hx : x ∈ Set.Icc lo hi)
    (h0 : quad B C lo ≤ K) (h1 : quad B C hi ≤ K) :
    quad B C x ≤ K := upper hx.1 hx.2 h0 h1
theorem actual_sine_products (p t : ℚ) :
    (p:ℝ)*Real.sin (t:ℝ) ≤ (sineProductUpper p t:ℝ) := sine_product_upper p t
end N11Formalization.C450GroupedPrelimImportedAudit
#check @N11Formalization.C450QuadraticBounds.upper
#check @N11Formalization.C450QuadraticBounds.lower
#check @N11Formalization.C450GroupedAnalytic.arc_mono
#check @N11Formalization.C450GroupedAnalytic.arc_unit_mono
#check @N11Formalization.C450GroupedAnalytic.actual_outer_group
#check @N11Formalization.C450GroupedAnalytic.actual_inner_group
#check @N11Formalization.C450GroupedAnalytic.actual_cos_beta
#check @N11Formalization.C450GroupedAnalytic.actual_pair_bound
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450QuadraticBounds.upper
#print axioms N11Formalization.C450QuadraticBounds.minimum_le
#print axioms N11Formalization.C450QuadraticBounds.lower
#print axioms N11Formalization.C450QuadraticBounds.minimum_cast
#print axioms N11Formalization.C450GroupedAnalytic.arc_mono
#print axioms N11Formalization.C450GroupedAnalytic.arc_unit_mono
#print axioms N11Formalization.C450GroupedAnalytic.scalar_group
#print axioms N11Formalization.C450GroupedAnalytic.actual_outer_group
#print axioms N11Formalization.C450GroupedAnalytic.actual_inner_group
#print axioms N11Formalization.C450GroupedAnalytic.actual_cos_beta
#print axioms N11Formalization.C450GroupedAnalytic.sine_product_upper
#print axioms N11Formalization.C450GroupedAnalytic.actual_pair_bound
#print axioms N11Formalization.C450GroupedPrelimImportedAudit.all_real_quadratic
#print axioms N11Formalization.C450GroupedPrelimImportedAudit.actual_sine_products
