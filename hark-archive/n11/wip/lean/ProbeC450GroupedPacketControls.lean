import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedPacketControls
open C450GroupedPacketKernel C450GroupedAmplitude C450GroupedAnalytic C450OuterGeometry

theorem cubic_negative_critical : (range3Q ⟨-1,0⟩).hi = 1 := by decide +kernel
theorem cubic_positive_critical : (range3Q ⟨0,1⟩).lo = -1 := by decide +kernel
theorem quadratic_contained_vertex : (range2Q ⟨-1,1⟩).lo = -1 := by decide +kernel
theorem cubic_endpoint_only_false : ¬ P3 (-1/2:ℝ) ≤ max (P3 (-1:ℝ)) (P3 0) := by
  norm_num [P3]
theorem signed_second_harmonic : (amplitudeInterval 0 (-1) 0 ⟨1,1⟩ ⟨-1,1⟩).hi = 1 := by
  decide +kernel
theorem squareThird_without_nonneg_false :
    ¬ RatInterval.Mem (squareThird ⟨-2,-1⟩) ((4*(-2:ℝ)^2-1)/3) := by
  norm_num [RatInterval.Mem,RatInterval.toSet,squareThird]
theorem negative_sine_uses_lower : sineProductUpper (-1) 1 = -sinLoNLag 1 := by
  norm_num only [sineProductUpper,show ¬ (0:ℚ) ≤ -1 by norm_num,if_false,neg_one_mul]
theorem scalar_upper_cannot_be_omitted : ¬ |(2:ℝ)| ≤ 1 := by norm_num
theorem wrong_capacity_mean :
    RatInterval.piLo*((2:ℚ)+1)/10 ≠ RatInterval.piLo*((2:ℚ)+2)/10 := by
  decide +kernel
end N11Formalization.C450GroupedPacketControls
#print axioms N11Formalization.C450GroupedPacketControls.cubic_negative_critical
#print axioms N11Formalization.C450GroupedPacketControls.cubic_positive_critical
#print axioms N11Formalization.C450GroupedPacketControls.quadratic_contained_vertex
#print axioms N11Formalization.C450GroupedPacketControls.cubic_endpoint_only_false
#print axioms N11Formalization.C450GroupedPacketControls.signed_second_harmonic
#print axioms N11Formalization.C450GroupedPacketControls.squareThird_without_nonneg_false
#print axioms N11Formalization.C450GroupedPacketControls.negative_sine_uses_lower
#print axioms N11Formalization.C450GroupedPacketControls.scalar_upper_cannot_be_omitted
#print axioms N11Formalization.C450GroupedPacketControls.wrong_capacity_mean
