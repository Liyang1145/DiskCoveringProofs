import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedRangesControls
open C450OuterGeometry C450PolynomialRanges C450GroupedGeometry C450GroupedAnalytic

theorem actual_full_cubic (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    P3 x ∈ Set.Icc (-1:ℝ) 1 := by
  have hh := range3 (by norm_num : (-1:ℝ) ≤ -1) (by norm_num : (1:ℝ) ≤ 1) hx.1 hx.2
  norm_num [lower3,upper3] at hh
  exact hh
theorem quadratic_turning_reading :
    lower2 (-1/2) (1/2) = (-1:ℝ) ∧ upper2 (-1/2) (1/2) = (-1/2:ℝ) := by
  norm_num [lower2,upper2,C450QuadraticBounds.vertex,P2]
theorem cubic_turning_reading :
    upper3 (-1) 0 = (1:ℝ) ∧ lower3 0 1 = (-1:ℝ) := by
  norm_num [upper3,lower3,P3]
theorem z_endpoint_lower_rejected :
    ¬min (zOf ((31:ℝ)/50)) (zOf ((69:ℝ)/50)) ≤ zOf 1 := by
  norm_num [zOf]
theorem missing_offset_domain_rejected :
    ¬(12/25:ℝ) ≤ ell (!₂[31/50,0]:Point) (1/5) := by
  have hp : (!₂[31/50,0]:Point)-(!₂[1/5,0]:Point) = (!₂[21/50,0]:Point) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> norm_num
  have hn : ‖(!₂[21/50,0]:Point)‖ = (21/50:ℝ) :=
    norm_pair_zero (by norm_num)
  rw [ell,hp,hn]
  norm_num
theorem zero_denominator_interval_rejected :
    ¬((1:ℚ) < 0 ∨ 0 < (-1:ℚ)) := by norm_num
theorem tangent_cosine_reading :
    innerCos (!₂[19/25,0]:Point) 0 = 1 := by
  have hp : (!₂[0,0]:Point) = 0 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  have hn : ‖(!₂[19/25,0]:Point)‖ = (19/25:ℝ) :=
    norm_pair_zero (by norm_num)
  norm_num [C450GroupedAnalytic.innerCos,hubPt,hp,hn]
theorem actual_ratio_endpoint :
    outerV (!₂[-7/10,0]:Point) = -1 := by
  have hn : ‖(!₂[-7/10,0]:Point)‖ = (7/10:ℝ) := by
    have hh := norm_sq_coord (!₂[-7/10,0]:Point)
    norm_num at hh
    nlinarith [norm_nonneg (!₂[-7/10,0]:Point)]
  unfold outerV
  rw [hn]
  norm_num
end N11Formalization.C450GroupedRangesControls
#print axioms N11Formalization.C450GroupedRangesControls.actual_full_cubic
#print axioms N11Formalization.C450GroupedRangesControls.quadratic_turning_reading
#print axioms N11Formalization.C450GroupedRangesControls.cubic_turning_reading
#print axioms N11Formalization.C450GroupedRangesControls.z_endpoint_lower_rejected
#print axioms N11Formalization.C450GroupedRangesControls.missing_offset_domain_rejected
#print axioms N11Formalization.C450GroupedRangesControls.zero_denominator_interval_rejected
#print axioms N11Formalization.C450GroupedRangesControls.tangent_cosine_reading
#print axioms N11Formalization.C450GroupedRangesControls.actual_ratio_endpoint
