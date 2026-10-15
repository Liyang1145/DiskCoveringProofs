import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedPrelimControls
open C450QuadraticBounds C450GroupedAnalytic C450OuterGeometry

theorem quadratic_endpoints_positive :
    0 ≤ quad (-1/2) (1/5) 0 ∧ 0 ≤ quad (-1/2) (1/5) 1 := by
  norm_num [quad]
theorem endpoint_only_lower_rejected :
    ¬(∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ quad (-1/2) (1/5) x) := by
  intro hp
  have hh := hp (1/2) ⟨by norm_num,by norm_num⟩
  norm_num [quad] at hh
theorem correct_vertex_lower :
    minimum 0 1 (-1/2) (1/5) = (-1/20:ℝ) := by
  norm_num [minimum,vertex,quad]
theorem cubic_endpoint_max_rejected : ¬P3 (-1/2) ≤ max (P3 (-1)) (P3 0) := by
  norm_num [P3]
theorem cubic_endpoint_min_rejected : ¬min (P3 0) (P3 1) ≤ P3 (1/2) := by
  norm_num [P3]
theorem negative_interval_upper_rejected :
    ¬((-1:ℝ)*Real.sin 0 ≤ (-1)*1) := by norm_num
private theorem sin_one_pos : 0 < Real.sin (1:ℝ) := by
  have hq : (0:ℚ) < sinLoNLag 1 := by decide +kernel
  have hh : 0 < Real.sin ((1:ℚ):ℝ) :=
    ((Rat.cast_pos (K := ℝ)).mpr hq).trans_le (sinLoNLag_le_sin 1)
  simpa only [Rat.cast_one] using hh
theorem missing_scalar_slope_rejected : ¬arc 0 (-1) 0 ≤ arc 0 (-1) 1 := by
  intro hp
  norm_num [arc] at hp
  linarith [sin_one_pos]
theorem missing_unit_angle_rejected : ¬arc 0 1 2 ≤ arc 0 1 3 := by
  have hq : sinHiNLag 3 < sinLoNLag 2 := by decide +kernel
  have hs : Real.sin (3:ℝ) < Real.sin (2:ℝ) :=
    ((sin_le_sinHiNLag 3).trans_lt ((Rat.cast_lt (K := ℝ)).mpr hq)).trans_le
      (sinLoNLag_le_sin 2)
  intro hp
  norm_num [arc] at hp
  linarith
theorem global_amplitude_control :
    arc 2 (-1) (-2) ≤ arc 2 (-1) 5 :=
  arc_mono (by norm_num) (by norm_num)
theorem actual_empty_beta : c450B (!₂[1,0]:Point) 0 = 0 := by
  have hz : (!₂[0,0]:Point) = 0 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  simp only [c450B,hz,sub_zero]
  have hn : ‖(!₂[1,0]:Point)‖ = 1 := by
    simpa using norm_pair_zero (by norm_num : (0:ℝ) ≤ 1)
  rw [hn]
  norm_num
theorem actual_empty_cosine : Real.cos (c450B (!₂[1,0]:Point) 0) = 1 := by
  rw [actual_empty_beta,Real.cos_zero]
theorem actual_zero_centre_definition :
    Real.cos (c450B (0:Point) 0) = innerCos (0:Point) 0 :=
  actual_cos_beta _ _
end N11Formalization.C450GroupedPrelimControls
#print axioms N11Formalization.C450GroupedPrelimControls.quadratic_endpoints_positive
#print axioms N11Formalization.C450GroupedPrelimControls.endpoint_only_lower_rejected
#print axioms N11Formalization.C450GroupedPrelimControls.correct_vertex_lower
#print axioms N11Formalization.C450GroupedPrelimControls.cubic_endpoint_max_rejected
#print axioms N11Formalization.C450GroupedPrelimControls.cubic_endpoint_min_rejected
#print axioms N11Formalization.C450GroupedPrelimControls.negative_interval_upper_rejected
#print axioms N11Formalization.C450GroupedPrelimControls.missing_scalar_slope_rejected
#print axioms N11Formalization.C450GroupedPrelimControls.missing_unit_angle_rejected
#print axioms N11Formalization.C450GroupedPrelimControls.global_amplitude_control
#print axioms N11Formalization.C450GroupedPrelimControls.actual_empty_cosine
#print axioms N11Formalization.C450GroupedPrelimControls.actual_zero_centre_definition
