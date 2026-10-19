import N11Formalization
#check @N11Formalization.PinTangentGeometry.det_sq_gram
#check @N11Formalization.PinTangentGeometry.pin_normals_independent
#check @N11Formalization.PinCircleDifferential.circle_velocity_row
#check @N11Formalization.PinCircleDifferential.two_pin_curves_derivative_eq
#check @N11Formalization.RootPinNormalConsumer.source_contact_chord_ne
#check @N11Formalization.RootPinNormalConsumer.source_contact_normals_independent
#check @N11Formalization.RootPinDifferentialConsumer.source_curve_legal
#check @N11Formalization.RootPinDifferentialConsumer.source_reflected_curve_derivative_eq
#check @N11Formalization.RootPinCurveSmooth.source_true_pin_velocity
#print axioms N11Formalization.RootPinCurveSmooth.source_true_pin_velocity
#print axioms N11Formalization.RootPinNormalConsumer.source_contact_normals_independent
#print axioms N11Formalization.RootPinDifferentialConsumer.source_curve_legal
#print axioms N11Formalization.RootPinDifferentialConsumer.source_reflected_curve_derivative_eq
namespace PinDifferentialAudit
open N11Formalization PinTangentGeometry
/-- Tangent circles: positive chord alone does not give unique linearized pin velocity. -/
theorem zero_height_negative_control :
    let P : Point := !₂[-1,0]
    let Q : Point := !₂[1,0]
    let U : Point := 0
    let v : Point := 0
    let w : Point := !₂[0,1]
    P ≠ Q ∧ ‖U-P‖=‖U-Q‖ ∧
      inner ℝ (U-P) v = inner ℝ (U-P) w ∧
      inner ℝ (U-Q) v = inner ℝ (U-Q) w ∧ v ≠ w := by
  dsimp
  constructor
  · intro h
    have hh := congrArg (fun p : Point => p 0) h
    norm_num at hh
  constructor
  · simp only [zero_sub, norm_neg]
    have h : (!₂[-1,0] : Point) = -(!₂[1,0] : Point) := by
      ext i; fin_cases i <;> norm_num
    rw [h, norm_neg]
  constructor
  · rw [inner_coords, inner_coords]
    norm_num
  constructor
  · rw [inner_coords, inner_coords]
    norm_num
  · intro h
    have hh := congrArg (fun p : Point => p 1) h
    norm_num at hh
end PinDifferentialAudit
#print axioms PinDifferentialAudit.zero_height_negative_control
