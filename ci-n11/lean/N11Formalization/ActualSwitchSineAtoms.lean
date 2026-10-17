import N11Formalization.ActualBoundarySwitchAngles

/-! Exact acute switch trigonometry on the genuine radius/offset data.
These supply the boundary squared-side matching atom, not just its area. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSwitchSineAtoms
open ActualBoundarySwitchMetric ActualBoundarySwitchAngles

theorem SwitchData.ratio_square {a b U : Point} {r : ℝ} (S : SwitchData a b U r) :
    1+(S.chord/S.offset)^2=(S.radius/S.offset)^2 := by
  simp only [div_pow]
  rw [← S.pythagorean]
  field_simp [S.offset_pos.ne']
  <;> ring

theorem SwitchData.sin_angle {a b U : Point} {r : ℝ} (S : SwitchData a b U r) :
    Real.sin (SwitchData.angle S)=S.chord/S.radius := by
  rw [SwitchData.angle,Real.sin_arctan,SwitchData.ratio_square,
    Real.sqrt_sq_eq_abs,abs_of_pos (div_pos S.radius_pos S.offset_pos)]
  field_simp [S.offset_pos.ne',S.radius_pos.ne']

theorem SwitchData.cos_angle {a b U : Point} {r : ℝ} (S : SwitchData a b U r) :
    Real.cos (SwitchData.angle S)=S.offset/S.radius := by
  rw [SwitchData.angle,Real.cos_arctan,SwitchData.ratio_square,
    Real.sqrt_sq_eq_abs,abs_of_pos (div_pos S.radius_pos S.offset_pos)]
  field_simp [S.offset_pos.ne',S.radius_pos.ne']

theorem SwitchData.chord_sine {a b U : Point} {r : ℝ} (S : SwitchData a b U r) :
    S.radius*Real.sin (SwitchData.angle S)=S.chord := by
  rw [SwitchData.sin_angle]
  field_simp [S.radius_pos.ne']

theorem SwitchData.squared_side_atom {a b U : Point} {r : ℝ} (S : SwitchData a b U r) :
    S.radius^2*Real.sin (SwitchData.angle S)^2=halfChord a b^2 := by
  have hs := congrArg (fun t : ℝ => t^2) (SwitchData.chord_sine S)
  rw [mul_pow,S.chord_exact] at hs
  exact hs

end N11Formalization.ActualSwitchSineAtoms
#check @N11Formalization.ActualSwitchSineAtoms.SwitchData.squared_side_atom
#print axioms N11Formalization.ActualSwitchSineAtoms.SwitchData.sin_angle
#print axioms N11Formalization.ActualSwitchSineAtoms.SwitchData.squared_side_atom
