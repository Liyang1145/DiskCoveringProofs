import N11Formalization.TrueCirclePinSmooth

/-! Central contact is treated separately: for independently moving Cartesian
hub centers the same pin construction uses a fixed upward seed; its restriction
to horizontal hubs is exactly the existing centralPin formula. -/
set_option autoImplicit false
namespace N11Formalization.HorizontalTruePin
open N11Formalization TrueCirclePin PinBranchBind PinTangentGeometry
noncomputable section

def up : Point := !₂[0,1]
def horizontal (a : ℝ) : Point := !₂[a,0]

theorem norm_up : ‖up‖ = 1 := by
  have hs := norm_sq_coords up
  have hn := norm_nonneg up
  simp only [up, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow, zero_add] at hs
  change ‖up‖^2 = 1 at hs
  nlinarith

theorem horizontal_normal (a b : ℝ) :
    normal up (horizontal a) (horizontal b) = up := by
  have hi : inner ℝ up (horizontal b - horizontal a) = 0 := by
    rw [inner_coords]
    simp [up, horizontal]
  simp [normal, hi]

theorem horizontal_rad (a b R : ℝ) :
    rad (horizontal a) (horizontal b) R = R^2 - ((b-a)/2)^2 := by
  have hs := norm_sq_coords (horizontal b - horizontal a)
  simp only [PiLp.sub_apply, horizontal, Matrix.cons_val_zero,
    Matrix.cons_val_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hs
  change ‖horizontal b-horizontal a‖^2 = (b-a)^2 at hs
  rw [rad, hs]
  ring

/-- Complete function identity, not merely equality of values/derivatives at the root. -/
theorem horizontal_pin (a b R : ℝ) :
    pin up (horizontal a) (horizontal b) R =
      !₂[(a+b)/2, Real.sqrt (R^2-((b-a)/2)^2)] := by
  rw [pin, horizontal_normal, horizontal_rad, norm_up]
  ext i
  fin_cases i <;> simp [chordMid, horizontal, up, smul_eq_mul] <;> ring

theorem source_hubs_distinct :
    hub0 SourceExactRoot.sourceRoot ≠ hub1 SourceExactRoot.sourceRoot := by
  intro h
  have hx := congrArg (fun p : Point => p 0) h
  change SourceExactRoot.sourceRoot 4 = SourceExactRoot.sourceRoot 5 at hx
  have hlo := (SourceExactRoot.sourceRoot_mem.1 4).1
  have hhi := (SourceExactRoot.sourceRoot_mem.1 5).2
  rw [ndBoxLo_4] at hlo
  rw [ndBoxHi_5] at hhi
  norm_num at hlo hhi
  linarith

theorem source_central_radicand_pos :
    0 < (SourceExactRoot.sourceRoot 6)^2 -
      ((SourceExactRoot.sourceRoot 5-SourceExactRoot.sourceRoot 4)/2)^2 := by
  have hlo := (WpIvBox_mem TCChartStationarityRoot.sourceRoot_mem_ball).1
  have hp : (0 : ℝ) < (WpIvBox.lo : ℝ) := by exact_mod_cast WpIvBox_pos
  exact lt_of_lt_of_le hp hlo

theorem source_central_pin :
    pin up (hub0 SourceExactRoot.sourceRoot) (hub1 SourceExactRoot.sourceRoot)
      (SourceExactRoot.sourceRoot 6) = wPoint SourceExactRoot.sourceRoot :=
  horizontal_pin _ _ _

theorem source_central_smooth :
    ContDiffAt ℝ 1 (TrueCirclePinSmooth.pinData up)
      ![SourceExactRoot.sourceRoot 4, 0,
        SourceExactRoot.sourceRoot 5, 0, SourceExactRoot.sourceRoot 6] := by
  apply TrueCirclePinSmooth.pinData_smooth
  · exact source_hubs_distinct
  · change normal up (horizontal _) (horizontal _) ≠ 0
    rw [horizontal_normal]
    intro h
    have hn := norm_up
    rw [h, norm_zero] at hn
    norm_num at hn
  · change rad (horizontal _) (horizontal _) _ ≠ 0
    rw [horizontal_rad]
    exact ne_of_gt source_central_radicand_pos

end
end N11Formalization.HorizontalTruePin
#check @N11Formalization.HorizontalTruePin.horizontal_pin
#check @N11Formalization.HorizontalTruePin.source_central_smooth
#print axioms N11Formalization.HorizontalTruePin.source_central_smooth
