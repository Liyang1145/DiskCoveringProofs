import N11Formalization.TrueCirclePinSmooth
import N11Formalization.BoundaryChartLinear
set_option autoImplicit false
namespace N11Formalization.CodexTruePinBranchAudit
open N11Formalization TrueCirclePin TrueCirclePinSmooth PinTangentGeometry PinBranchBind
noncomputable section

/-- Different representation check: reversing the seed reverses the chosen branch. -/
theorem normal_neg_seed (W P Q : Point) :
    normal (-W) P Q = -normal W P Q := by
  simp only [normal, inner_neg_left, neg_div, neg_smul]
  module

theorem pin_neg_seed (W P Q : Point) (R : ℝ) :
    pin (-W) P Q R = (2 : ℝ) • chordMid P Q - pin W P Q R := by
  simp only [pin, normal_neg_seed, norm_neg, smul_neg]
  module

/-- Wrong seed still solves both circles at the actual source, but is NOT the source pin.
Thus equations alone cannot silently pay the source branch/value obligation. -/
theorem opposite_source_branch (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    (‖pinData (-sourceSeed k) (sourceData k) - left (sourceData k)‖^2 =
      (sourceData k 4)^2 ∧
     ‖pinData (-sourceSeed k) (sourceData k) - right (sourceData k)‖^2 =
      (sourceData k 4)^2) ∧
    pinData (-sourceSeed k) (sourceData k) ≠ Uvec SourceExactRoot.sourceRoot k := by
  constructor
  · exact pin_circle_equations _ _ _ _ (by
      simpa only [left_source, right_source] using
        RootPinNormalConsumer.source_contact_chord_ne k hk) (by
      rw [normal_neg_seed]
      exact neg_ne_zero.mpr (source_normal_ne k hk))
      (le_of_lt (source_radicand_pos k hk))
  · have he : pinData (-sourceSeed k) (sourceData k) =
        (2 : ℝ) • chordMid (left (sourceData k)) (right (sourceData k)) -
          Uvec SourceExactRoot.sourceRoot k := by
      unfold pinData
      rw [pin_neg_seed]
      exact congrArg
        (fun p : Point => (2 : ℝ) •
          chordMid (left (sourceData k)) (right (sourceData k)) - p)
        (source_pinData_eq k hk)
    rw [he]
    intro h
    have hm : Uvec SourceExactRoot.sourceRoot k =
        chordMid (left (sourceData k)) (right (sourceData k)) := by
      ext i
      have hi := congrArg (fun p : Point => p i) h
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hi
      linarith
    have hp := RootPinNormalConsumer.source_contact_height k hk
    change 0 < ‖Uvec SourceExactRoot.sourceRoot k -
      chordMid (ringCenter SourceExactRoot.sourceRoot k)
        (ringCenter SourceExactRoot.sourceRoot (k+1))‖ at hp
    simp only [left_source, right_source] at hm
    rw [hm, sub_self, norm_zero] at hp
    exact (lt_irrefl 0) hp

/-- Agreement on the chart does not imply equality in independent coordinates. -/
theorem boundary_kernel_not_full :
    (∀ z : Fin 7 → ℝ, BoundaryChartLinear.boundary (BoundaryChartLinear.chart z) 0 = 0) ∧
    BoundaryChartLinear.boundary (Pi.single 6 1) 0 = 1 := by
  constructor
  · intro z
    rw [BoundaryChartLinear.boundary_chart]
    rfl
  · norm_num [BoundaryChartLinear.boundary, Pi.single_apply, Fin.ext_iff]

end
end N11Formalization.CodexTruePinBranchAudit
#check @N11Formalization.CodexTruePinBranchAudit.opposite_source_branch
#print axioms N11Formalization.CodexTruePinBranchAudit.opposite_source_branch
#print axioms N11Formalization.CodexTruePinBranchAudit.boundary_kernel_not_full
