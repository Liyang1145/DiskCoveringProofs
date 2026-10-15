import N11Formalization.ActualBoundarySwitchMetric

/-! Exact positive switch angle and its boundary area atom.
For genuine metric data b=arctan(chord/offset) lies in(0,pi/2);
radius² sin(2b)/2=chord*offset. Closed zero endpoints are a relaxation,
not a silently imposed degeneracy on the actual cover. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundarySwitchAngles
open ActualBoundarySwitchMetric

theorem sin_two_arctan (x : ℝ) :
    Real.sin (2*Real.arctan x)=2*x/(1+x^2) := by
  rw [Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
  have hs : Real.sqrt (1+x^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : (0 : ℝ)<1+x^2)).ne'
  calc
    2*(x/Real.sqrt (1+x^2))*(1/Real.sqrt (1+x^2)) =
        2*x/(Real.sqrt (1+x^2)^2) := by field_simp <;> ring
    _ = 2*x/(1+x^2) := by rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1+x^2)]

def SwitchData.angle {a b U : Point} {r : ℝ} (S : SwitchData a b U r) : ℝ :=
  Real.arctan (S.chord/S.offset)

theorem SwitchData.angle_bounds {a b U : Point} {r : ℝ} (S : SwitchData a b U r) :
    0 < SwitchData.angle S ∧ SwitchData.angle S < Real.pi/2 := by
  exact ⟨Real.arctan_pos.mpr (div_pos S.chord_pos S.offset_pos),
    Real.arctan_lt_pi_div_two _⟩

theorem SwitchData.exact_area_atom {a b U : Point} {r : ℝ} (S : SwitchData a b U r) :
    S.radius^2*Real.sin (2*SwitchData.angle S)/2=S.chord*S.offset := by
  rw [SwitchData.angle,sin_two_arctan,← S.pythagorean]
  have hoff : S.offset ≠ 0 := S.offset_pos.ne'
  have hd : 1+(S.chord/S.offset)^2 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem actual_switch_angle_and_area {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (i : Fin 9) (U : ActualBoundaryNeighborTies.NeighborTie c r i) :
    ∃ S : SwitchData (c (ActualRingDirectionOrder.ringSite i))
      (c (ActualRingLinkBoundaryData.nextSite i)) (circleMap U.angle) r,
      0 < SwitchData.angle S ∧ SwitchData.angle S < Real.pi/2 ∧
        S.radius^2*Real.sin (2*SwitchData.angle S)/2=S.chord*S.offset := by
  obtain ⟨S⟩ := actual_boundary_switch_metric h hr i U
  exact ⟨S,(SwitchData.angle_bounds S).1,(SwitchData.angle_bounds S).2,
    SwitchData.exact_area_atom S⟩

end N11Formalization.ActualBoundarySwitchAngles
#check @N11Formalization.ActualBoundarySwitchAngles.actual_switch_angle_and_area
#print axioms N11Formalization.ActualBoundarySwitchAngles.SwitchData.exact_area_atom
#print axioms N11Formalization.ActualBoundarySwitchAngles.actual_switch_angle_and_area
