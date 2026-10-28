import N11Formalization.ActualSwitchSineAtoms
import N11Formalization.ActualFaceCircumradiusAtoms

/-! The actual switch angle is half the apex angle, not a base angle.
Both real base angles are exactly pi/2 minus the paid switch angle.
This supplies the base-angle term needed by the remaining ring closure.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSwitchBaseAngle

open ActualBoundarySwitchMetric ActualBoundarySwitchAngles ActualSwitchSineAtoms

theorem isosceles_base_cos {a b U : Point} {chord radius : ℝ}
    (hU : dist U a = dist U b) (hchord : dist a b = 2*chord)
    (hradius : dist U a = radius) (hc : 0 < chord) (hr : 0 < radius) :
    Real.cos (EuclideanGeometry.angle b a U) = chord/radius := by
  have hn : ‖b-a‖ = 2*chord := by
    rw [← dist_eq_norm,dist_comm]
    exact hchord
  have hnU : ‖U-a‖ = radius := by
    rw [← dist_eq_norm]
    exact hradius
  have hinner := ActualFaceCircumradiusAtoms.common_circle_projection hU
  rw [real_inner_comm,hn] at hinner
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm (b-a) (U-a)
  change Real.cos (EuclideanGeometry.angle b a U) * (‖b-a‖ * ‖U-a‖) =
    inner ℝ (b-a) (U-a) at hcos
  rw [hn,hnU,hinner] at hcos
  apply (eq_div_iff hr.ne').2
  apply mul_left_cancel₀ (show 2*chord ≠ 0 by positivity)
  nlinarith only [hcos]

theorem SwitchData.base_angles {a b U : Point} {r : ℝ}
    (S : SwitchData a b U r) (hU : dist U a = dist U b) :
    EuclideanGeometry.angle b a U = Real.pi/2-SwitchData.angle S ∧
      EuclideanGeometry.angle a b U = Real.pi/2-SwitchData.angle S := by
  have hc : dist a b = 2*S.chord := by
    rw [S.chord_exact,halfChord]
    ring
  have hleft := isosceles_base_cos hU hc S.radius_exact.symm S.chord_pos S.radius_pos
  have hright := isosceles_base_cos hU.symm
    (by rwa [dist_comm] at hc) (hU.symm.trans S.radius_exact.symm)
    S.chord_pos S.radius_pos
  have ht := SwitchData.angle_bounds S
  have hmem : Real.pi/2-SwitchData.angle S ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have htarget : Real.cos (Real.pi/2-SwitchData.angle S) = S.chord/S.radius := by
    rw [Real.cos_pi_div_two_sub,SwitchData.sin_angle]
  constructor
  · exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _,
      EuclideanGeometry.angle_le_pi _ _ _⟩ hmem (hleft.trans htarget.symm)
  · exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _,
      EuclideanGeometry.angle_le_pi _ _ _⟩ hmem (hright.trans htarget.symm)

theorem actual_switch_base_angles {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (i : Fin 9) (U : ActualBoundaryNeighborTies.NeighborTie c r i) :
    ∃ S : SwitchData (c (ActualRingDirectionOrder.ringSite i))
      (c (ActualRingLinkBoundaryData.nextSite i)) (circleMap U.angle) r,
      EuclideanGeometry.angle (c (ActualRingLinkBoundaryData.nextSite i))
          (c (ActualRingDirectionOrder.ringSite i)) (circleMap U.angle) =
        Real.pi/2-SwitchData.angle S ∧
      EuclideanGeometry.angle (c (ActualRingDirectionOrder.ringSite i))
          (c (ActualRingLinkBoundaryData.nextSite i)) (circleMap U.angle) =
        Real.pi/2-SwitchData.angle S := by
  obtain ⟨S⟩ := actual_boundary_switch_metric h hr i U
  exact ⟨S,SwitchData.base_angles S U.equidistant⟩

end N11Formalization.ActualSwitchBaseAngle
#check @N11Formalization.ActualSwitchBaseAngle.actual_switch_base_angles
#print axioms N11Formalization.ActualSwitchBaseAngle.SwitchData.base_angles
#print axioms N11Formalization.ActualSwitchBaseAngle.actual_switch_base_angles
