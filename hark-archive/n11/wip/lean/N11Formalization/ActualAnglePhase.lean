import N11Formalization.ActualFaceCircumradiusAtoms

/-! True real angles as directed phase differences modulo 2*pi.
The sine sign is proved from the actual determinant, including flat
nonnegative sectors. This is a productive precursor to real site sums,
not a site-angle-sum hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualAnglePhase
open ActualFiniteNearestRefinement ActualMetricAngleAtoms ActualFaceCircumradiusAtoms
open ActualRingShoelacePositive FlashTiling

def directionAngle (x : Point) : ℝ := circleAngle (centerDir x)

theorem direction_representation {x : Point} (hx : x≠0) :
    x=‖x‖ • circleMap (directionAngle x) := by
  rw [directionAngle,circleMap_circleAngle _ (centerDir_norm hx)]
  exact self_eq_norm_smul_centerDir hx

theorem positive_determinant_angle_phase {x y : Point}
    (hx : x≠0) (hy : y≠0) (hd : 0 ≤ det2 x y) :
    (InnerProductGeometry.angle x y : Real.Angle) =
      (directionAngle y : Real.Angle)-(directionAngle x : Real.Angle) := by
  have hprod : ‖x‖*‖y‖≠0 :=
    (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  have hinner : inner ℝ x y =
      ‖x‖*‖y‖*Real.cos (directionAngle y-directionAngle x) := by
    conv_lhs => rw [direction_representation hx,direction_representation hy]
    rw [real_inner_smul_left,real_inner_smul_right,inner_circleMap]
    rw [show directionAngle x-directionAngle y=-(directionAngle y-directionAngle x) by ring,
      Real.cos_neg]
    ring
  have hdet : det2 x y=‖x‖*‖y‖*Real.sin (directionAngle y-directionAngle x) := by
    conv_lhs => rw [direction_representation hx,direction_representation hy]
    rw [det2_smul_left,det2_smul,det_circleMap]
    ring
  have hc : Real.cos (InnerProductGeometry.angle x y) =
      Real.cos (directionAngle y-directionAngle x) := by
    apply mul_right_cancel₀ hprod
    rw [InnerProductGeometry.cos_angle_mul_norm_mul_norm,hinner]
    ring
  have hs : Real.sin (InnerProductGeometry.angle x y) =
      Real.sin (directionAngle y-directionAngle x) := by
    apply mul_right_cancel₀ hprod
    have ht := determinant_eq_norm_sin hd
    rw [hdet] at ht
    nlinarith only [ht]
  have he := Real.Angle.cos_sin_inj hc hs
  simpa only [Real.Angle.coe_sub] using he

def sitePhase (c : Fin 11 → Point) (i j : Fin 11) : Real.Angle :=
  (directionAngle (c j-c i) : Real.Angle)

theorem actual_face_slot_phase {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    (faceAngle R A s : Real.Angle) =
      sitePhase c (R.labels A s) (R.labels A (s+2)) -
        sitePhase c (R.labels A s) (R.labels A (s+1)) := by
  have hp : 0 < orient (c (R.labels A s)) (c (R.labels A (s+1))) (c (R.labels A (s+2))) := by
    rw [actual_cyclic_face_orient]
    exact (Refinement.real_triangle R A).2.2
  have hx : c (R.labels A (s+1))-c (R.labels A s)≠0 := by
    intro he
    simp only [orient,he,det2_zero_left] at hp
    exact (lt_irrefl 0) hp
  have hy : c (R.labels A (s+2))-c (R.labels A s)≠0 := by
    intro he
    simp [orient,he,det2] at hp
  exact positive_determinant_angle_phase hx hy hp.le

end N11Formalization.ActualAnglePhase
#check @N11Formalization.ActualAnglePhase.actual_face_slot_phase
#print axioms N11Formalization.ActualAnglePhase.positive_determinant_angle_phase
#print axioms N11Formalization.ActualAnglePhase.actual_face_slot_phase
