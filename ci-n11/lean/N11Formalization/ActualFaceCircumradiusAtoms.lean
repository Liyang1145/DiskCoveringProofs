import N11Formalization.ActualMetricAngleAtoms

/-! Actual face circumradius and sine atoms, including obtuse faces.
The circumradius is the original common-nearest witness distance; no
candidate circumcenter, saturation, or abstract radius premise is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualFaceCircumradiusAtoms
open ActualMetricAngleAtoms ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualVoronoiCells FlashTiling

theorem determinant_norm_adjugate (u x y : Point) :
    ‖u‖^2*det2 x y^2 =
      ‖x‖^2*(inner ℝ u y)^2 + ‖y‖^2*(inner ℝ u x)^2 -
        2*inner ℝ x y*inner ℝ u x*inner ℝ u y := by
  simp only [PinTangentGeometry.norm_sq_coords,PinTangentGeometry.inner_coords,det2]
  ring

theorem common_circle_projection {a b z : Point} (he : dist z a=dist z b) :
    inner ℝ (z-a) (b-a)=‖b-a‖^2/2 := by
  have hs := congrArg (fun t : ℝ => t^2) he
  have hv : z-b=(z-a)-(b-a) := by module
  rw [dist_eq_norm,dist_eq_norm,hv] at hs
  rw [norm_sub_sq_real (z-a) (b-a)] at hs
  linarith

theorem common_circle_area_product {a b k z : Point}
    (hab : dist z a=dist z b) (hak : dist z a=dist z k) :
    4*dist z a^2*orient a b k^2 = dist a b^2*dist a k^2*dist b k^2 := by
  have hg := determinant_norm_adjugate (z-a) (b-a) (k-a)
  rw [common_circle_projection hab,common_circle_projection hak] at hg
  have hv : b-k=(b-a)-(k-a) := by module
  have hbk : dist b k^2=‖b-a‖^2+‖k-a‖^2-2*inner ℝ (b-a) (k-a) := by
    rw [dist_eq_norm,hv,norm_sub_sq_real]
    ring
  rw [hbk,dist_comm a b,dist_comm a k,dist_eq_norm,dist_eq_norm,dist_eq_norm]
  change 4*‖z-a‖^2*det2 (b-a) (k-a)^2 =
    ‖b-a‖^2*‖k-a‖^2*(‖b-a‖^2+‖k-a‖^2-2*inner ℝ (b-a) (k-a))
  nlinarith only [hg]

theorem actual_angle_strict_of_positive_orient {a b k : Point}
    (hp : 0 < orient a b k) :
    0 < EuclideanGeometry.angle b a k ∧ EuclideanGeometry.angle b a k < Real.pi := by
  have hd := determinant_eq_norm_sin hp.le
  have hsin : 0 < Real.sin (EuclideanGeometry.angle b a k) := by
    change orient a b k = ‖b-a‖*‖k-a‖*
      Real.sin (EuclideanGeometry.angle b a k) at hd
    have hn := mul_nonneg (norm_nonneg (b-a)) (norm_nonneg (k-a))
    by_contra hnot
    have hs := mul_nonpos_of_nonneg_of_nonpos hn (le_of_not_gt hnot)
    linarith
  have hlo := EuclideanGeometry.angle_nonneg b a k
  have hhi := EuclideanGeometry.angle_le_pi b a k
  constructor
  · apply lt_of_le_of_ne hlo
    intro he
    rw [← he,Real.sin_zero] at hsin
    exact (lt_irrefl 0) hsin
  · apply lt_of_le_of_ne hhi
    intro he
    rw [he,Real.sin_pi] at hsin
    exact (lt_irrefl 0) hsin

theorem common_circle_sine_rule {a b k z : Point}
    (hp : 0 < orient a b k) (hab : dist z a=dist z b) (hak : dist z a=dist z k) :
    dist b k = 2*dist z a*Real.sin (EuclideanGeometry.angle b a k) := by
  have hd := determinant_eq_norm_sin hp.le
  change orient a b k=‖b-a‖*‖k-a‖*Real.sin (EuclideanGeometry.angle b a k) at hd
  have hn : 0 < ‖b-a‖*‖k-a‖ := by
    have hn0 := mul_nonneg (norm_nonneg (b-a)) (norm_nonneg (k-a))
    apply lt_of_le_of_ne hn0
    intro he
    rw [← he,zero_mul] at hd
    linarith
  have hprod := common_circle_area_product hab hak
  rw [hd,dist_comm a b,dist_comm a k,dist_eq_norm b a,dist_eq_norm k a] at hprod
  have hsq : (‖b-a‖*‖k-a‖)^2 *
      (2*dist z a*Real.sin (EuclideanGeometry.angle b a k))^2 =
      (‖b-a‖*‖k-a‖)^2*(dist b k)^2 := by
    nlinarith only [hprod]
  have hc := mul_left_cancel₀ (pow_ne_zero 2 hn.ne') hsq
  have ht : 0 ≤ 2*dist z a*Real.sin (EuclideanGeometry.angle b a k) :=
    mul_nonneg (mul_nonneg (by norm_num) dist_nonneg)
      (InnerProductGeometry.sin_angle_nonneg _ _)
  nlinarith [dist_nonneg (x := b) (y := k)]

def faceRadius {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (A : R.Index) : ℝ :=
  dist (R.witness A) (c (R.labels A 0))

theorem actual_face_equidistant {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s t : Fin 3) :
    dist (R.witness A) (c (R.labels A s)) =
      dist (R.witness A) (c (R.labels A t)) := by
  have hN := (Refinement.real_triangle R A).2.1
  exact le_antisymm ((hN s).1 _) ((hN t).1 _)

theorem actual_face_radius_bounds {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (R : Refinement c r) (A : R.Index) :
    0 < faceRadius R A ∧ faceRadius R A ≤ r := by
  have hN := (Refinement.real_triangle R A).2.1
  refine ⟨?_,(hN 0).2⟩
  apply dist_pos.mpr
  intro he
  have heq := actual_face_equidistant R A 0 1
  rw [he,dist_self] at heq
  have hc : c (R.labels A 0)=c (R.labels A 1) := dist_eq_zero.mp heq.symm
  exact ((Refinement.labels_injective R A).ne (by decide : (0:Fin 3) ≠ 1)) (h.injective hc)

theorem actual_face_sine_rule_zero {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) :
    dist (c (R.labels A 1)) (c (R.labels A 2)) =
      2*faceRadius R A*Real.sin (faceAngle R A 0) := by
  have hp := (Refinement.real_triangle R A).2.2
  simpa only [faceRadius,faceAngle,zero_add] using
    common_circle_sine_rule hp (actual_face_equidistant R A 0 1)
      (actual_face_equidistant R A 0 2)

theorem actual_cyclic_face_orient {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    orient (c (R.labels A s)) (c (R.labels A (s+1))) (c (R.labels A (s+2))) =
      orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2)) := by
  fin_cases s
  · norm_num
  · change orient (c (R.labels A 1)) (c (R.labels A 2)) (c (R.labels A 0))=_
    exact (ActualIncidentFacetAdjacency.orient_cycle _ _ _).symm
  · change orient (c (R.labels A 2)) (c (R.labels A 0)) (c (R.labels A 1))=_
    rw [ActualIncidentFacetAdjacency.orient_cycle]

theorem actual_face_angle_strict {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    0 < faceAngle R A s ∧ faceAngle R A s < Real.pi := by
  have hp : 0 < orient (c (R.labels A s)) (c (R.labels A (s+1))) (c (R.labels A (s+2))) := by
    rw [actual_cyclic_face_orient]
    exact (Refinement.real_triangle R A).2.2
  exact actual_angle_strict_of_positive_orient hp

theorem actual_face_sine_rule {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    dist (c (R.labels A (s+1))) (c (R.labels A (s+2))) =
      2*faceRadius R A*Real.sin (faceAngle R A s) := by
  have hp : 0 < orient (c (R.labels A s)) (c (R.labels A (s+1))) (c (R.labels A (s+2))) := by
    rw [actual_cyclic_face_orient]
    exact (Refinement.real_triangle R A).2.2
  have hs := common_circle_sine_rule hp (actual_face_equidistant R A s (s+1))
    (actual_face_equidistant R A s (s+2))
  rw [← actual_face_equidistant R A 0 s] at hs
  exact hs

def faceSquaredNormalized {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) : ℝ := (faceRadius R A/(19/50))^2

theorem actual_face_squared_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (A : R.Index) :
    0 ≤ faceSquaredNormalized R A ∧ faceSquaredNormalized R A ≤ 1 := by
  have hb := actual_face_radius_bounds h R A
  have hlo : 0 ≤ faceRadius R A/(19/50) := div_nonneg hb.1.le (by norm_num)
  have hhi : faceRadius R A/(19/50) ≤ 1 := by
    rw [div_le_one₀ (by norm_num : (0:ℝ)<19/50)]
    exact hb.2.trans hr.le
  unfold faceSquaredNormalized
  exact ⟨sq_nonneg _,by nlinarith⟩

theorem actual_face_squared_units {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) :
    (19/50 : ℝ)^2*faceSquaredNormalized R A=faceRadius R A^2 := by
  unfold faceSquaredNormalized
  ring

theorem actual_face_area_product {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) :
    orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2))/2 =
      2*faceRadius R A^2*Real.sin (faceAngle R A 0)*
        Real.sin (faceAngle R A 1)*Real.sin (faceAngle R A 2) := by
  have hs1 := actual_face_sine_rule R A 1
  have hs2 := actual_face_sine_rule R A 2
  change dist (c (R.labels A 2)) (c (R.labels A 0)) =
    2*faceRadius R A*Real.sin (faceAngle R A 1) at hs1
  change dist (c (R.labels A 0)) (c (R.labels A 1)) =
    2*faceRadius R A*Real.sin (faceAngle R A 2) at hs2
  rw [actual_face_area_angle,dist_comm (c (R.labels A 1)) (c (R.labels A 0)),hs2,hs1]
  ring

theorem actual_face_factor_area {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) :
    orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2))/2 =
      2*(19/50 : ℝ)^2*faceSquaredNormalized R A*Real.sin (faceAngle R A 0)*
        Real.sin (faceAngle R A 1)*Real.sin (faceAngle R A 2) := by
  rw [show 2*(19/50 : ℝ)^2*faceSquaredNormalized R A =
    2*((19/50 : ℝ)^2*faceSquaredNormalized R A) by ring,actual_face_squared_units]
  exact actual_face_area_product R A

end N11Formalization.ActualFaceCircumradiusAtoms
#check @N11Formalization.ActualFaceCircumradiusAtoms.actual_face_radius_bounds
#check @N11Formalization.ActualFaceCircumradiusAtoms.actual_face_sine_rule_zero
#check @N11Formalization.ActualFaceCircumradiusAtoms.actual_face_factor_area
#print axioms N11Formalization.ActualFaceCircumradiusAtoms.common_circle_sine_rule
#print axioms N11Formalization.ActualFaceCircumradiusAtoms.actual_face_sine_rule_zero
#print axioms N11Formalization.ActualFaceCircumradiusAtoms.actual_face_factor_area
