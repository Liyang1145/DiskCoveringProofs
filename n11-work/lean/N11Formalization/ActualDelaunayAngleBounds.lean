import N11Formalization.ActualSelectedEdgeOrientation
import N11Formalization.ActualMetricAngleAtoms
import N11Formalization.ActualFaceCircumradiusAtoms

/-! Delaunay opposite-angle control from the actual nearest witnesses.
The key inequality is proved algebraically: an empty circumcircle gives a
nonnegative sine of the sum of the two opposite angles. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualDelaunayAngleBounds

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementSideMultiplicity
open ActualSelectedEdgeOrientation ActualDelaunaySupport
open ActualMetricAngleAtoms FlashTiling

def edgeDot (a b p : Point) : ℝ := inner ℝ (a-p) (b-p)

theorem det_inner_basis (e p q u : Point) :
    det2 e p * inner ℝ u q + det2 p q * inner ℝ u e -
      det2 e q * inner ℝ u p = 0 := by
  simp only [det2, PinTangentGeometry.inner_coords]
  ring

theorem det_norm_identity (e p q : Point) :
    ‖e‖^2 * det2 p q = inner ℝ e p * det2 e q -
      inner ℝ e q * det2 e p := by
  rw [PinTangentGeometry.norm_sq_coords]
  simp only [det2, PinTangentGeometry.inner_coords]
  ring

theorem circle_gap_vector {e p q u : Point}
    (hue : 2*inner ℝ u e = ‖e‖^2)
    (hup : 2*inner ℝ u p = ‖p‖^2) :
    (‖p‖^2-inner ℝ p e)*(-det2 e q) +
      (‖q‖^2-inner ℝ q e)*det2 e p =
      det2 e p*(‖q‖^2-2*inner ℝ u q) := by
  have hb := det_inner_basis e p q u
  have hn := det_norm_identity e p q
  rw [← real_inner_comm p e, ← real_inner_comm q e]
  linear_combination 2*hb - det2 p q*hue + det2 e q*hup - hn

theorem point_circle_gap_identity {a b p q u : Point}
    (hua : dist u a = dist u b) (hup : dist u a = dist u p) :
    edgeDot a b p * (-orient a b q) + edgeDot a b q * orient a b p =
      orient a b p * (dist u q^2-dist u a^2) := by
  have hab := ActualHubEdgeEndpointGeometry.translated_bisector hua
  have hap := ActualHubEdgeEndpointGeometry.translated_bisector hup
  have hvec := circle_gap_vector (e := b-a) (p := p-a) (q := q-a) (u := u-a)
    (by simpa only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
      using hab.symm)
    (by simpa only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
      using hap.symm)
  have hdp : edgeDot a b p = ‖p-a‖^2-inner ℝ (p-a) (b-a) := by
    unfold edgeDot
    rw [show a-p=-(p-a) by module, show b-p=(b-a)-(p-a) by module,
      inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have hdq : edgeDot a b q = ‖q-a‖^2-inner ℝ (q-a) (b-a) := by
    unfold edgeDot
    rw [show a-q=-(q-a) by module, show b-q=(b-a)-(q-a) by module,
      inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have hgap : dist u q^2-dist u a^2 = ‖q-a‖^2-2*inner ℝ (u-a) (q-a) := by
    rw [dist_eq_norm, dist_eq_norm, show u-q=(u-a)-(q-a) by module,
      norm_sub_sq_real]
    ring
  rw [hdp,hdq,show orient a b p=det2 (b-a) (p-a) by rfl,
    show orient a b q=det2 (b-a) (q-a) by rfl,hgap]
  exact hvec

theorem angle_sum_le_pi_of_empty_circle {a b p q u : Point}
    (hp : 0 < orient a b p) (hq : orient a b q < 0)
    (hua : dist u a = dist u b) (hup : dist u a = dist u p)
    (huq : dist u a ≤ dist u q) :
    EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b ≤ Real.pi := by
  have hpa : 0 < EuclideanGeometry.angle a p b := by
    have ho : orient p a b = orient a b p := ActualIncidentFacetAdjacency.orient_cycle _ _ _
    exact (ActualFaceCircumradiusAtoms.actual_angle_strict_of_positive_orient
      (a := p) (b := a) (k := b) (ho ▸ hp)).1
  have hpb : EuclideanGeometry.angle a p b < Real.pi := by
    have ho : orient p a b = orient a b p := ActualIncidentFacetAdjacency.orient_cycle _ _ _
    exact (ActualFaceCircumradiusAtoms.actual_angle_strict_of_positive_orient
      (a := p) (b := a) (k := b) (ho ▸ hp)).2
  have hqa : 0 < EuclideanGeometry.angle a q b := by
    have ho : orient q b a = -orient a b q := by
      simp only [orient, det2, PiLp.sub_apply]
      ring
    have hh := (ActualFaceCircumradiusAtoms.actual_angle_strict_of_positive_orient
      (a := q) (b := b) (k := a) (by rw [ho]; linarith [hq])).1
    simpa only [EuclideanGeometry.angle_comm] using hh
  have hqb : EuclideanGeometry.angle a q b < Real.pi := by
    have ho : orient q b a = -orient a b q := by
      simp only [orient, det2, PiLp.sub_apply]
      ring
    have hh := (ActualFaceCircumradiusAtoms.actual_angle_strict_of_positive_orient
      (a := q) (b := b) (k := a) (by rw [ho]; linarith [hq])).2
    simpa only [EuclideanGeometry.angle_comm] using hh
  have hnepa : a ≠ p := by
    intro he
    subst p
    have := hp
    simp [orient,det2] at this
  have hnepb : b ≠ p := by
    intro he
    subst p
    have := hp
    simp [orient,det2] at this
    nlinarith
  have hneqa : a ≠ q := by
    intro he
    subst q
    have := hq
    simp [orient,det2] at this
  have hneqb : b ≠ q := by
    intro he
    subst q
    have := hq
    simp [orient,det2] at this
    nlinarith
  have hsP : orient a b p = dist a p*dist b p*
      Real.sin (EuclideanGeometry.angle a p b) := by
    have hdet : orient a b p = det2 (a-p) (b-p) := by
      simp only [orient,det2,PiLp.sub_apply]
      ring
    have hh := determinant_eq_norm_sin (show 0 ≤ det2 (a-p) (b-p) by
      rw [← hdet]
      exact hp.le)
    rw [hdet]
    simpa only [dist_eq_norm,EuclideanGeometry.angle,vsub_eq_sub] using hh
  have hcP : edgeDot a b p = dist a p*dist b p*
      Real.cos (EuclideanGeometry.angle a p b) := by
    have hh := InnerProductGeometry.cos_angle_mul_norm_mul_norm (a-p) (b-p)
    calc
      edgeDot a b p = inner ℝ (a-p) (b-p) := rfl
      _ = Real.cos (InnerProductGeometry.angle (a-p) (b-p)) *
          (‖a-p‖*‖b-p‖) := hh.symm
      _ = dist a p*dist b p*Real.cos (EuclideanGeometry.angle a p b) := by
        simp only [dist_eq_norm,EuclideanGeometry.angle,vsub_eq_sub]
        ring
  have hsQ : -orient a b q = dist a q*dist b q*
      Real.sin (EuclideanGeometry.angle a q b) := by
    have hdet : -orient a b q = det2 (b-q) (a-q) := by
      simp only [orient,det2,PiLp.sub_apply]
      ring
    have hh := determinant_eq_norm_sin (show 0 ≤ det2 (b-q) (a-q) by
      rw [← hdet]
      linarith [hq])
    rw [hdet]
    have hh' := hh
    rw [InnerProductGeometry.angle_comm] at hh'
    simpa only [dist_eq_norm,EuclideanGeometry.angle,vsub_eq_sub,mul_comm,mul_assoc,
      mul_left_comm] using hh'
  have hcQ : edgeDot a b q = dist a q*dist b q*
      Real.cos (EuclideanGeometry.angle a q b) := by
    have hh := InnerProductGeometry.cos_angle_mul_norm_mul_norm (b-q) (a-q)
    have hh' := hh.symm
    rw [InnerProductGeometry.angle_comm, real_inner_comm] at hh'
    calc
      edgeDot a b q = inner ℝ (a-q) (b-q) := rfl
      _ = Real.cos (InnerProductGeometry.angle (a-q) (b-q)) *
          (‖a-q‖*‖b-q‖) := by simpa only [mul_comm] using hh'
      _ = dist a q*dist b q*Real.cos (EuclideanGeometry.angle a q b) := by
        simp only [dist_eq_norm,EuclideanGeometry.angle,vsub_eq_sub]
        ring
  have hgap_nonneg : 0 ≤ dist u q^2-dist u a^2 := by
    nlinarith [dist_nonneg (x := u) (y := q),dist_nonneg (x := u) (y := a)]
  have hnum : 0 ≤ edgeDot a b p*(-orient a b q)+edgeDot a b q*orient a b p := by
    rw [point_circle_gap_identity hua hup]
    exact mul_nonneg hp.le hgap_nonneg
  let α := EuclideanGeometry.angle a p b
  let β := EuclideanGeometry.angle a q b
  have hprod :
      (dist a p*dist b p)*(dist a q*dist b q)*Real.sin (α+β) =
        edgeDot a b p*(-orient a b q)+edgeDot a b q*orient a b p := by
    dsimp [α,β]
    rw [Real.sin_add]
    rw [hcP, hsQ, hcQ, hsP]
    ring
  have hsin : 0 ≤ Real.sin (α+β) := by
    have hpos : 0 < (dist a p*dist b p)*(dist a q*dist b q) := by
      exact mul_pos (mul_pos (dist_pos.mpr hnepa) (dist_pos.mpr hnepb))
        (mul_pos (dist_pos.mpr hneqa) (dist_pos.mpr hneqb))
    nlinarith [hprod,hnum]
  dsimp [α,β] at hsin ⊢
  by_contra hnot
  have hgt : Real.pi < EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b :=
    lt_of_not_ge hnot
  have hlt : EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b < 2*Real.pi := by
    nlinarith [hpb,hqb,Real.pi_pos]
  have hneg := Real.sin_neg_of_neg_of_neg_pi_lt
    (show EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b - 2*Real.pi < 0 by linarith)
    (show -Real.pi < EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b - 2*Real.pi by linarith)
  rw [Real.sin_sub_two_pi] at hneg
  exact (not_lt_of_ge hsin) hneg

end N11Formalization.ActualDelaunayAngleBounds
#check @N11Formalization.ActualDelaunayAngleBounds.angle_sum_le_pi_of_empty_circle
#print axioms N11Formalization.ActualDelaunayAngleBounds.angle_sum_le_pi_of_empty_circle
