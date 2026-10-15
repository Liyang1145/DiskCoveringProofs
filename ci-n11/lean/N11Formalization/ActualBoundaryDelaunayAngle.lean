import N11Formalization.ActualDelaunayFlatDiagonal
import N11Formalization.ActualSwitchWedgeArea

/-! True boundary face-to-switch metric inequalities.
The switch term is the paid half-apex angle b, not the apex 2b.
Signed bisector coefficients retain obtuse selected faces. The true
circle exit lies strictly past every interior primal witness, so the
combined cotangent is positive without a generic-position premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryDelaunayAngle

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementSideMultiplicity
open ActualBoundaryExteriorGeometry ActualHubEdgeGeometry ActualHubEdgeEndpointGeometry
open ActualIncidentFacetAdjacency ActualBoundaryTriangleExterior ActualSwitchWedgeArea
open ActualDelaunayAngleBounds ActualDelaunayAngleConsumer ActualDelaunayFlatDiagonal
open ActualMetricAngleAtoms ActualFaceCircumradiusAtoms ActualSquaredSideMatching
open ActualBoundarySwitchMetric ActualBoundarySwitchAngles ActualSwitchSineAtoms
open ActualBoundaryNineTies ActualBoundaryNeighborTies ActualSwitchAtomAggregate
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder FlashTiling

theorem perp_norm_sq (e : Point) : ‖perp e‖^2 = ‖e‖^2 := by
  simp only [PinTangentGeometry.norm_sq_coords, perp,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem bisector_coefficient_orient {a b x : Point} {s : ℝ}
    (hx : x-midpoint a b = s • perp (b-a)) :
    orient a b x = s*‖b-a‖^2 := by
  rw [← perp_inner_orient]
  have he : x-a = (x-midpoint a b)+(midpoint a b-a) := by module
  rw [he, hx, midpoint_sub, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, perp_inner, mul_zero, add_zero, real_inner_self_eq_norm_sq,
    perp_norm_sq]

theorem circle_coefficient_dot {a b k z : Point} {t : ℝ}
    (hz : z-midpoint a b = t • perp (b-a)) (he : dist z a = dist z k) :
    edgeDot a b k = 2*t*orient a b k := by
  have hp := translated_bisector he
  have hv : z-a = (1/2 : ℝ) • (b-a)+t • perp (b-a) := by
    rw [← midpoint_sub, ← hz]
    module
  rw [hv, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    perp_inner_orient, real_inner_comm (k-a) (b-a)] at hp
  have hd : edgeDot a b k = ‖k-a‖^2-inner ℝ (k-a) (b-a) := by
    unfold edgeDot
    rw [show a-k = -(k-a) by module, show b-k = (b-a)-(k-a) by module,
      inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  rw [hd]
  nlinarith only [hp]

theorem face_cotangent_coefficient {a b k z : Point} {t : ℝ}
    (hp : 0 < orient a b k) (hz : z-midpoint a b = t • perp (b-a))
    (he : dist z a = dist z k) :
    Real.cos (EuclideanGeometry.angle a k b) / Real.sin (EuclideanGeometry.angle a k b) = 2*t := by
  have hs := positive_orient_sine hp
  have hc := edge_dot_cosine a b k
  have hd := circle_coefficient_dot hz he
  have hprod : 0 < dist a k * dist b k := by
    apply lt_of_le_of_ne (mul_nonneg dist_nonneg dist_nonneg)
    intro hh
    rw [← hh, zero_mul] at hs
    linarith
  have ho : orient k a b = orient a b k := orient_cycle _ _ _
  have ha := actual_angle_strict_of_positive_orient (a := k) (b := a) (k := b) (ho ▸ hp)
  have hsin := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  apply (div_eq_iff hsin.ne').2
  apply mul_left_cancel₀ hprod.ne'
  calc
    (dist a k * dist b k) * Real.cos (EuclideanGeometry.angle a k b) = edgeDot a b k := hc.symm
    _ = 2*t*orient a b k := hd
    _ = (dist a k * dist b k)*(2*t*Real.sin (EuclideanGeometry.angle a k b)) := by
      rw [hs]
      ring

theorem switch_cotangent_coefficient {a b U : Point} {r s : ℝ}
    (hab : a ≠ b) (he : dist U a = dist U b) (hU : orient a b U < 0)
    (hs : U-midpoint a b = s • perp (b-a)) (S : SwitchData a b U r) :
    Real.cos (SwitchData.angle S) / Real.sin (SwitchData.angle S) = -2*s := by
  have hsq := bisector_wedge_squared hab he
  rw [← S.chord_exact, ← S.offset_exact] at hsq
  have hpositive : 0 < orient a U b := by
    have hh := orient_swap a b U
    linarith
  have hm := mul_pos S.chord_pos S.offset_pos
  have hatom : orient a U b / 2 = S.chord*S.offset := by nlinarith only [hsq,hpositive,hm]
  have hcoord := bisector_coefficient_orient hs
  have hch : ‖b-a‖ = 2*S.chord := by
    rw [← dist_eq_norm, dist_comm, S.chord_exact, halfChord]
    ring
  have hneg : -orient a b U = 2*S.chord*S.offset := by
    have hh := orient_swap a b U
    linarith
  rw [hcoord,hch] at hneg
  have hfactor : S.chord*(S.offset+2*s*S.chord) = 0 := by nlinarith only [hneg]
  have hoff : S.offset = (-2*s)*S.chord := by
    have hh := (mul_eq_zero.mp hfactor).resolve_left S.chord_pos.ne'
    linarith
  have hcot : Real.cos (SwitchData.angle S) / Real.sin (SwitchData.angle S) = S.offset/S.chord := by
    rw [SwitchData.cos_angle, SwitchData.sin_angle]
    field_simp [S.radius_pos.ne',S.chord_pos.ne']
  rw [hcot]
  exact (div_eq_iff S.chord_pos.ne').2 hoff

theorem boundary_bisector_coefficients_order {a b U z : Point} {s t : ℝ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hU : ‖U‖ = 1) (hz : ‖z‖ < 1)
    (ho : orient a b U < 0)
    (hUs : U-midpoint a b = s • perp (b-a))
    (hzt : z-midpoint a b = t • perp (b-a)) : s < t := by
  have hcoord := bisector_coefficient_orient hUs
  have hsneg : s < 0 := by
    by_contra hnot
    have hh := mul_nonneg (le_of_not_gt hnot) (sq_nonneg ‖b-a‖)
    rw [← hcoord] at hh
    exact (not_lt_of_ge hh) ho
  have hSm := outward_inner_positive hU (midpoint_inside ha hb)
  rw [hUs, real_inner_smul_right] at hSm
  have hinner : inner ℝ U (perp (b-a)) < 0 := by
    by_contra hnot
    have hh := mul_nonpos_of_nonpos_of_nonneg hsneg.le (le_of_not_gt hnot)
    exact (not_lt_of_ge hh) hSm
  have hv : U-z = (s-t) • perp (b-a) := by
    calc
      U-z = (U-midpoint a b)-(z-midpoint a b) := by module
      _ = s • perp (b-a)-t • perp (b-a) := by rw [hUs,hzt]
      _ = (s-t) • perp (b-a) := by module
  have hUz := outward_inner_positive hU hz
  rw [hv, real_inner_smul_right] at hUz
  have hdiff : s-t < 0 := by
    by_contra hnot
    have hh := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hnot) hinner.le
    exact (not_lt_of_ge hh) hUz
  linarith

theorem boundary_cotangent_sum_pos {a b k U z : Point} {r : ℝ}
    (hab : a ≠ b) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hU : ‖U‖ = 1) (hz : ‖z‖ < 1)
    (hUe : dist U a = dist U b) (hze : dist z a = dist z b)
    (hzk : dist z a = dist z k) (hoK : 0 < orient a b k) (hoU : orient a b U < 0)
    (S : SwitchData a b U r) :
    0 < Real.cos (EuclideanGeometry.angle a k b) / Real.sin (EuclideanGeometry.angle a k b) +
      Real.cos (SwitchData.angle S) / Real.sin (SwitchData.angle S) := by
  obtain ⟨s,hs⟩ := bisector_perp_coordinate hab hUe
  obtain ⟨t,ht⟩ := bisector_perp_coordinate hab hze
  have horder := boundary_bisector_coefficients_order ha hb hU hz hoU hs ht
  rw [face_cotangent_coefficient hoK ht hzk, switch_cotangent_coefficient hab hUe hoU hs S]
  linarith

theorem angle_sum_lt_pi_of_cotangent_sum_pos {α β : ℝ}
    (hα0 : 0 < α) (hαπ : α < Real.pi) (hβ0 : 0 < β) (hβπ : β < Real.pi)
    (hpos : 0 < Real.cos α / Real.sin α + Real.cos β / Real.sin β) : α+β < Real.pi := by
  have hα := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have hβ := Real.sin_pos_of_pos_of_lt_pi hβ0 hβπ
  have he : Real.sin (α+β) =
      (Real.cos α / Real.sin α + Real.cos β / Real.sin β)*(Real.sin α*Real.sin β) := by
    rw [Real.sin_add]
    field_simp [hα.ne',hβ.ne']
    ring
  have hspos : 0 < Real.sin (α+β) := by rw [he]; exact mul_pos hpos (mul_pos hα hβ)
  by_contra hnot
  have hge : Real.pi ≤ α+β := le_of_not_gt hnot
  have hle : α+β ≤ 2*Real.pi := by linarith
  have hsnon := Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (show α+β-2*Real.pi ≤ 0 by linarith)
    (show -Real.pi ≤ α+β-2*Real.pi by linarith)
  rw [Real.sin_sub_two_pi] at hsnon
  exact (not_lt_of_ge hsnon) hspos

theorem actual_boundary_side_cotangent_sum_pos {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    0 < Real.cos (faceAngle R A s) / Real.sin (faceAngle R A s) +
      Real.cos (SwitchData.angle (switchData h hr v i)) /
        Real.sin (SwitchData.angle (switchData h hr v i)) := by
  have hd : ∀ u : Fin 3, u ≠ u+1 ∧ u ≠ u+2 := by decide
  have h1 := (Refinement.labels_injective R A).ne (hd s).1
  have h2 := (Refinement.labels_injective R A).ne (hd s).2
  have hlabels : ringSite i ∈ labelSet R A ∧ nextSite i ∈ labelSet R A ∧
      R.labels A s ≠ ringSite i ∧ R.labels A s ≠ nextSite i := by
    rcases hs with ⟨hs1,hs2⟩ | ⟨hs1,hs2⟩
    · exact ⟨mem_labelSet.mpr ⟨s+1,hs1⟩,mem_labelSet.mpr ⟨s+2,hs2⟩,
        hs1 ▸ h1,hs2 ▸ h2⟩
    · exact ⟨mem_labelSet.mpr ⟨s+2,hs2⟩,mem_labelSet.mpr ⟨s+1,hs1⟩,
        hs2 ▸ h2,hs1 ▸ h1⟩
  obtain ⟨hAi,hAj,hki,hkj⟩ := hlabels
  have hAk : R.labels A s ∈ labelSet R A := mem_labelSet.mpr ⟨s,rfl⟩
  have hNi := nearest_of_label_mem R hAi
  have hNj := nearest_of_label_mem R hAj
  have hNk := nearest_of_label_mem R hAk
  have hUorient : orient (c (ringSite i)) (c (nextSite i)) (circleMap (v.tie i).angle) < 0 := by
    have hp := actual_switch_wedge_positive h hr R i (v.tie i)
    have hh := orient_swap (c (ringSite i)) (c (nextSite i)) (circleMap (v.tie i).angle)
    linarith
  have hop := actual_boundary_triangle_exterior h R i (v.tie i) hki hkj hAi hAj hAk
  have hKorient : 0 < orient (c (ringSite i)) (c (nextSite i)) (c (R.labels A s)) := by
    rcases mul_neg_iff.mp hop with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · linarith
    · exact hb
  rw [face_angle_at_side R hs]
  exact boundary_cotangent_sum_pos (h.injective.ne (boundary_sites_distinct i).2.1.symm)
    (h.center_inside _) (h.center_inside _) (circleMap_norm _) (Refinement.real_triangle R A).1
    (v.tie i).equidistant (le_antisymm (hNi _) (hNj _)) (le_antisymm (hNi _) (hNk _))
    hKorient hUorient (switchData h hr v i)

theorem actual_boundary_side_angle_sum_lt_pi {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    faceAngle R A s + SwitchData.angle (switchData h hr v i) < Real.pi := by
  have hA := actual_face_angle_strict R A s
  have hb := SwitchData.angle_bounds (switchData h hr v i)
  exact angle_sum_lt_pi_of_cotangent_sum_pos hA.1 hA.2 hb.1
    (by linarith [Real.pi_pos]) (actual_boundary_side_cotangent_sum_pos h hr R v i hs)

theorem actual_boundary_side_angle_sum_le_pi {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    faceAngle R A s + SwitchData.angle (switchData h hr v i) ≤ Real.pi :=
  (actual_boundary_side_angle_sum_lt_pi h hr R v i hs).le

theorem actual_boundary_side_metric_producer {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) :
    ∃ A : R.Index, ∃ s : Fin 3, SideAt R A s (ringSite i) (nextSite i) ∧
      faceSideSquared R A s = switchSideSquared h hr v i ∧
      faceAngle R A s + SwitchData.angle (switchData h hr v i) < Real.pi ∧
      0 < Real.cos (faceAngle R A s) / Real.sin (faceAngle R A s) +
        Real.cos (SwitchData.angle (switchData h hr v i)) /
          Real.sin (SwitchData.angle (switchData h hr v i)) := by
  obtain ⟨A,s,hs,he⟩ := actual_boundary_side_match_producer h hr R v i
  exact ⟨A,s,hs,he,actual_boundary_side_angle_sum_lt_pi h hr R v i hs,
    actual_boundary_side_cotangent_sum_pos h hr R v i hs⟩

end N11Formalization.ActualBoundaryDelaunayAngle
#check @N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_cotangent_sum_pos
#check @N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_angle_sum_le_pi
#check @N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_metric_producer
#print axioms N11Formalization.ActualBoundaryDelaunayAngle.boundary_cotangent_sum_pos
#print axioms N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_cotangent_sum_pos
#print axioms N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_angle_sum_le_pi
#print axioms N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_metric_producer
