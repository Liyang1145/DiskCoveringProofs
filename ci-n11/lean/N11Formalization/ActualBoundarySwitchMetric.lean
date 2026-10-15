import N11Formalization.ActualBoundaryTriangleExterior

/-! Real positive boundary-switch offsets and exact Pythagorean rows.
The actual representative/originalr is kept; normalization by19/50 is
only a change of units, not a new inner-root replacement. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundarySwitchMetric
open ActualBoundaryExteriorGeometry ActualHubEdgeGeometry ActualHubEdgeEndpointGeometry
open ActualCoverStructuralReduction ActualBoundaryNeighborTies
open ActualRingDirectionOrder ActualRingLinkBoundaryData

def halfChord (a b : Point) : ℝ := dist a b/2
def exteriorOffset (a b U : Point) : ℝ := ‖U-midpoint a b‖

theorem exterior_offset_positive {a b U : Point}
    (ha : ‖a‖<1) (hb : ‖b‖<1) (hU : ‖U‖=1) :
    0 < exteriorOffset a b U := by
  apply norm_pos_iff.mpr
  intro he
  have heq := sub_eq_zero.mp he
  have hm := midpoint_inside ha hb
  rw [← heq,hU] at hm
  exact lt_irrefl 1 hm

theorem bisector_pythagorean {a b U : Point} (hab : a ≠ b)
    (hU : dist U a=dist U b) :
    dist U a^2 = halfChord a b^2+exteriorOffset a b U^2 := by
  obtain ⟨s,hs⟩ := bisector_perp_coordinate hab hU
  have horth : inner ℝ (U-midpoint a b) (midpoint a b-a)=0 := by
    rw [midpoint_sub,hs,real_inner_smul_left,real_inner_smul_right,perp_inner]
    ring
  have he : U-a=(U-midpoint a b)+(midpoint a b-a) := by module
  rw [dist_eq_norm,he,norm_add_sq_real,horth,mul_zero,add_zero,midpoint_sub,norm_smul,
    Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  have hd : dist a b=‖b-a‖ := by rw [dist_comm a b,dist_eq_norm]
  unfold halfChord exteriorOffset
  rw [hd]
  ring

structure SwitchData (a b U : Point) (r : ℝ) where
  chord : ℝ
  offset : ℝ
  radius : ℝ
  chord_exact : chord=halfChord a b
  offset_exact : offset=exteriorOffset a b U
  radius_exact : radius=dist U a
  chord_pos : 0 < chord
  offset_pos : 0 < offset
  radius_pos : 0 < radius
  original_radius : radius ≤ r
  pythagorean : chord^2+offset^2=radius^2
  chord_le_radius : chord ≤ radius
  offset_le_radius : offset ≤ radius
  normalized_radius : 0 ≤ radius/(19/50) ∧ radius/(19/50) ≤ 1

theorem actual_boundary_switch_metric {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (U : NeighborTie c r i) :
    Nonempty (SwitchData (c (ringSite i)) (c (nextSite i)) (circleMap U.angle) r) := by
  have hij := (boundary_sites_distinct i).2.1.symm
  have hchord : 0 < halfChord (c (ringSite i)) (c (nextSite i)) :=
    div_pos (dist_pos.mpr (h.injective.ne hij)) (by norm_num)
  have hoff : 0 < exteriorOffset (c (ringSite i)) (c (nextSite i)) (circleMap U.angle) :=
    exterior_offset_positive (h.center_inside (ringSite i)) (h.center_inside (nextSite i))
    (circleMap_norm U.angle)
  have hpy := bisector_pythagorean (h.injective.ne hij) U.equidistant
  have hnon := dist_nonneg (x := circleMap U.angle) (y := c (ringSite i))
  have hrad : 0 < dist (circleMap U.angle) (c (ringSite i)) := by
    nlinarith [sq_pos_of_pos hchord,
      sq_nonneg (exteriorOffset (c (ringSite i)) (c (nextSite i)) (circleMap U.angle))]
  have hc : halfChord (c (ringSite i)) (c (nextSite i)) ≤
      dist (circleMap U.angle) (c (ringSite i)) := by
    nlinarith [sq_nonneg (exteriorOffset (c (ringSite i)) (c (nextSite i)) (circleMap U.angle))]
  have he : exteriorOffset (c (ringSite i)) (c (nextSite i)) (circleMap U.angle) ≤
      dist (circleMap U.angle) (c (ringSite i)) := by
    nlinarith [sq_nonneg (halfChord (c (ringSite i)) (c (nextSite i)))]
  have hn : 0 ≤ dist (circleMap U.angle) (c (ringSite i))/(19/50) ∧
      dist (circleMap U.angle) (c (ringSite i))/(19/50) ≤ 1 := by
    constructor
    · positivity
    · rw [div_le_one₀ (by norm_num : (0 : ℝ)<19/50)]
      exact U.radius.trans hr.le
  exact ⟨⟨halfChord _ _,exteriorOffset _ _ _,dist _ _,rfl,rfl,rfl,
    hchord,hoff,hrad,U.radius,hpy.symm,hc,he,hn⟩⟩

end N11Formalization.ActualBoundarySwitchMetric
#check @N11Formalization.ActualBoundarySwitchMetric.actual_boundary_switch_metric
#print axioms N11Formalization.ActualBoundarySwitchMetric.bisector_pythagorean
#print axioms N11Formalization.ActualBoundarySwitchMetric.actual_boundary_switch_metric
