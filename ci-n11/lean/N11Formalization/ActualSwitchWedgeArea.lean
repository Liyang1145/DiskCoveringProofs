import N11Formalization.ActualSwitchAtomAggregate
import N11Formalization.ActualCenterRingShoelace

/-! Actual outward switch wedge equals the positive chord-offset atom.
Its sign is paid by the real +1 boundary chain and nearest exterior sign.
The exact metric identity does not assume an acute selected triangle. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSwitchWedgeArea
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNeighborTies ActualBoundaryNineTies ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualTriangleBoundaryChain ActualBoundaryChainConservation
open ActualBoundaryShoelace ActualRefinementBoundaryCount ActualRefinementTriangleUniqueness
open ActualRefinementSideMultiplicity ActualBoundaryTriangleExterior ActualCenterRingShoelace
open ActualBoundaryExteriorGeometry ActualBoundarySwitchMetric ActualHubEdgeGeometry FlashTiling
open ActualRefinementInteriorFacetCount

theorem actual_switch_wedge_positive {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 9) (U : NeighborTie c r i) :
    0 < orient (c (ringSite i)) (circleMap U.angle) (c (nextSite i)) := by
  classical
  have hc := actual_boundary_triangle_count h hr R i
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (by rw [hc]; decide)
  have hmem := (Finset.mem_filter.mp hA).2
  have hij := (boundary_sites_distinct i).2.1.symm
  obtain ⟨k,hki,hkn,hset⟩ := ActualRefinementLinkDegrees.three_set_third
    (labelSet_card R A) hij hmem.1 hmem.2
  have hk : k ∈ labelSet R A := by rw [hset]; simp
  have hb : BoundaryLabels (ringSite i) (nextSite i) :=
    (boundary_labels_at_ring i (nextSite i)).mpr (Or.inr rfl)
  have ht := boundary_total_eq_coefficient h hr R hij hb hmem.1 hmem.2
  have hcoeff : coefficient R A (ringSite i) (nextSite i)=1 := by
    rw [← ht]
    exact actual_all_boundary_mass_positive_one h hr R i
  rw [coefficient_of_third R hij hki hkn hmem.1 hmem.2 hk] at hcoeff
  have hthird : 0 < orient (c (ringSite i)) (c (nextSite i)) (c k) := by
    by_contra hnot
    rw [if_neg hnot] at hcoeff
    norm_num at hcoeff
  have he := actual_boundary_triangle_exterior h R i U hki hkn hmem.1 hmem.2 hk
  have hneg : orient (c (ringSite i)) (c (nextSite i)) (circleMap U.angle)<0 := by
    rcases mul_neg_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · linarith
    · exact ha
  rw [ActualIncidentFacetAdjacency.orient_swap]
  linarith

theorem determinant_gram (w z : Point) :
    det2 w z^2 = ‖w‖^2*‖z‖^2-(inner ℝ w z)^2 := by
  have hw : ‖w‖^2=w 0^2+w 1^2 := by
    rw [← real_inner_self_eq_norm_sq,PinTangentGeometry.inner_coords]
    ring
  have hz : ‖z‖^2=z 0^2+z 1^2 := by
    rw [← real_inner_self_eq_norm_sq,PinTangentGeometry.inner_coords]
    ring
  rw [hw,hz,PinTangentGeometry.inner_coords]
  unfold det2
  ring

theorem bisector_wedge_squared {a b U : Point} (hab : a ≠ b)
    (he : dist U a=dist U b) :
    (orient a U b/2)^2 =
      (halfChord a b*exteriorOffset a b U)^2 := by
  obtain ⟨s,hs⟩ := bisector_perp_coordinate hab he
  have ho : inner ℝ (b-a) (U-midpoint a b)=0 := by
    rw [hs,real_inner_smul_right,real_inner_comm,perp_inner,mul_zero]
  have hgram := determinant_gram (b-a) (U-midpoint a b)
  rw [ho] at hgram
  norm_num at hgram
  have hv : U-a=(U-midpoint a b)+(1/2 : ℝ) • (b-a) := by
    rw [← midpoint_sub]
    module
  have horient : orient a U b = -det2 (b-a) (U-midpoint a b) := by
    unfold orient
    rw [hv,det2_add_left,det2_smul_left,det2_self,mul_zero,add_zero]
    exact ActualTriangleShoelace.det2_antisymm _ _
  have hdist : dist a b=‖b-a‖ := by rw [dist_comm a b,dist_eq_norm]
  rw [horient]
  unfold halfChord exteriorOffset
  rw [hdist]
  nlinarith [hgram]

theorem actual_switch_wedge_equals_atom {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 9) (U : NeighborTie c r i)
    (S : SwitchData (c (ringSite i)) (c (nextSite i)) (circleMap U.angle) r) :
    orient (c (ringSite i)) (circleMap U.angle) (c (nextSite i))/2 =
      S.chord*S.offset := by
  have hp := actual_switch_wedge_positive h hr R i U
  have hs := bisector_wedge_squared (h.injective.ne (boundary_sites_distinct i).2.1.symm)
    U.equidistant
  rw [← S.chord_exact,← S.offset_exact] at hs
  have hm := mul_pos S.chord_pos S.offset_pos
  nlinarith

end N11Formalization.ActualSwitchWedgeArea
#check @N11Formalization.ActualSwitchWedgeArea.actual_switch_wedge_equals_atom
#print axioms N11Formalization.ActualSwitchWedgeArea.actual_switch_wedge_equals_atom
