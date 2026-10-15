import N11Formalization.ActualHubLinkConnected
import N11Formalization.ActualRefinementBoundaryCount

/-! Real ring-cell frontier data for circle-augmented link connectedness.
All frontier points are actual nearest points. A point strictly insideD
has a selected true nearest neighbor; onS1 any other nearest label is one
of the two true boundary-ring neighbors. Both boundary neighbors really
occur, with produced circle points and selected triangles. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingLinkBoundaryData
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualClippedCellPartition ActualClippedSpokeEmbedding ActualHubLinkConnected
open ActualClippedCellFrontiers ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementSideMultiplicity ActualRefinementVertexLinks ActualRefinementFacetRetention
open ActualHubPositiveDegree ActualPositiveFacetGraph ActualClippedMeshVertices
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualBoundaryNineTies
open ActualBoundaryNearestPairs ActualBoundaryNeighborTies ActualRefinementBoundaryCount

def prevSite (i : Fin 9) : Fin 11 := ringSite (i-1)
def nextSite (i : Fin 9) : Fin 11 := ringSite (nextRing i)

theorem boundary_sites_distinct : ∀ i : Fin 9,
    prevSite i ≠ ringSite i ∧ nextSite i ≠ ringSite i ∧ prevSite i ≠ nextSite i := by
  decide +kernel

theorem clipped_frontier_mem {c : Fin 11 → Point} {i : Fin 11} {x : Point}
    (hx : x ∈ frontier (ClippedCell c i)) : x ∈ ClippedCell c i := by
  have hclosed : IsClosed (ClippedCell c i) := (clipped_compact c i).isClosed
  have hc := frontier_subset_closure hx
  rwa [hclosed.closure_eq] at hc

theorem clipped_pair_frontier {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) {x : Point} (hx : x ∈ unitDisk)
    (hpair : x ∈ Cell c i ∩ Cell c j) : x ∈ frontier (ClippedCell c i) := by
  rw [frontier,(clipped_compact c i).isClosed.closure_eq]
  exact ⟨⟨hx,hpair.1⟩,tied_point_not_cell_interior hc hij hpair.1 hpair.2⟩

theorem clipped_frontier_inside_cell_frontier {c : Fin 11 → Point} {i : Fin 11} {x : Point}
    (hx : x ∈ frontier (ClippedCell c i)) (hxn : ‖x‖ < 1) :
    x ∈ frontier (Cell c i) := by
  have hmem := clipped_frontier_mem hx
  rw [frontier,(cell_closed c i).closure_eq]
  refine ⟨hmem.2,?_⟩
  intro hxint
  have hxd : x ∈ interior unitDisk := by
    apply interior_mono (show {p : Point | ‖p‖ < 1} ⊆ unitDisk from
      fun p hp => mem_unitDisk.mpr hp.le)
    rw [(isOpen_lt continuous_norm continuous_const).interior_eq]
    exact hxn
  have hxclip : x ∈ interior (ClippedCell c i) := by
    rw [ClippedCell,interior_inter]
    exact ⟨hxd,hxint⟩
  exact Set.disjoint_left.mp disjoint_interior_frontier hxclip hx

theorem selected_neighbor_at_inside_frontier {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 11} {x : Point} (hx : x ∈ frontier (ClippedCell c i)) (hxn : ‖x‖ < 1) :
    ∃ j : Fin 11, Neighbor R i j ∧ x ∈ Cell c j := by
  have hcellfront := clipped_frontier_inside_cell_frontier hx hxn
  obtain ⟨hxi,j,hji,hxj⟩ := cell_frontier_tie hcellfront
  have hpos : ∃ k : Fin 11, k ≠ i ∧ x ∈ Cell c k ∧ PositivePair c i k := by
    by_cases hv : x ∈ ClippedVertices c
    · obtain ⟨F,hF⟩ := clipped_vertex_face h hr hv
      obtain ⟨k,hki,_,hk,hik⟩ := true_vertex_other_positive_neighbor h F hji.symm
        (mem_incident.mpr (by rw [hF]; exact hxi))
        (mem_incident.mpr (by rw [hF]; exact hxj))
      have hnear := mem_incident.mp hk
      rw [hF] at hnear
      exact ⟨k,hki,hnear,hik⟩
    · exact ⟨j,hji,hxj,vertex_free_pair_positive h.injective h.cover hji.symm
        hxn hv ⟨hxi,hxj⟩⟩
  obtain ⟨k,hki,hxk,hik⟩ := hpos
  obtain ⟨a,hai,hak⟩ := Refinement.positive_pair_retained R h hr hik
  exact ⟨k,⟨hki,a,mem_labelSet.mpr hai,mem_labelSet.mpr hak⟩,hxk⟩

theorem other_circle_label_boundary_neighbor {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) {j : Fin 11}
    (hji : j ≠ ringSite i) {x : Point} (hx : ‖x‖ = 1)
    (hxi : x ∈ Cell c (ringSite i)) (hxj : x ∈ Cell c j) :
    j = prevSite i ∨ j = nextSite i := by
  let J : Fin 9 := ⟨j.val,nearest_ring h.cover h.labels hx hxj⟩
  have hJ : ringSite J = j := Fin.ext rfl
  have hIJ : i ≠ J := by
    intro he
    apply hji
    rw [← hJ,he]
  have hcases := nearest_ring_pair_adjacent h.cover hr h.labels h.midpoint_order hIJ hx hxi
    (by rw [hJ]; exact hxj)
  rcases hcases with he | he
  · exact Or.inr (by rw [← hJ,he]; rfl)
  · have hpred : J = i-1 := by
      change i = J+1 at he
      rw [he,add_sub_cancel_right]
    exact Or.inl (by rw [← hJ,hpred]; rfl)

theorem actual_boundary_neighbors {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    Neighbor R (ringSite i) (prevSite i) ∧ Neighbor R (ringSite i) (nextSite i) := by
  have hp := PositivePair.symm (boundary_positive_pair h hr (i-1))
  have hpn : nextRing (i-1) = i := by change i-1+1 = i; exact sub_add_cancel _ _
  rw [hpn] at hp
  obtain ⟨A,hAi,hAp⟩ := Refinement.positive_pair_retained R h hr hp
  obtain ⟨B,hBi,hBn⟩ := Refinement.positive_pair_retained R h hr (boundary_positive_pair h hr i)
  have hd := boundary_sites_distinct i
  exact ⟨⟨hd.1,A,mem_labelSet.mpr hAi,mem_labelSet.mpr hAp⟩,
    ⟨hd.2.1,B,mem_labelSet.mpr hBi,mem_labelSet.mpr hBn⟩⟩

theorem actual_circle_frontier_point {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) :
    ∃ x : Point, x ∈ frontier (ClippedCell c (ringSite i)) ∧ ‖x‖ = 1 := by
  obtain ⟨z⟩ := neighbor_tie h.cover hr h.labels h.midpoint_order i
  exact ⟨circleMap z.angle,clipped_pair_frontier h.injective (boundary_sites_distinct i).2.1.symm
    (mem_unitDisk.mpr (circleMap_norm z.angle).le) z.nearest,circleMap_norm z.angle⟩

end N11Formalization.ActualRingLinkBoundaryData
#check @N11Formalization.ActualRingLinkBoundaryData.selected_neighbor_at_inside_frontier
#check @N11Formalization.ActualRingLinkBoundaryData.other_circle_label_boundary_neighbor
#print axioms N11Formalization.ActualRingLinkBoundaryData.selected_neighbor_at_inside_frontier
#print axioms N11Formalization.ActualRingLinkBoundaryData.actual_boundary_neighbors
