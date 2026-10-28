import N11Formalization.ActualRefinementDiagonalCount
import N11Formalization.ActualHubPositiveDegree

/-! FULL actual selected-edge triangle incidence: exactly1 for the nine
boundary-ring cycle pairs and exactly2 for every other selected edge.
True positive facets and zero-primal-length artificial diagonals are proved
separately then classified from the actual incident polygon. No disk/Euler
or assumed two-face condition. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSelectedEdgeIncidence
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementSideMultiplicity ActualRefinementInteriorFacetCount
open ActualRefinementBoundaryCount ActualRefinementDiagonalCount ActualLocalRefinementPairCounts
open ActualIncidentPolygonFacets ActualIncidentFacetAdjacency ActualHubPositiveDegree
open ActualPositiveFacetGraph

instance (i j : Fin 11) : Decidable (BoundaryLabels i j) := by
  unfold BoundaryLabels
  infer_instance

theorem boundary_labels_pair_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) {i j : Fin 11}
    (hb : BoundaryLabels i j) : (pairTriangles R i j).card = 1 := by
  classical
  obtain ⟨a,ha⟩ := hb
  rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact actual_boundary_triangle_count h hr R a
  · have he : pairTriangles R (ActualRingDirectionOrder.ringSite (ActualBoundaryCyclicOrder.nextRing a))
        (ActualRingDirectionOrder.ringSite a) = boundaryTriangles R a := by
      ext k
      simp [pairTriangles,boundaryTriangles,and_comm]
    rw [he]
    exact actual_boundary_triangle_count h hr R a

theorem actual_selected_nonboundary_edge_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) {i j : Fin 11}
    (hij : i ≠ j) {a : R.Index}
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a)
    (hnb : ¬ BoundaryLabels i j) : (pairTriangles R i j).card = 2 := by
  let V := a.1
  let F := R.face V
  let o := R.order V
  have hi : i ∈ incident c F.point := mem_incident.mpr (nearest_of_label_mem R hai)
  have hj : j ∈ incident c F.point := mem_incident.mpr (nearest_of_label_mem R haj)
  let I := o.order.symm ⟨i,hi⟩
  let J := o.order.symm ⟨j,hj⟩
  have hI : (o.order I).val = i := congrArg Subtype.val (o.order.apply_symm_apply ⟨i,hi⟩)
  have hJ : (o.order J).val = j := congrArg Subtype.val (o.order.apply_symm_apply ⟨j,hj⟩)
  have hIJ : I ≠ J := by
    intro he
    apply hij
    rw [← hI,← hJ,he]
  have hn : 0 < (incident c (R.face V).point).card :=
    lt_of_lt_of_le (by decide : 0 < 3) (R.face V).at_least_three
  have hIk : I ∈ ActualIncidentFanRefinement.indexTriangle hn a.2.val := by
    apply (local_label_mem R V a.2 I).mp
    change (o.order I).val ∈ labelSet R a
    rwa [hI]
  have hJk : J ∈ ActualIncidentFanRefinement.indexTriangle hn a.2.val := by
    apply (local_label_mem R V a.2 J).mp
    change (o.order J).val ∈ labelSet R a
    rwa [hJ]
  by_cases hadj : Adjacent I J
  · have hp : PositivePair c i j := by
      rcases hadj with hJnext | hInext
      · obtain ⟨g⟩ := ActualIncidentPolygonFacets.OrderedCircle.adjacent_facets o h.cover I
        have hp := facetGerm_positivePair
          ((OrderedCircle.label_injective o).ne (rotate_ne
            (lt_of_lt_of_le (by decide : 1 < 3) F.at_least_three) I)) g
        have he : finRotate (incident c F.point).card I = J := hJnext.symm
        rwa [he,hI,hJ] at hp
      · obtain ⟨g⟩ := ActualIncidentPolygonFacets.OrderedCircle.adjacent_facets o h.cover J
        have hp := facetGerm_positivePair
          ((OrderedCircle.label_injective o).ne (rotate_ne
            (lt_of_lt_of_le (by decide : 1 < 3) F.at_least_three) J)) g
        have he : finRotate (incident c F.point).card J = I := hInext.symm
        rw [he,hI,hJ] at hp
        exact PositivePair.symm hp
    exact actual_positive_interior_pair_count h hr R hp hnb
  · have hh := actual_selected_diagonal_count h.injective R V hIJ hadj a.2.property hIk hJk
    rwa [hI,hJ] at hh

theorem actual_selected_edge_incidence {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) {i j : Fin 11}
    (hij : i ≠ j) {a : R.Index} (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a) :
    (pairTriangles R i j).card = if BoundaryLabels i j then 1 else 2 := by
  classical
  by_cases hb : BoundaryLabels i j
  · rw [if_pos hb]
    exact boundary_labels_pair_count h hr R hb
  · rw [if_neg hb]
    exact actual_selected_nonboundary_edge_count h hr R hij hai haj hb

end N11Formalization.ActualSelectedEdgeIncidence
#check @N11Formalization.ActualSelectedEdgeIncidence.actual_selected_edge_incidence
#print axioms N11Formalization.ActualSelectedEdgeIncidence.actual_selected_nonboundary_edge_count
#print axioms N11Formalization.ActualSelectedEdgeIncidence.actual_selected_edge_incidence
