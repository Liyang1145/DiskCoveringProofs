import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA10RootAudit

theorem same_coordinate : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl

theorem still_explicit_main_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : ActualMainRoute.Canonical33Obligation) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMainRoute.main_of_remaining h450 henergy h33

theorem actual_nearest_ear_count {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (s : Finset (Fin 9)) (hs : ∀ i ∈ s, ActualNearestEarExclusion.NearestEar c i) :
    s.card ≤ 1 := ActualNearestEarExclusion.nearest_ears_card_le_one h hr s hs

/-- ALL of the displayed finite refinement/graph/count conclusions are
produced, not additional hypotheses on an arbitrary real representative. -/
theorem actual_refinement_count_consumer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50) :
    ∃ R : ActualFiniteNearestRefinement.Refinement c r,
      (ActualRefinementGraphConnected.triangleGraph R).Connected ∧
      (ActualRefinementEarCount.ringOnlyTriangles R).card ≤ 1 ∧
      (ActualRefinementHubCount.hubTriangles R).card = 2 ∧
      ∀ i : Fin 9, (ActualRefinementBoundaryCount.boundaryTriangles R i).card = 1 := by
  obtain ⟨R⟩ := ActualFiniteNearestRefinement.actual_refinement h hr
  exact ⟨R,ActualRefinementGraphConnected.actual_triangle_graph_connected h hr R,
    ActualRefinementEarCount.actual_selected_ear_count h hr R,
    ActualRefinementHubCount.actual_hub_triangle_count h hr R,
    ActualRefinementBoundaryCount.actual_boundary_triangle_count h hr R⟩

end N11Formalization.ProbeA10RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA10RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA10RootAudit.actual_refinement_count_consumer
#check @N11Formalization.ProbeA10RootAudit.actual_nearest_ear_count
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#check @N11Formalization.ActualPuncturedDiskConnected.punctured_disk_pathConnected
#check @N11Formalization.ActualPositiveFacetGraph.positive_cut_edge
#check @N11Formalization.ActualFiniteNearestRefinement.Refinement.real_triangle
#check @N11Formalization.ActualFiniteNearestRefinement.Refinement.triangles_interior_disjoint
#check @N11Formalization.ActualRefinementTriangleUniqueness.labelSet_injective
#check @N11Formalization.ActualRefinementFacetRetention.Refinement.positive_pair_retained
#check @N11Formalization.ActualRefinementFacetRetention.Refinement.hub_edge_two_retained
#check @N11Formalization.ActualHubPositiveDegree.actual_hub_two_ring_neighbors
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualNearestPairRigidity.nonadjacent_diagonal_unique_witness
#print axioms N11Formalization.ProbeA10RootAudit.same_coordinate
#print axioms N11Formalization.ProbeA10RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA10RootAudit.actual_refinement_count_consumer
#print axioms N11Formalization.ActualFiniteNearestRefinement.Refinement.triangles_interior_disjoint
#print axioms N11Formalization.ActualRefinementTriangleUniqueness.labelSet_injective
#print axioms N11Formalization.ActualNearestPairRigidity.nonadjacent_diagonal_unique_witness
