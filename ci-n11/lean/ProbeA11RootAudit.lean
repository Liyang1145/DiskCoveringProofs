import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA11RootAudit

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

theorem actual_edge_and_paths_consumer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50) :
    ∃ (R : ActualFiniteNearestRefinement.Refinement c r)
      (P : ActualHubRingPaths.RingPath R 9 10)
      (Q : ActualHubRingPaths.RingPath R 10 9),
      ({P.first,P.last} : Finset (Fin 11)) = {Q.first,Q.last} ∧
      3*Fintype.card R.Index+9 = 2*(ActualRefinementDoubleCounting.edges R).card ∧
      ∀ i j : Fin 11, i ≠ j → ∀ a : R.Index,
        i ∈ ActualRefinementTriangleUniqueness.labelSet R a →
        j ∈ ActualRefinementTriangleUniqueness.labelSet R a →
        (ActualRefinementInteriorFacetCount.pairTriangles R i j).card =
          if ActualRefinementInteriorFacetCount.BoundaryLabels i j then 1 else 2 := by
  obtain ⟨R⟩ := ActualFiniteNearestRefinement.actual_refinement h hr
  obtain ⟨P,Q,hends⟩ := ActualCentralRingEndpoints.actual_two_paths_common_endpoints h hr R
  refine ⟨R,P,Q,hends,ActualRefinementDoubleCounting.actual_triangle_edge_double_count h hr R,?_⟩
  intro i j hij a hai haj
  exact ActualSelectedEdgeIncidence.actual_selected_edge_incidence h hr R hij hai haj

end N11Formalization.ProbeA11RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA11RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA11RootAudit.actual_refinement_count_consumer
#check @N11Formalization.ProbeA11RootAudit.actual_nearest_ear_count
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ProbeA11RootAudit.actual_edge_and_paths_consumer
#check @N11Formalization.ActualHubLinkCycles.actual_hub_cycle_through_other_hub
#check @N11Formalization.ActualHubRingPaths.actual_two_ring_paths
#check @N11Formalization.ActualCentralRingEndpoints.actual_central_labels
#print axioms N11Formalization.ProbeA11RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA11RootAudit.actual_edge_and_paths_consumer
#print axioms N11Formalization.ActualHubLinkConnected.actual_hub_link_reachable
#print axioms N11Formalization.ActualCentralRingEndpoints.actual_two_paths_common_endpoints
