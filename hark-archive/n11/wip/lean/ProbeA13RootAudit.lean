import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA13RootAudit

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

theorem actual_refinement_euler_consumer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50) :
    ∃ (R : ActualFiniteNearestRefinement.Refinement c r)
      (P : ActualHubRingPaths.RingPath R 9 10)
      (Q : ActualHubRingPaths.RingPath R 10 9),
      Fintype.card R.Index = 11 ∧
      (ActualRefinementDoubleCounting.edges R).card = 21 ∧
      (ActualHubTriangleCensus.ringNeighbors R 9 ∩
        ActualHubTriangleCensus.ringNeighbors R 10) = {P.first,P.last} ∧
      P.walk.length+Q.walk.length+(ActualRefinementEarCount.ringOnlyTriangles R).card = 9 ∧
      ∀ a : R.Index, ‖R.witness a‖ < 1 ∧ ∀ v : Fin 3,
        R.witness a ∈ ActualVoronoiCells.Cell c (R.labels a v) ∧
        dist (R.witness a) (c (R.labels a v)) ≤ r := by
  obtain ⟨R⟩ := ActualFiniteNearestRefinement.actual_refinement h hr
  obtain ⟨P⟩ := (ActualHubRingPaths.actual_two_ring_paths h hr R).1
  obtain ⟨Q⟩ := (ActualHubRingPaths.actual_two_ring_paths h hr R).2
  exact ⟨R,P,Q,ActualRefinementEulerCount.actual_faces_eleven h hr R,
    ActualRefinementEulerCount.actual_edges_twenty_one h hr R,
    ActualHubPathCounts.actual_common_neighbors_are_endpoints h hr R P,
    ActualHubPathCounts.actual_ring_path_edge_count h hr R P Q,
    fun a => ⟨(ActualFiniteNearestRefinement.Refinement.real_triangle R a).1,
      (ActualFiniteNearestRefinement.Refinement.real_triangle R a).2.1⟩⟩

end N11Formalization.ProbeA13RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA13RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA13RootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeA13RootAudit.actual_refinement_euler_consumer
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualSelectedSkipChordEar.actual_selected_skip_chord_ear
#check @N11Formalization.ActualRefinementEulerCount.actual_faces_eleven
#check @N11Formalization.ActualRefinementEulerCount.actual_edges_twenty_one
#check @N11Formalization.ActualHubPathCounts.actual_common_neighbors_are_endpoints
#check @N11Formalization.ActualHubPathCounts.actual_ring_path_edge_count
#check @N11Formalization.ActualHubPathCounts.actual_hub_degree_sum
#check @N11Formalization.ActualHubDegreeClasses.actual_q0_q1_degree_classes
#print axioms N11Formalization.ProbeA13RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA13RootAudit.actual_refinement_euler_consumer
#print axioms N11Formalization.ActualSelectedSkipChordEar.actual_selected_skip_chord_ear
#print axioms N11Formalization.ActualHubPathCounts.actual_common_neighbors_are_endpoints
#print axioms N11Formalization.ActualHubDegreeClasses.actual_q0_q1_degree_classes
