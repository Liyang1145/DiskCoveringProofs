import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA9RootAudit

theorem same_coordinate : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl

theorem still_explicit_main_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : ActualMainRoute.Canonical33Obligation) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMainRoute.main_of_remaining h450 henergy h33

/-- Real producer consumer: no additional noAdjacent premise. -/
theorem actual_nearest_ear_count {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (s : Finset (Fin 9)) (hs : ∀ i ∈ s, ActualNearestEarExclusion.NearestEar c i) :
    s.card ≤ 1 := ActualNearestEarExclusion.nearest_ears_card_le_one h hr s hs

end N11Formalization.ProbeA9RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA9RootAudit.still_explicit_main_consumer
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#check @N11Formalization.ActualVoronoiLocalFan.local_normal_fan
#check @N11Formalization.ActualIncidentPolygonOrder.InteriorFace.orderedCircle
#check @N11Formalization.ActualIncidentPolygonFacets.actual_incident_polygon_facets
#check @N11Formalization.ActualIncidentFacetAdjacency.OrderedCircle.positive_facet_adjacent
#check @N11Formalization.ActualClippedFacetIntervals.clippedCommon_interval
#check @N11Formalization.ActualClippedMeshVertices.mesh_vertices_finite
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.hull_selected_cover
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.selected_nearest
#check @N11Formalization.ActualBoundaryFacetUniqueness.neighbor_nearest_vertex_unique
#check @N11Formalization.ProbeA9RootAudit.actual_nearest_ear_count
#check @N11Formalization.ActualNearestRingTriangles.nearest_ring_triangles_same_set
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#print axioms N11Formalization.ProbeA9RootAudit.same_coordinate
#print axioms N11Formalization.ProbeA9RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA9RootAudit.actual_nearest_ear_count
#print axioms N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#print axioms N11Formalization.ActualIncidentFanRefinement.OrderedCircle.hull_selected_cover
#print axioms N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#print axioms N11Formalization.ActualNearestRingTriangles.nearest_ring_triangles_same_set
#print axioms N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
