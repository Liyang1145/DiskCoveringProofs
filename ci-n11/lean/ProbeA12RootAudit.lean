import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA12RootAudit
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

theorem actual_local_surface_consumer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50) :
    Nonempty (ActualLocalSurfaceData.LocalData c r) :=
  ActualLocalSurfaceData.actual_local_data h hr
end N11Formalization.ProbeA12RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA12RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA12RootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeA12RootAudit.actual_local_surface_consumer
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualRingLinkConnected.actual_all_site_links_reachable
#check @N11Formalization.ActualRingLinkSimplePaths.actual_ring_link_simple_path
#check @N11Formalization.ActualLocalSurfaceData.actual_local_data
#print N11Formalization.ActualLocalSurfaceData.LocalData
#print axioms N11Formalization.ProbeA12RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA12RootAudit.actual_local_surface_consumer
#print axioms N11Formalization.ActualRingLinkConnected.actual_all_site_links_reachable
#print axioms N11Formalization.ActualRingLinkSimplePaths.actual_ring_link_simple_path
