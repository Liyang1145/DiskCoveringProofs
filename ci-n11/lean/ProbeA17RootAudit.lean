import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA17RootAudit
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

theorem still_explicit_seven_class_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMetricClassReduction.main_of_seven_class_certificates h450 henergy hclasses

theorem actual_shoelace_and_segments {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (R : ActualFiniteNearestRefinement.Refinement c r) :
    (∑ A : R.Index, FlashTiling.orient (c (R.labels A 0)) (c (R.labels A 1))
      (c (R.labels A 2))) =
      ∑ i : Fin 9, FlashTiling.det2 (c (ActualRingDirectionOrder.ringSite i))
        (c (ActualRingLinkBoundaryData.nextSite i)) :=
  ActualCenterRingShoelace.actual_center_ring_shoelace h hr R

end N11Formalization.ProbeA17RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA17RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA17RootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeA17RootAudit.still_explicit_seven_class_consumer
#check @N11Formalization.ProbeA17RootAudit.actual_shoelace_and_segments
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#print N11Formalization.ActualMetricClassReduction.SevenClassExclusions
#check @N11Formalization.ActualCircleSegmentAlgebra.segmentTerm_sum_widths
#check @N11Formalization.ActualCircleSegmentAlgebra.segmentTerm_nonneg
#check @N11Formalization.ActualCircleSegmentAlgebra.switchAtom_is_chord_offset
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#print N11Formalization.C450Source11Segment.RemainingSourceObligation
#print N11Formalization.EnergyTerminalBatchB11.RemainingTerminalRadius
#print axioms N11Formalization.ProbeA17RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA17RootAudit.still_explicit_seven_class_consumer
#print axioms N11Formalization.ProbeA17RootAudit.actual_shoelace_and_segments
