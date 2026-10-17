import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA15RootAudit
theorem still_explicit_main_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : ActualMainRoute.Canonical33Obligation) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMainRoute.main_of_remaining h450 henergy h33

theorem still_explicit_seven_class_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMetricClassReduction.main_of_seven_class_certificates h450 henergy hclasses

theorem actual_nearest_ear_count {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (s : Finset (Fin 9)) (hs : ∀ i ∈ s, ActualNearestEarExclusion.NearestEar c i) :
    s.card ≤ 1 := ActualNearestEarExclusion.nearest_ears_card_le_one h hr s hs

theorem actual_complete_fan_metric_consumer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50) :
    (∃ R : ActualFiniteNearestRefinement.Refinement c r,
      ((ActualRefinementEarCount.ringOnlyTriangles R).card=0 ∧
        ∃ O : ActualQ0OrderedTwoFans.OrderedData R,
          1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4) ∨
      ((ActualRefinementEarCount.ringOnlyTriangles R).card=1 ∧
        ∃ O : ActualQ1OrderedCoreFans.OrderedCoreData R,
          1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4)) ∧
    (∀ i : Fin 9, ∀ U : ActualBoundaryNeighborTies.NeighborTie c r i,
      ∃ S : ActualBoundarySwitchMetric.SwitchData (c (ActualRingDirectionOrder.ringSite i))
        (c (ActualRingLinkBoundaryData.nextSite i)) (circleMap U.angle) r,
        0 < ActualBoundarySwitchAngles.SwitchData.angle S ∧
        ActualBoundarySwitchAngles.SwitchData.angle S < Real.pi/2 ∧
        S.radius^2*Real.sin (2*ActualBoundarySwitchAngles.SwitchData.angle S)/2=S.chord*S.offset) :=
  ⟨ActualFiniteFanFamilies.actual_cover_finite_family_producer h hr,
    ActualBoundarySwitchAngles.actual_switch_angle_and_area h hr⟩
end N11Formalization.ProbeA15RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA15RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA15RootAudit.still_explicit_seven_class_consumer
#check @N11Formalization.ProbeA15RootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeA15RootAudit.actual_complete_fan_metric_consumer
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#print N11Formalization.ActualQ0CanonicalNearestRows.RemainingMetricClassification
#print N11Formalization.ActualMetricClassReduction.Q0RunExclusion
#print N11Formalization.ActualMetricClassReduction.Q1RunExclusion
#print N11Formalization.ActualMetricClassReduction.SevenClassExclusions
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualBoundaryTriangleExterior.actual_boundary_triangle_exterior
#check @N11Formalization.ActualQ1OrderedCoreFans.actual_q1_ordered_core_fans
#check @N11Formalization.ActualQ1FacePartition.actual_q1_all_faces
#check @N11Formalization.ActualQ1RunDegrees.actual_q1_run_degrees
#check @N11Formalization.ActualFiniteFanFamilies.actual_cover_finite_family_producer
#check @N11Formalization.ActualBoundarySwitchAngles.actual_switch_angle_and_area
#check @N11Formalization.ActualMetricClassReduction.actual_metric_classification_of_seven
#print axioms N11Formalization.ProbeA15RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA15RootAudit.still_explicit_seven_class_consumer
#print axioms N11Formalization.ProbeA15RootAudit.actual_complete_fan_metric_consumer
#print axioms N11Formalization.ActualBoundaryTriangleExterior.actual_boundary_triangle_exterior
