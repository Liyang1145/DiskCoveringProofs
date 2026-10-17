import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA18RootAudit

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

/-- Exact zero-height local chord control. A closed-sector theorem may
not replace its nonnegative determinant with a strictly positive one. -/
theorem flat_chord_fixture (d : ℝ) :
    FlashTiling.orient (Real.cos d • circleMap 0) (circleMap (-d)) (circleMap d)=0 := by
  have hh := ActualOwnedChordGeometry.center_chord_orientation
    (Real.cos d • circleMap 0) 0 d
  simpa only [zero_sub,zero_add,real_inner_smul_left,inner_circleMap,sub_self,
    Real.cos_zero,mul_one,sub_self,mul_zero] using hh

end N11Formalization.ProbeA18RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA18RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA18RootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeA18RootAudit.still_explicit_seven_class_consumer
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#print N11Formalization.ActualMetricClassReduction.SevenClassExclusions
#print N11Formalization.C450Source11Segment.RemainingSourceObligation
#print N11Formalization.EnergyTerminalBatchB11.RemainingTerminalRadius
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_positive
#check @N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_sum
#check @N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_floor
#check @N11Formalization.ActualOwnershipSwitchWidths.actual_weakLift_eq_switch_interval
#check @N11Formalization.ActualOwnedChordGeometry.actual_owned_chord_triangle_nonneg
#check @N11Formalization.ActualSwitchWedgeArea.actual_switch_wedge_equals_atom
#check @N11Formalization.ActualOwnedSectorDecomposition.actual_disk_atom_decomposition
#check @N11Formalization.ActualOwnedSectorDecomposition.actual_area_data_producer
#check @N11Formalization.ProbeA18RootAudit.flat_chord_fixture
#print axioms N11Formalization.ProbeA18RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA18RootAudit.still_explicit_seven_class_consumer
#print axioms N11Formalization.ProbeA18RootAudit.flat_chord_fixture
#print axioms N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_floor
#print axioms N11Formalization.ActualOwnershipSwitchWidths.actual_weakLift_eq_switch_interval
#print axioms N11Formalization.ActualOwnedChordGeometry.actual_owned_chord_triangle_nonneg
#print axioms N11Formalization.ActualSwitchWedgeArea.actual_switch_wedge_equals_atom
#print axioms N11Formalization.ActualOwnedSectorDecomposition.actual_disk_atom_decomposition
#print axioms N11Formalization.ActualOwnedSectorDecomposition.actual_area_data_producer
