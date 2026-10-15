import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeRecoveryRootAudit

theorem still_explicit_main_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : ActualMainRoute.Canonical33Obligation) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMainRoute.main_of_remaining h450 henergy h33

theorem still_explicit_full_disk_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point),
      0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r := by
  have H := ActualMetricClassReduction.main_of_seven_class_certificates
    h450 henergy hclasses
  exact (strongInterface_of_n11_main H).bounds

theorem actual_nearest_ear_count {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (s : Finset (Fin 9)) (hs : ∀ i ∈ s, ActualNearestEarExclusion.NearestEar c i) :
    s.card ≤ 1 := ActualNearestEarExclusion.nearest_ears_card_le_one h hr s hs

theorem actual_a19_inputs_remain_explicit
    (H : ActualMetricBridgeAudit.UnpaidMainRouteInputs) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMetricBridgeAudit.main_route_from_a19_audit_inputs H

theorem actual_hub_one_turn {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (R : ActualFiniteNearestRefinement.Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) :
    ActualSiteAngleChain.siteFaceSum R i = 2*Real.pi :=
  ActualHubOneTurn.actual_hub_angle_sum h hr R i hi

theorem actual_shared_side_metric_bridge {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r)
    (R : ActualFiniteNearestRefinement.Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) {i j : Fin 11} (hij : i ≠ j)
    (hAi : i ∈ ActualRefinementTriangleUniqueness.labelSet R A)
    (hAj : j ∈ ActualRefinementTriangleUniqueness.labelSet R A)
    (hBi : i ∈ ActualRefinementTriangleUniqueness.labelSet R B)
    (hBj : j ∈ ActualRefinementTriangleUniqueness.labelSet R B) :
    ∃ s t : Fin 3, ActualSquaredSideMatching.SideAt R A s i j ∧
      ActualSquaredSideMatching.SideAt R B t i j ∧
      ActualSquaredSideMatching.faceSideSquared R A s =
        ActualSquaredSideMatching.faceSideSquared R B t ∧
      ActualMetricAngleAtoms.faceAngle R A s +
        ActualMetricAngleAtoms.faceAngle R B t ≤ Real.pi :=
  ActualDelaunayAngleConsumer.actual_shared_side_metric_producer
    h.injective R hAB hij hAi hAj hBi hBj

theorem actual_metric_angle_data_producer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50) :
    ∃ (R : ActualFiniteNearestRefinement.Refinement c r)
      (v : ActualBoundaryNineTies.NineTies c r),
      (∀ i : Fin 11, 9 ≤ i.val → ActualSiteAngleChain.siteFaceSum R i = 2*Real.pi) ∧
      (∀ i : Fin 9, ActualMetricAngleAtoms.sectorAngle v i +
        ActualSiteAngleChain.siteFaceSum R (ActualRingLinkBoundaryData.nextSite i) -
        ActualBoundarySwitchAngles.SwitchData.angle
          (ActualSwitchAtomAggregate.switchData h hr v i) -
        ActualBoundarySwitchAngles.SwitchData.angle
          (ActualSwitchAtomAggregate.switchData h hr v
            (ActualBoundaryCyclicOrder.nextRing i)) = Real.pi) := by
  obtain ⟨R⟩ := ActualFiniteNearestRefinement.actual_refinement h hr
  obtain ⟨v⟩ := ActualBoundaryNineTies.nineTies_of_cover
    h.cover hr h.labels h.midpoint_order
  exact ⟨R,v,fun i hi => ActualHubOneTurn.actual_hub_angle_sum h hr R i hi,
    fun i => ActualRingAngleClosure.actual_ring_angle_closure h hr R v i⟩

theorem actual_degree_three_envelope_data_producer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50) :
    ∃ (R : ActualFiniteNearestRefinement.Refinement c r)
      (v : ActualBoundaryNineTies.NineTies c r),
      Real.pi = (∑ A : R.Index, ActualSharedFactorArea.faceArea R A) +
        (∑ i : Fin 9, ActualSharedFactorArea.switchArea h hr v i) +
        ∑ i : Fin 9, ActualSharedFactorArea.sectorArea v i ∧
      (∑ i : Fin 9, ActualSharedFactorArea.sectorArea v i) ≤
        ∑ i : Fin 9, ActualSectorAreaEnvelope.areaEnvelope
          (ActualMetricAngleAtoms.sectorAngle v i) ∧
      2*Real.pi ≤ ∑ i : Fin 9, ActualSectorAreaEnvelope.widthEnvelope
        (ActualMetricAngleAtoms.sectorAngle v i) := by
  obtain ⟨R⟩ := ActualFiniteNearestRefinement.actual_refinement h hr
  obtain ⟨v⟩ := ActualBoundaryNineTies.nineTies_of_cover
    h.cover hr h.labels h.midpoint_order
  exact ⟨R,v,ActualSharedFactorArea.actual_shared_factor_area h hr R v,
    ActualSectorAreaEnvelope.actual_total_sector_area_envelope h hr v,
    ActualSectorAreaEnvelope.actual_total_width_envelope h hr v⟩

theorem skew_endpoints_need_max :
    ¬ ((1 : ℝ)^2+0^2-2*1*0*Real.cos 0 ≤ 4*Real.sin (0/2)^2) := by
  norm_num

end N11Formalization.ProbeRecoveryRootAudit

#print N11Formalization.SourceExactRoot.sourceRadius
#print N11Formalization.Covers
#print N11Formalization.N11MainStatement
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeRecoveryRootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeRecoveryRootAudit.still_explicit_full_disk_consumer
#check @N11Formalization.ProbeRecoveryRootAudit.actual_a19_inputs_remain_explicit
#check @N11Formalization.ProbeRecoveryRootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeRecoveryRootAudit.actual_hub_one_turn
#check @N11Formalization.ProbeRecoveryRootAudit.actual_shared_side_metric_bridge
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#print N11Formalization.ActualMetricClassReduction.SevenClassExclusions
#print N11Formalization.C450Source11Segment.RemainingSourceObligation
#print N11Formalization.EnergyTerminalBatchB11.RemainingTerminalRadius
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualDelaunayAngleConsumer.actual_shared_side_cotangent_sum_nonneg
#check @N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_angle_sum_eq_pi
#check @N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_cotangent_sum_eq_zero
#check @N11Formalization.ActualSwitchBaseAngle.actual_switch_base_angles
#check @N11Formalization.ActualSiteAnglePacking.actual_site_face_sum_le_two_pi
#check @N11Formalization.ActualRingAngleClosure.actual_ring_angle_closure
#check @N11Formalization.ProbeRecoveryRootAudit.actual_metric_angle_data_producer
#check @N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_angle_sum_lt_pi
#check @N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_metric_producer
#check @N11Formalization.ActualSectorAreaEnvelope.actual_sector_width_envelope
#check @N11Formalization.ActualSectorAreaEnvelope.actual_sector_area_envelope
#check @N11Formalization.ProbeRecoveryRootAudit.actual_degree_three_envelope_data_producer
#check @N11Formalization.ProbeRecoveryRootAudit.skew_endpoints_need_max
#print axioms N11Formalization.ProbeRecoveryRootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeRecoveryRootAudit.still_explicit_full_disk_consumer
#print axioms N11Formalization.ProbeRecoveryRootAudit.actual_a19_inputs_remain_explicit
#print axioms N11Formalization.ProbeRecoveryRootAudit.actual_hub_one_turn
#print axioms N11Formalization.ProbeRecoveryRootAudit.actual_shared_side_metric_bridge
#print axioms N11Formalization.ActualDelaunayAngleConsumer.actual_shared_side_cotangent_sum_nonneg
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_angle_sum_eq_pi
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_cotangent_sum_eq_zero
#print axioms N11Formalization.ActualSwitchBaseAngle.actual_switch_base_angles
#print axioms N11Formalization.ActualSiteAnglePacking.actual_site_face_sum_le_two_pi
#print axioms N11Formalization.ActualRingAngleClosure.actual_ring_angle_closure
#print axioms N11Formalization.ProbeRecoveryRootAudit.actual_metric_angle_data_producer
#print axioms N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_metric_producer
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_sector_width_envelope
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_sector_area_envelope
#print axioms N11Formalization.ProbeRecoveryRootAudit.actual_degree_three_envelope_data_producer
#print axioms N11Formalization.ProbeRecoveryRootAudit.skew_endpoints_need_max

#check @N11Formalization.ActualEdgeAreaAtoms.actual_face_area_eq_half_side_cotangent_sum
#check @N11Formalization.ActualEdgeAreaAtoms.actual_shared_edge_area_producer
#check @N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_boundary_edge_area_producer
#check @N11Formalization.ActualEdgeFlagSums.actual_site_degree_offset
#check @N11Formalization.ActualEdgeMetricModel.actual_edge_metric_model
#check @N11Formalization.ActualEdgeMetricModel.actual_weighted_angle_balance
#check @N11Formalization.MetricAreaDual.exclude_of_full_domain_certificate
#check @N11Formalization.MetricAreaEnvelopeRegularity.areaEnvelope_difference
#check @N11Formalization.MetricAreaGridCertificate.uniform_grid_cover
#check @N11Formalization.MetricAreaGridDual.exclude_of_grid_certificate
#check @N11Formalization.ActualMetricGridBridge.exclude_representative_of_grid_certificate
#check @N11Formalization.MetricAreaRationalCertificate.exclude_representative_of_rational_certificate
#check @N11Formalization.ActualSwitchPointClosure.actual_switch_point_closure
#check @N11Formalization.ActualSectorEndpointCoordinates.actual_sector_endpoint_scalar_producer
#check @N11Formalization.ActualSectorEndpointCoordinates.actual_switch_point_scalar_closure
#check @N11Formalization.ActualDBMCellEnergyAdapter.Valid
#check @N11Formalization.ActualDBMCellEnergyAdapter.matrix_cell_radius
#check @N11Formalization.ActualDBMCellEnergyAdapter.source_cell_radius_of_refinement
#print axioms N11Formalization.ActualEdgeAreaAtoms.actual_shared_edge_area_producer
#print axioms N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_boundary_edge_area_producer
#print axioms N11Formalization.ActualEdgeFlagSums.actual_site_degree_offset
#print axioms N11Formalization.ActualEdgeMetricModel.actual_edge_metric_model
#print axioms N11Formalization.ActualEdgeMetricModel.actual_weighted_angle_balance
#print axioms N11Formalization.MetricAreaDual.exclude_of_full_domain_certificate
#print axioms N11Formalization.MetricAreaEnvelopeRegularity.areaEnvelope_difference
#print axioms N11Formalization.MetricAreaGridCertificate.uniform_grid_cover
#print axioms N11Formalization.MetricAreaGridDual.exclude_of_grid_certificate
#print axioms N11Formalization.ActualMetricGridBridge.exclude_representative_of_grid_certificate
#print axioms N11Formalization.MetricAreaRationalCertificate.exclude_representative_of_rational_certificate
#print axioms N11Formalization.ActualSwitchPointClosure.actual_switch_point_closure
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_sector_endpoint_scalar_producer
#print axioms N11Formalization.ActualSectorEndpointCoordinates.actual_switch_point_scalar_closure
#print axioms N11Formalization.ActualDBMCellEnergyAdapter.matrix_cell_radius
#print axioms N11Formalization.ActualDBMCellEnergyAdapter.source_cell_radius_of_refinement
