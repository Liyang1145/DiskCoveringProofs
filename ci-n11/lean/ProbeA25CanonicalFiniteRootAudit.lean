import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA25CanonicalFiniteRootAudit

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

end N11Formalization.ProbeA25CanonicalFiniteRootAudit

#print N11Formalization.SourceExactRoot.sourceRadius
#print N11Formalization.Covers
#print N11Formalization.N11MainStatement
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.still_explicit_full_disk_consumer
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_a19_inputs_remain_explicit
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_hub_one_turn
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_shared_side_metric_bridge
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
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_metric_angle_data_producer
#check @N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_angle_sum_lt_pi
#check @N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_metric_producer
#check @N11Formalization.ActualSectorAreaEnvelope.actual_sector_width_envelope
#check @N11Formalization.ActualSectorAreaEnvelope.actual_sector_area_envelope
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_degree_three_envelope_data_producer
#check @N11Formalization.ProbeA25CanonicalFiniteRootAudit.skew_endpoints_need_max
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.still_explicit_full_disk_consumer
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_a19_inputs_remain_explicit
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_hub_one_turn
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_shared_side_metric_bridge
#print axioms N11Formalization.ActualDelaunayAngleConsumer.actual_shared_side_cotangent_sum_nonneg
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_angle_sum_eq_pi
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_cotangent_sum_eq_zero
#print axioms N11Formalization.ActualSwitchBaseAngle.actual_switch_base_angles
#print axioms N11Formalization.ActualSiteAnglePacking.actual_site_face_sum_le_two_pi
#print axioms N11Formalization.ActualRingAngleClosure.actual_ring_angle_closure
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_metric_angle_data_producer
#print axioms N11Formalization.ActualBoundaryDelaunayAngle.actual_boundary_side_metric_producer
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_sector_width_envelope
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_sector_area_envelope
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.actual_degree_three_envelope_data_producer
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.skew_endpoints_need_max

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

#check @N11Formalization.ActualOrderedMetricGraphs.actual_q0_degree_three_table_graph
#check @N11Formalization.ActualOrderedMetricGraphs.actual_q1_degree_three_table_graph
#check @N11Formalization.ActualEarOwnedWidth.actual_ear_owned_width
#check @N11Formalization.ActualEarOwnedWidth.actual_selected_ear_outside_envelope
#check @N11Formalization.MetricAreaMaskedGridDual.exclude_of_masked_grid_certificate
#check @N11Formalization.ActualEarMaskedGridBridge.exclude_selected_ear_of_masked_grid_certificate
#check @N11Formalization.MetricAreaMaskedRationalCertificate.exclude_selected_ear_of_rational_certificate
#check @N11Formalization.ActualSharedMomentData.actual_side_moment_cancellation
#check @N11Formalization.ActualSharedMomentData.actual_copy_moment_cancellation
#check @N11Formalization.MetricSectorCompactRegularity.chordLength_difference
#check @N11Formalization.CompactBoxGridCertificate.weighted_box_upper_of_grid
#check @N11Formalization.MetricSectorBoxCertificate.actual_sector_box_upper_of_grid
#check @N11Formalization.ActualSharedMomentDual.actual_weighted_station_balance
#check @N11Formalization.ActualSharedMomentDual.actual_moment_factor_sum
#check @N11Formalization.ActualSharedMomentDual.exclude_of_full_domain_moment_certificate
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q0_degree_three_table_graph
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q1_degree_three_table_graph
#print axioms N11Formalization.ActualEarOwnedWidth.actual_ear_owned_width
#print axioms N11Formalization.ActualEarOwnedWidth.actual_selected_ear_outside_envelope
#print axioms N11Formalization.MetricAreaMaskedGridDual.exclude_of_masked_grid_certificate
#print axioms N11Formalization.MetricAreaMaskedRationalCertificate.exclude_selected_ear_of_rational_certificate
#print axioms N11Formalization.ActualSharedMomentData.actual_side_moment_cancellation
#print axioms N11Formalization.ActualSharedMomentData.actual_copy_moment_cancellation
#print axioms N11Formalization.MetricSectorCompactRegularity.chordLength_difference
#print axioms N11Formalization.CompactBoxGridCertificate.weighted_box_upper_of_grid
#print axioms N11Formalization.MetricSectorBoxCertificate.actual_sector_box_upper_of_grid
#print axioms N11Formalization.ActualSharedMomentDual.actual_weighted_station_balance
#print axioms N11Formalization.ActualSharedMomentDual.actual_moment_factor_sum
#print axioms N11Formalization.ActualSharedMomentDual.exclude_of_full_domain_moment_certificate

#check @N11Formalization.ActualSharedMomentMaskedDual.actual_masked_moment_area_bound
#check @N11Formalization.ActualSharedMomentMaskedDual.sector_factor_upper_of_grid
#check @N11Formalization.ActualSharedMomentMaskedDual.exclude_of_full_domain_masked_moment_certificate
#print axioms N11Formalization.ActualSharedMomentMaskedDual.actual_masked_moment_area_bound
#print axioms N11Formalization.ActualSharedMomentMaskedDual.sector_factor_upper_of_grid
#print axioms N11Formalization.ActualSharedMomentMaskedDual.exclude_of_full_domain_masked_moment_certificate

namespace N11Formalization.ProbeA25CanonicalFiniteRootAudit
theorem coincident_endpoint_retained :
    MetricSectorCompactRegularity.chordLength 0 1 1 = 0 := by
  norm_num [MetricSectorCompactRegularity.chordLength]
theorem unequal_endpoint_zero_angle_chord :
    MetricSectorCompactRegularity.chordLength 0 1 0 = 1 := by
  norm_num [MetricSectorCompactRegularity.chordLength]
theorem wrap_ear_owners_retained :
    ActualEarOwnedWidth.earGaps 0 = ({7,8,0} : Finset (Fin 9)) := by
  decide +kernel
end N11Formalization.ProbeA25CanonicalFiniteRootAudit
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.coincident_endpoint_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.unequal_endpoint_zero_angle_chord
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.wrap_ear_owners_retained

#check @N11Formalization.CompactQuadraticMomentMaximum.quad_le_maximum
#check @N11Formalization.CompactQuadraticMomentMaximum.maximum_attained
#check @N11Formalization.CompactQuadraticMomentMaximum.maximum_cast
#check @N11Formalization.CompactQuadraticMomentMaximum.maximum_lipschitz
#check @N11Formalization.CompactSimplexGridCertificate.pi_simplex_upper_of_grid
#check @N11Formalization.SharedMomentFactorGridCertificate.face_full_domain_upper_of_grid
#check @N11Formalization.SharedMomentFactorGridCertificate.switch_full_domain_upper_of_grid
#check @N11Formalization.SharedMomentFactorRationalNodes.face_full_domain_upper_of_rational_certificate
#check @N11Formalization.SharedMomentFactorRationalNodes.switch_full_domain_upper_of_rational_certificate
#check @N11Formalization.MetricSectorRationalNodes.sector_upper_of_node
#check @N11Formalization.MetricSectorRationalNodes.sector_box_upper_of_rational_certificate
#check @N11Formalization.ActualSharedMomentRationalCertificate.maskBalanced_of_rational
#check @N11Formalization.ActualSharedMomentRationalCertificate.face_factor_eq_objective
#check @N11Formalization.ActualSharedMomentRationalCertificate.switch_factor_eq_objective
#check @N11Formalization.ActualSharedMomentRationalCertificate.dualConstant_upper
#check @N11Formalization.ActualSharedMomentRationalCertificate.exclude_of_rational_certificate
#print axioms N11Formalization.CompactQuadraticMomentMaximum.quad_le_maximum
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_attained
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_cast
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_lipschitz
#print axioms N11Formalization.CompactSimplexGridCertificate.pi_simplex_upper_of_grid
#print axioms N11Formalization.SharedMomentFactorGridCertificate.face_full_domain_upper_of_grid
#print axioms N11Formalization.SharedMomentFactorGridCertificate.switch_full_domain_upper_of_grid
#print axioms N11Formalization.SharedMomentFactorRationalNodes.face_full_domain_upper_of_rational_certificate
#print axioms N11Formalization.SharedMomentFactorRationalNodes.switch_full_domain_upper_of_rational_certificate
#print axioms N11Formalization.MetricSectorRationalNodes.sector_upper_of_node
#print axioms N11Formalization.MetricSectorRationalNodes.sector_box_upper_of_rational_certificate
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.maskBalanced_of_rational
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.face_factor_eq_objective
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.switch_factor_eq_objective
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.dualConstant_upper
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.exclude_of_rational_certificate

namespace N11Formalization.ProbeA25CanonicalFiniteRootAudit
theorem interior_radius_maximum_retained :
    CompactQuadraticMomentMaximum.maximum (-1) 1 = (1/4 : ℝ) ∧
      max (CompactQuadraticMomentMaximum.quad (-1) 1 0)
        (CompactQuadraticMomentMaximum.quad (-1) 1 1) <
          CompactQuadraticMomentMaximum.quad (-1) 1 (1/2) := by
  norm_num [CompactQuadraticMomentMaximum.maximum,CompactQuadraticMomentMaximum.quad]

theorem signed_width_lower_bracket_retained (B : MetricSectorRationalNodes.NodeBounds) :
    MetricSectorRationalNodes.signedWidthUpperQ (-1) B = -2*B.halfWidthLo := by
  norm_num [MetricSectorRationalNodes.signedWidthUpperQ]

theorem zero_chord_rational_node_retained :
    MetricSectorRationalNodes.NodeValid 0 1 1 ⟨0,0,0,0⟩ := by
  constructor <;>
    norm_num [MetricSectorRationalNodes.chordSqLoQ,MetricSectorRationalNodes.chordSqHiQ,
      sinLoNLag,sinHiNLag,cosLoNLag,cosHiNLag,sinTQ,cosTQ,Finset.sum_range_succ]
end N11Formalization.ProbeA25CanonicalFiniteRootAudit
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.interior_radius_maximum_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.signed_width_lower_bracket_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.zero_chord_rational_node_retained

#check @N11Formalization.RationalBoxSubdivision.split_cover
#check @N11Formalization.RationalBoxSubdivision.certificate_sound
#check @N11Formalization.SharedMomentFactorLocalCertificate.face_upper_of_local_certificate
#check @N11Formalization.SharedMomentFactorLocalCertificate.switch_upper_of_local_certificate
#check @N11Formalization.MetricSectorLocalCertificate.cell_upper_of_rational_certificate
#check @N11Formalization.MetricSectorLocalCertificate.subdivision_upper_of_rational_certificate
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.face_not_outside
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.face_upper_of_tree
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.switch_upper_of_tree
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.sector_upper_of_tree
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_adaptive_rational_certificate
#print axioms N11Formalization.RationalBoxSubdivision.split_cover
#print axioms N11Formalization.RationalBoxSubdivision.certificate_sound
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.face_upper_of_local_certificate
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.switch_upper_of_local_certificate
#print axioms N11Formalization.MetricSectorLocalCertificate.cell_upper_of_rational_certificate
#print axioms N11Formalization.MetricSectorLocalCertificate.subdivision_upper_of_rational_certificate
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.face_not_outside
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.face_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.switch_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.sector_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_adaptive_rational_certificate

namespace N11Formalization.ProbeA25CanonicalFiniteRootAudit
open RationalBoxSubdivision
def testRoot : Cell (Fin 1) := fun _ => ⟨0,1⟩

theorem cut_boundary_retained :
    Mem (leftChild testRoot 0 (1/2)) (fun _ => (1/2 : ℝ)) ∧
      Mem (rightChild testRoot 0 (1/2)) (fun _ => (1/2 : ℝ)) := by
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [Mem,leftChild,rightChild,testRoot,Function.update_self,
      RatInterval.Mem,RatInterval.toSet]

theorem left_child_alone_misses_right :
    ¬ Mem (leftChild testRoot 0 (1/2)) (fun _ => (1 : ℝ)) := by
  intro h
  have hh := h 0
  norm_num [leftChild,testRoot,Function.update_self,RatInterval.Mem,RatInterval.toSet] at hh

theorem degenerate_axis_retained :
    halfWidth (fun _ : Fin 1 => (⟨0,0⟩ : RatInterval)) 0 = 0 ∧
      Mem (fun _ : Fin 1 => (⟨0,0⟩ : RatInterval)) (fun _ => (0 : ℝ)) := by
  constructor
  · norm_num [halfWidth]
  · intro i
    norm_num [RatInterval.Mem,RatInterval.toSet]

theorem below_triangle_plane_pruned :
    ActualSharedMomentAdaptiveCertificate.FaceOutside (fun _ => (⟨0,0⟩ : RatInterval)) := by
  right
  norm_num [RatInterval.piLo,Fin.sum_univ_three]
end N11Formalization.ProbeA25CanonicalFiniteRootAudit
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.cut_boundary_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.left_child_alone_misses_right
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.degenerate_axis_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.below_triangle_plane_pruned

#check @N11Formalization.ActualSharedMomentUnmaskedDual.actual_unmasked_moment_area_bound
#check @N11Formalization.ActualSharedMomentUnmaskedDual.exclude_of_full_domain_unmasked_moment_certificate
#check @N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate
#print axioms N11Formalization.ActualSharedMomentUnmaskedDual.actual_unmasked_moment_area_bound
#print axioms N11Formalization.ActualSharedMomentUnmaskedDual.exclude_of_full_domain_unmasked_moment_certificate
#print axioms N11Formalization.ActualSharedMomentAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate

#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_mem
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_mem
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_attained
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_attained
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximizer_bounds
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximizer_corner_enclosure
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_cast
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_cast
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArgQ_nonneg
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArgQ_le_one
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArgQ_nonneg
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArgQ_le_one
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximizer_rational_enclosure
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximum_attained_with_rational_enclosure
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximum_attained_with_rational_upper
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_endpoint_tie
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_endpoint_tie
#print axioms N11Formalization.CompactQuadraticArgmaxRange.zero_coefficients_all_maximizers

#print axioms N11Formalization.RationalTrigCellBounds.distance_le_halfWidth
#print axioms N11Formalization.RationalTrigCellBounds.sinCell_mem
#print axioms N11Formalization.RationalTrigCellBounds.cosCell_mem
#print axioms N11Formalization.RationalTrigCellBounds.squareCell_mem
#print axioms N11Formalization.RationalTrigCellBounds.sinCell_valid
#print axioms N11Formalization.RationalTrigCellBounds.cosCell_valid
#print axioms N11Formalization.RationalTrigCellBounds.squareCell_valid

#check @N11Formalization.SharedMomentFactorIntervalCertificate.face_upper_of_direct_certificate
#check @N11Formalization.SharedMomentFactorIntervalCertificate.switch_upper_of_direct_certificate
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_quadratic_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_linear_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_angle_linear_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_envelope_le_direct_upper
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_upper_of_direct_certificate
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_quadratic_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_linear_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_envelope_le_direct_upper
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_upper_of_direct_certificate

#check @N11Formalization.SharedMomentActiveRadiusCertificate.face_upper_of_active_certificate
#check @N11Formalization.SharedMomentActiveRadiusCertificate.switch_upper_of_active_certificate
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.face_objective_change_le_active
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.face_envelope_le_active_upper
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.face_upper_of_active_certificate
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.switch_objective_change_le_active
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.switch_envelope_le_active_upper
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.switch_upper_of_active_certificate

#check @N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_adaptive_rational_certificate
#check @N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.face_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.switch_upper_of_tree
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_adaptive_rational_certificate
#print axioms N11Formalization.ActualSharedMomentTightAdaptiveCertificate.exclude_of_unmasked_adaptive_rational_certificate

namespace N11Formalization.ProbeA25CanonicalFiniteRootAudit
open CompactQuadraticArgmaxRange RationalTrigCellBounds SharedMomentActiveRadiusCertificate

theorem strict_interior_radius_retained : upperArgQ (-1) 1 = (1/2 : ℚ) := by
  norm_num [upperArgQ]

theorem endpoint_tie_retained : lowerArgQ 1 (-1) = 0 ∧ upperArgQ 1 (-1) = 1 := by
  norm_num [lowerArgQ,upperArgQ]

theorem flat_all_radii_retained : lowerArgQ 0 0 = 0 ∧ upperArgQ 0 0 = 1 := by
  norm_num [lowerArgQ,upperArgQ]

theorem endpoint_zero_and_one_retained : upperArgQ (-1) 0 = 0 ∧ upperArgQ (-1) 2 = 1 := by
  norm_num [upperArgQ]

theorem square_crossing_zero_retained : squareCell ⟨-1,1⟩ = ⟨0,1⟩ := by
  norm_num [squareCell]

theorem square_negative_interval_retained : squareCell ⟨-2,-1⟩ = ⟨1,4⟩ := by
  norm_num [squareCell]

theorem zero_active_radius_keeps_angle_cost (p q b : Fin 3 → ℚ) (s : Fin 3) :
    faceActiveLipschitzQ p q b 0 s = |p s| := by
  norm_num [faceActiveLipschitzQ]

theorem zero_switch_radius_keeps_angle_cost (p q b : ℚ) :
    switchActiveLipschitzQ p q b 0 = |p| := by
  norm_num [switchActiveLipschitzQ]
end N11Formalization.ProbeA25CanonicalFiniteRootAudit
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.strict_interior_radius_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.endpoint_tie_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.flat_all_radii_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.endpoint_zero_and_one_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.square_crossing_zero_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.square_negative_interval_retained
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.zero_active_radius_keeps_angle_cost
#print axioms N11Formalization.ProbeA25CanonicalFiniteRootAudit.zero_switch_radius_keeps_angle_cost


#check @N11Formalization.ActualCanonicalFaceCoordinates.q0Coordinates
#check @N11Formalization.ActualCanonicalFaceCoordinates.q1Coordinates
#check @N11Formalization.CanonicalSharedMomentFiniteCertificate.SevenFiniteTables
#check @N11Formalization.CanonicalSharedMomentFiniteCertificate.full_disk_bound_of_finite_class_tables
#check @N11Formalization.CanonicalSharedMomentOrbitTransport.balanced_certificates_of_two
#print axioms N11Formalization.SharedMomentFactorPermutation.face_upper_of_permuted_coefficients
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.q0Coordinates
#print axioms N11Formalization.ActualCanonicalFaceCoordinates.q1Coordinates
#print axioms N11Formalization.ActualCanonicalMomentTransport.maskBalanced_pullback
#print axioms N11Formalization.ActualCanonicalMomentTransport.constantCoeffQ_pullback
#print axioms N11Formalization.ActualSharedMomentSharpConstant.ear_asin_863314
#print axioms N11Formalization.ActualSharedMomentSharpConstant.dualConstant_upper_of_bracket
#print axioms N11Formalization.RationalTrigLocalLipschitz.image_sub_le_of_derivative_mem
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_path_hasDerivAt
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_fixed_radius_difference
#print axioms N11Formalization.SharedMomentFacePlaneCertificate.face_upper_of_plane_tree
#print axioms N11Formalization.SharedMomentFacePlaneDirectCertificate.face_upper_of_direct_plane_tree
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.plane_fixed_radius_difference
#print axioms N11Formalization.SharedMomentFacePlaneGradientCertificate.face_upper_of_gradient_plane_tree
#print axioms N11Formalization.SharedMomentFacePlaneRoundedGradientCertificate.face_upper_of_rounded_plane_tree
#print axioms N11Formalization.MetricSectorRationalCellCertificate.qCell_mem
#print axioms N11Formalization.MetricSectorRationalCellCertificate.width_bounds_of_cell
#print axioms N11Formalization.MetricSectorRationalCellCertificate.sector_upper_of_direct_certificate
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.sector_path_hasDerivAt
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.PositiveCertificate.sound
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.FaceCertificate.sound
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.SwitchCertificate.sound
#print axioms N11Formalization.SharedMomentFiniteFactorCertificate.SectorCertificate.sound
#print axioms N11Formalization.SharedMomentEfficientFactorCertificate.EfficientSectorCertificate.sound
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q0_ordered
#print axioms N11Formalization.ActualCanonicalSharedMomentConsumer.exclude_q1_ordered
#print axioms N11Formalization.CanonicalBalancedGraphOrbits.balanced_orbit
#print axioms N11Formalization.CanonicalSharedMomentOrbitTransport.balanced_certificates_of_two
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.q0_run_exclusion_of_finite
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.q1_run_exclusion_of_finite
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.seven_class_exclusions_of_finite
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.full_disk_bound_of_finite_class_tables