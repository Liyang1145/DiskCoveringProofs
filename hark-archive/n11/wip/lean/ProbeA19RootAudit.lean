import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA19RootAudit

theorem still_explicit_main_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : ActualMainRoute.Canonical33Obligation) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMainRoute.main_of_remaining h450 henergy h33

theorem actual_a19_inputs_remain_explicit
    (H : ActualMetricBridgeAudit.UnpaidMainRouteInputs) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMetricBridgeAudit.main_route_from_a19_audit_inputs H

theorem exact_site_turn_of_bound {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r)
    (hr : r < 19/50) (R : ActualFiniteNearestRefinement.Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val)
    (hupper : ActualSiteAngleChain.siteFaceSum R i ≤ 2*Real.pi) :
    ActualSiteAngleChain.siteFaceSum R i = 2*Real.pi :=
  ActualHubAngleSum.hub_sum_eq_two_pi_of_upper h hr R i hi hupper

end N11Formalization.ProbeA19RootAudit

#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA19RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA19RootAudit.actual_a19_inputs_remain_explicit
#check @N11Formalization.ActualMetricBridgeAudit.a19_area_data_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_shared_factor_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_width_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_boundary_side_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_small_degree_angle_bridge
#check @N11Formalization.ActualSiteAngleChain.actual_hub_positive_integer_turns
#check @N11Formalization.ActualSiteAngleChain.actual_all_site_face_sum
#check @N11Formalization.ProbeA19RootAudit.exact_site_turn_of_bound
#check @N11Formalization.ActualHubAngleSum.sum_interval_lengths_le_period
#print N11Formalization.ActualMetricClassReduction.SevenClassExclusions
#print N11Formalization.C450Source11Segment.RemainingSourceObligation
#print N11Formalization.EnergyTerminalBatchB11.RemainingTerminalRadius
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#print axioms N11Formalization.ProbeA19RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA19RootAudit.actual_a19_inputs_remain_explicit
#print axioms N11Formalization.ProbeA19RootAudit.exact_site_turn_of_bound
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_area_data_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_shared_factor_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_width_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_boundary_side_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_small_degree_angle_bridge
#print axioms N11Formalization.ActualHubAngleSum.hub_sum_eq_two_pi_of_upper
#print axioms N11Formalization.ActualHubAngleSum.sum_interval_lengths_le_period
