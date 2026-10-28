import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA14RootAudit

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

theorem still_explicit_metric_consumer
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hmetric : ActualQ0CanonicalNearestRows.RemainingMetricClassification) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualQ0CanonicalNearestRows.main_of_metric_remaining h450 henergy hmetric

theorem actual_q0_canonical_consumer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (R : ActualFiniteNearestRefinement.Refinement c r)
    (hq : (ActualRefinementEarCount.ringOnlyTriangles R).card=0)
    (hd : min (ActualHubTriangleCensus.neighbors R 9).card
      (ActualHubTriangleCensus.neighbors R 10).card=6 ∧
      max (ActualHubTriangleCensus.neighbors R 9).card
        (ActualHubTriangleCensus.neighbors R 10).card=7) :
    ∃ (k : Fin 9) (e : Equiv.Perm (Fin 11)) (Z : Fin 11 → Point),
      (∀ i : Fin 9, e (ActualRingDirectionOrder.ringSite i)=
        ActualRingDirectionOrder.ringSite (i+k)) ∧
      (∀ f : Fin 11, ‖Z f‖<1) ∧
      ∀ f : Fin 11, ∀ v : Fin 3, Z f ∈ ActualVoronoiCells.Cell c (e (ResumeNetwork.face f v)) ∧
        dist (Z f) (c (e (ResumeNetwork.face f v))) ≤ r :=
  ActualQ0CanonicalNearestRows.actual_q0_six_seven_canonical_nearest h hr R hq hd

theorem actual_q1_core_consumer {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) (hr : r < 19/50)
    (R : ActualFiniteNearestRefinement.Refinement c r)
    (hq : (ActualRefinementEarCount.ringOnlyTriangles R).card=1) :
    Nonempty (ActualQ1CoreFans.CoreFans R) :=
  ActualQ1CoreFans.actual_q1_core_fans h hr R hq

end N11Formalization.ProbeA14RootAudit
#print N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.ProbeA14RootAudit.still_explicit_main_consumer
#check @N11Formalization.ProbeA14RootAudit.actual_nearest_ear_count
#check @N11Formalization.ProbeA14RootAudit.still_explicit_metric_consumer
#check @N11Formalization.ProbeA14RootAudit.actual_q0_canonical_consumer
#check @N11Formalization.ProbeA14RootAudit.actual_q1_core_consumer
#print N11Formalization.ActualMainRoute.Canonical33Obligation
#print N11Formalization.ActualMainRoute.CanonicalNearest33Obligation
#print N11Formalization.ActualQ0CanonicalNearestRows.RemainingMetricClassification
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#check @N11Formalization.ActualIncidentFanRefinement.OrderedCircle.positive_facet_retained
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualQ0OrderedTwoFans.actual_q0_ordered_two_fans
#check @N11Formalization.ActualQ0RunDegrees.actual_q0_run_degrees
#check @N11Formalization.ActualQ0FourRunNormalization.actual_q0_four_run_data
#check @N11Formalization.ActualCanonicalSitePermutation.canonicalPerm_ring
#check @N11Formalization.ActualQ0CanonicalNearestRows.canonical_nearest_of_metric
#print axioms N11Formalization.ProbeA14RootAudit.still_explicit_main_consumer
#print axioms N11Formalization.ProbeA14RootAudit.still_explicit_metric_consumer
#print axioms N11Formalization.ProbeA14RootAudit.actual_q0_canonical_consumer
#print axioms N11Formalization.ProbeA14RootAudit.actual_q1_core_consumer
