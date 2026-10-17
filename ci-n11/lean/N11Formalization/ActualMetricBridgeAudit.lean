import N11Formalization.ActualMetricClassReduction
import N11Formalization.ActualSiteAngleChain
import N11Formalization.ActualSharedFactorArea
import N11Formalization.ActualSquaredSideMatching

/-! Audit-only bridge for the A19 actual metric atoms.

This module records exactly which A19 facts can be consumed by a future
numeric exclusion proof and which obligations are still explicit.  It does
not turn a geometric identity into a metric exclusion, and it does not add a
source, chart, radius, symmetry, or canonicality premise.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualMetricBridgeAudit

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualMetricClassReduction ActualMainRoute
open ActualOwnedSectorDecomposition ActualSharedFactorArea
open ActualSquaredSideMatching ActualSiteAngleChain
open ActualMetricAngleAtoms ActualSectorMetricDomain
open ActualBoundaryNineTies
open ActualCircleSegmentAlgebra ActualOwnershipSwitchWidths
open ActualRingDirectionOrder ActualRingLinkBoundaryData
open ActualBoundaryCyclicOrder
open ActualHubTriangleCensus FlashTiling

/- A representative produces the actual refinement, nine genuine nearest
switches, and the exact signed disk-area decomposition.  This is the only
unconditional producer needed before a numerical class estimate starts. -/
theorem a19_area_data_bridge
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    ∃ (R : Refinement c r) (v : NineTies c r),
      Real.pi =
        (∑ A : R.Index,
          orient (c (R.labels A 0)) (c (R.labels A 1))
            (c (R.labels A 2)))/2 +
        (∑ i : Fin 9,
          (ActualSwitchAtomAggregate.switchData h hr v i).chord *
            (ActualSwitchAtomAggregate.switchData h hr v i).offset) +
        (∑ i : Fin 9,
          orient (c (nextSite i)) (switchPoint v i)
            (switchPoint v (nextRing i)))/2 +
        ∑ i : Fin 9, segmentTerm (switchGap v i) := by
  exact actual_area_data_producer h hr

/- The source-style area variables are definitional transforms of the same
 actual data.  This is a bridge to a future interval/numerical estimate, not
 an estimate itself. -/
theorem a19_shared_factor_bridge
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r) :
    Real.pi = (∑ A : R.Index, faceArea R A) +
      (∑ i : Fin 9, switchArea h hr v i) +
      ∑ i : Fin 9, sectorArea v i := by
  exact actual_shared_factor_area h hr R v

/- A19 keeps unequal endpoint radii.  The factor width is therefore the
 actual nearest-switch width with the quadratic carrying both endpoints. -/
theorem a19_width_bridge
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) :
    switchGap v i =
      2 * Real.arcsin ((19/50 : ℝ) *
        Real.sqrt (chordQuadratic v i) / 2) := by
  exact actual_factor_width_formula h hr v i

/- Every actual face and every genuine boundary switch is matched by an
 actual half-chord.  Artificial refinement diagonals are handled by the
 producer's chosen opposite slots; no frozen source table is used. -/
theorem a19_boundary_side_bridge
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r) (i : Fin 9) :
    ∃ (A : R.Index) (s : Fin 3),
      SideAt R A s (ringSite i) (nextSite i) ∧
        faceSideSquared R A s = switchSideSquared h hr v i := by
  exact actual_boundary_side_match_producer h hr R v i

/- For degree at most four, the phase chain has an exact one-turn lift.  The
 general degree-five-or-more lift is intentionally absent from this audit. -/
theorem a19_small_degree_angle_bridge
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (i : Fin 11) (hi : 9 ≤ i.val)
    (hd : (neighbors R i).card ≤ 4) :
    siteFaceSum R i = 2 * Real.pi := by
  exact actual_small_degree_hub_angle_sum h hr R i hi hd

/- The seven exclusions remain genuine proof inputs.  Naming this alias in the
 audit prevents an area identity from being mistaken for a paid certificate. -/
def UnpaidSevenClassExclusions : Prop := SevenClassExclusions

theorem unpaid_seven_class_is_exactly_metric_input :
    UnpaidSevenClassExclusions = SevenClassExclusions := rfl

/- Likewise, the C450 and energy consumers remain separate from A19. -/
structure UnpaidMainRouteInputs : Prop where
  source : C450Source11Segment.RemainingSourceObligation
  energy : EnergyTerminalBatchB11.RemainingTerminalRadius
  classes : UnpaidSevenClassExclusions

theorem main_route_from_a19_audit_inputs
    (H : UnpaidMainRouteInputs) :
    N11MainStatement SourceExactRoot.sourceRadius := by
  exact ActualMetricClassReduction.main_of_seven_class_certificates
    H.source H.energy H.classes

/- This is an audit boundary: A19 facts alone do not inhabit the three
 explicit fields above.  The theorem is deliberately a conditional consumer
 so that no false completion claim can enter the root import graph. -/
theorem a19_bridge_consumes_only_explicit_inputs
    (H : UnpaidMainRouteInputs) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  main_route_from_a19_audit_inputs H

end N11Formalization.ActualMetricBridgeAudit

#check @N11Formalization.ActualMetricBridgeAudit.a19_area_data_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_shared_factor_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_width_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_boundary_side_bridge
#check @N11Formalization.ActualMetricBridgeAudit.a19_small_degree_angle_bridge
#check @N11Formalization.ActualMetricBridgeAudit.main_route_from_a19_audit_inputs
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_area_data_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_shared_factor_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_width_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_boundary_side_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.a19_small_degree_angle_bridge
#print axioms N11Formalization.ActualMetricBridgeAudit.main_route_from_a19_audit_inputs
