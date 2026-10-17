import N11Formalization.ActualEdgeMetricModel
import N11Formalization.MetricAreaGridDual

/-! Actual geometry feeds the finite-node certificate consumer.
The only certificate inputs are node bounds, nonnegative width multiplier,
grid size/coverage endpoint, and a strict final sum. No angle, area, graph,
radius-matching or site-balance premise is supplied by the certificate. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualMetricGridBridge

open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualBoundaryNineTies
open ActualRefinementDoubleCounting ActualEdgeMetricModel ActualMetricAngleAtoms
open ActualSectorAreaEnvelope ActualRingLinkBoundaryData
open MetricAreaGridCertificate MetricAreaGridDual

/-- All geometric inputs to the grid dual are produced from the same real
representative, refinement and nearest ownership switches. -/
theorem exclude_representative_of_grid_certificate
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r)
    (mu : Fin 11 → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (U : ℝ) (hU : Real.pi ≤ U) (N : ℕ) (hN : 0 < N)
    (edgeMax : Finset (Fin 11) → ℝ) (sectorMax : Fin 9 → ℝ)
    (hedge : ∀ e ∈ edges R, ∀ k : Fin (N+1),
      edgeResidual (∑ j ∈ e, mu j) (gridPoint U N k) ≤ edgeMax e)
    (hsector : ∀ (i : Fin 9) (k : Fin (N+1)),
      sectorResidual (mu (nextSite i)) lam (gridPoint U N k) ≤ sectorMax i)
    (hstrict : 2*Real.pi*((∑ j : Fin 11, mu j)-lam) +
      (∑ e ∈ edges R, (edgeMax e+((19/50 : ℝ)^2+|∑ j ∈ e, mu j|)*U/(N : ℝ))) +
      (∑ i : Fin 9, (sectorMax i+(1+lam+|mu (nextSite i)|)*U/(N : ℝ))) < Real.pi) :
    False := by
  classical
  have hsum (f : Finset (Fin 11) → ℝ) :
      (∑ e : edges R, f e.val) = ∑ e ∈ edges R, f e := Finset.sum_coe_sort _ _
  obtain ⟨_,hθ,_,_,harea,hwidth⟩ := actual_edge_metric_model h hr R v
  have hb : (∑ e : edges R, (∑ j ∈ e.val, mu j)*edgeAngle h hr R v e.val) +
      (∑ i : Fin 9, mu (nextSite i)*sectorAngle v i) =
        2*Real.pi*(∑ j : Fin 11, mu j) := by
    rw [hsum (fun e => (∑ j ∈ e, mu j)*edgeAngle h hr R v e)]
    exact actual_weighted_angle_balance h hr R v mu
  have ha : Real.pi ≤ (19/50 : ℝ)^2*(∑ e : edges R, Real.sin (edgeAngle h hr R v e.val)) +
      ∑ i : Fin 9, areaEnvelope (sectorAngle v i) := by
    rw [hsum (fun e => Real.sin (edgeAngle h hr R v e))]
    exact harea
  have htotal : 2*Real.pi*(∑ j : Fin 11, mu j)-2*Real.pi*lam +
      (∑ e : edges R, (edgeMax e.val+((19/50 : ℝ)^2+|∑ j ∈ e.val, mu j|)*U/(N : ℝ))) +
      (∑ i : Fin 9, (sectorMax i+(1+lam+|mu (nextSite i)|)*U/(N : ℝ))) < Real.pi := by
    rw [hsum (fun e => edgeMax e+((19/50 : ℝ)^2+|∑ j ∈ e, mu j|)*U/(N : ℝ))]
    nlinarith only [hstrict]
  exact exclude_of_grid_certificate
    (fun e : edges R => edgeAngle h hr R v e.val) (sectorAngle v)
    (fun e : edges R => ∑ j ∈ e.val, mu j) (fun i : Fin 9 => mu (nextSite i))
    (2*Real.pi*(∑ j : Fin 11, mu j))
    (fun e => hθ e.val e.property) (actual_sector_angle_bounds v)
    hb ha hwidth lam hlam U hU N hN
    (fun e : edges R => edgeMax e.val) sectorMax
    (fun e => hedge e.val e.property) hsector htotal

end N11Formalization.ActualMetricGridBridge
#check @N11Formalization.ActualMetricGridBridge.exclude_representative_of_grid_certificate
#print axioms N11Formalization.ActualMetricGridBridge.exclude_representative_of_grid_certificate
