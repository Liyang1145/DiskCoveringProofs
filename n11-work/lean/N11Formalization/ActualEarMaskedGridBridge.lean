import N11Formalization.ActualEarOwnedWidth
import N11Formalization.ActualMetricGridBridge
import N11Formalization.MetricAreaMaskedGridDual

/-! The actual selected ear produces the additional six-gap width budget
for the masked area dual. Geometry, true nearest switches and the original
radius produce every angle/area/width/balance input internally. Numerical
node bounds and the strict final sum remain explicit certificate inputs. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualEarMaskedGridBridge

open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualBoundaryNineTies
open ActualRefinementDoubleCounting ActualEdgeMetricModel ActualMetricAngleAtoms
open ActualSectorAreaEnvelope ActualRingLinkBoundaryData ActualQ1CoreFans
open MetricAreaGridCertificate MetricAreaMaskedGridDual ActualEarOwnedWidth

theorem exclude_selected_ear_of_masked_grid_certificate
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r) (E : EarData R)
    (mu : Fin 11 → ℝ) (lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (U : ℝ) (hU : Real.pi ≤ U) (N : ℕ) (hN : 0 < N)
    (edgeMax : Finset (Fin 11) → ℝ) (sectorMax : Fin 9 → ℝ)
    (hedge : ∀ e ∈ edges R, ∀ k : Fin (N+1),
      edgeResidual (∑ j ∈ e, mu j) (gridPoint U N k) ≤ edgeMax e)
    (hsector : ∀ (i : Fin 9) (k : Fin (N+1)),
      sectorResidual (mu (nextSite i))
        (widthMultiplier (outsideGaps E.center) lam eta i)
        (gridPoint U N k) ≤ sectorMax i)
    (hstrict : 2*Real.pi*((∑ j : Fin 11, mu j)-lam) -
      (2*Real.pi-2*Real.arcsin (19/25))*eta +
      (∑ e ∈ edges R, (edgeMax e+((19/50 : ℝ)^2+|∑ j ∈ e, mu j|)*U/(N : ℝ))) +
      (∑ i : Fin 9, (sectorMax i+
        (1+widthMultiplier (outsideGaps E.center) lam eta i+|mu (nextSite i)|)*U/(N : ℝ))) < Real.pi) :
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
  have hmask := actual_selected_ear_outside_envelope h hr v E
  have htotal : 2*Real.pi*(∑ j : Fin 11, mu j)-2*Real.pi*lam -
      (2*Real.pi-2*Real.arcsin (19/25))*eta +
      (∑ e : edges R, (edgeMax e.val+((19/50 : ℝ)^2+|∑ j ∈ e.val, mu j|)*U/(N : ℝ))) +
      (∑ i : Fin 9, (sectorMax i+
        (1+widthMultiplier (outsideGaps E.center) lam eta i+|mu (nextSite i)|)*U/(N : ℝ))) < Real.pi := by
    rw [hsum (fun e => edgeMax e+((19/50 : ℝ)^2+|∑ j ∈ e, mu j|)*U/(N : ℝ))]
    nlinarith only [hstrict]
  exact exclude_of_masked_grid_certificate
    (fun e : edges R => edgeAngle h hr R v e.val) (sectorAngle v)
    (fun e : edges R => ∑ j ∈ e.val, mu j) (fun i : Fin 9 => mu (nextSite i))
    (2*Real.pi*(∑ j : Fin 11, mu j))
    (fun e => hθ e.val e.property) (actual_sector_angle_bounds v)
    hb ha hwidth (outsideGaps E.center) (Real.arcsin (19/25)) hmask
    lam eta hlam heta U hU N hN (fun e : edges R => edgeMax e.val) sectorMax
    (fun e => hedge e.val e.property) hsector htotal

end N11Formalization.ActualEarMaskedGridBridge
#check @N11Formalization.ActualEarMaskedGridBridge.exclude_selected_ear_of_masked_grid_certificate
#print axioms N11Formalization.ActualEarMaskedGridBridge.exclude_selected_ear_of_masked_grid_certificate
