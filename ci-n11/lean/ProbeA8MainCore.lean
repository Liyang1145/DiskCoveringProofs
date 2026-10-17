import N11Formalization.ActualBoundaryChartRelabeling
import N11Formalization.ActualHubEdgeEndpoints
import N11Formalization.EnergyTerminalBatchB11

/-! Preflight the ACTUAL main-route connection before the historical
source11 cache completes. The real SourceObligation remains explicit;
this probe does NOT pay any C450 source segment or final lower bound. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA8MainCore
open ActualCoverStructuralReduction ActualBoundaryChart ActualBoundaryChartRelabeling
open ActualBoundaryCyclicOrder ActualRingDirectionOrder SourceChartIsometry ResumeNetwork

def Canonical33Obligation : Prop :=
  ∀ (c : Fin 11 → Point) (r : ℝ), Representative c r →
    r < SourceExactRoot.sourceRadius →
    ∃ (k : Fin 9) (e : Equiv.Perm (Fin 11)) (Z : Fin 11 → Point),
      (∀ i : Fin 9, e (ringSite i) = ringSite (i+k)) ∧
      ∀ f : Fin 11, ∀ v : Fin 3, dist (c (e (face f v))) (Z f) ≤ r

theorem lower_bound_core
    (hs : C450NormalizedInterface.SourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : Canonical33Obligation) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r := by
  intro r c hr0 hc
  by_contra hnot
  have hlt : r < SourceExactRoot.sourceRadius := lt_of_not_ge hnot
  obtain ⟨p,d,hd,_,_⟩ := representative_of_source hs hlt hc
  have hrR0 : r < 19/50 := hlt.trans
    (SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real)
  obtain ⟨b⟩ := boundaryChart_of_cover hd.cover hrR0 hd.labels hd.midpoint_order
  obtain ⟨k,e,Z,he,hfaces⟩ := h33 d r hd hlt
  have hf := BoundaryChart.shifted_feasible_of_faces b hr0 k e he Z hfaces
  have hbound := EnergyTerminalBatchB11.chart_radius_of_remaining henergy
    (shiftY b.y k) (shiftY_nonneg b.nonneg k) (shiftY_sum b.sum_one k)
    (fun i => gaugeMap b k (d (e i))) (fun f => gaugeMap b k (Z f)) r hf
  exact not_le_of_gt hlt hbound

end N11Formalization.ProbeA8MainCore
#check @N11Formalization.ProbeA8MainCore.lower_bound_core
#print axioms N11Formalization.ProbeA8MainCore.lower_bound_core
