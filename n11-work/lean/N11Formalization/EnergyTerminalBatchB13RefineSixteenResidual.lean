import N11Formalization.EnergyTerminalBatchB13RefineSixteenRepair
import N11Formalization.EnergyTerminalBatchB13ResidualCertificates

/-! Residual interface for the repaired sixteen-refinement paid set.  The
theorems below reduce the B13 radius obligation to the complement of the
strictly larger `RefineSixteenRepair.paidIDs`; they assert neither its
cardinality nor the existence of any residual certificate. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
open N11Formalization SourceChartIsometry ResumeNetwork
open scoped BigOperators
noncomputable section

def residualIDs : Finset (Fin 5011) :=
  (Finset.univ.filter fun n => (DBMSourceTree.data n).terminal = true).filter
    fun n => n ∉ Patch120SharpDispatch.sharpIDs ∧
      n ∉ EnergyTerminalBatchB13RefineSixteenRepair.paidIDs

theorem mem_residualIDs_iff (n : Fin 5011) :
    n ∈ residualIDs ↔ (DBMSourceTree.data n).terminal = true ∧
      n ∉ Patch120SharpDispatch.sharpIDs ∧
      n ∉ EnergyTerminalBatchB13RefineSixteenRepair.paidIDs := by
  simp only [residualIDs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem remaining_iff :
    EnergyTerminalBatchB13RefineSixteenRepair.RemainingTerminalRadius ↔
      ∀ n : Fin 5011, n ∈ residualIDs →
        ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
          FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
            (FlashLeafSplit.tlift y) →
          ∀ (C Z : Fin 11 → Point) (r : ℝ),
            Feasible (chartAnchors y) C Z r →
              SourceExactRoot.sourceRadius ≤ r := by
  constructor
  · intro h n hn
    obtain ⟨ht, hs, hp⟩ := (mem_residualIDs_iff n).mp hn
    exact h n ht hs hp
  · intro h n ht hs hp
    exact h n ((mem_residualIDs_iff n).mpr ⟨ht, hs, hp⟩)

theorem residual_radius_certificate_of_remaining
    (h : EnergyTerminalBatchB13RefineSixteenRepair.RemainingTerminalRadius)
    (n : Fin 5011) (hn : n ∈ residualIDs) :
    EnergyTerminalBatchB13.ResidualRadiusCertificate n :=
  ⟨fun y hy0 hy1 hc C Z r hf =>
    (remaining_iff.mp h) n hn y hy0 hy1 hc C Z r hf⟩

theorem remaining_of_residual_radius_certificates
    (h : ∀ n : Fin 5011, n ∈ residualIDs →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13RefineSixteenRepair.RemainingTerminalRadius := by
  rw [remaining_iff]
  intro n hn y hy0 hy1 hc C Z r hf
  exact (h n hn).radius y hy0 hy1 hc C Z r hf

theorem b13_remaining_of_residual_radius_certificates
    (h : ∀ n : Fin 5011, n ∈ residualIDs →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  EnergyTerminalBatchB13RefineSixteenRepair.remaining_of
    (remaining_of_residual_radius_certificates h)

theorem chart_radius_of_residual_radius_certificates
    (h : ∀ n : Fin 5011, n ∈ residualIDs →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius ≤ r :=
  EnergyTerminalBatchB13.chart_radius_of_remaining
    (b13_remaining_of_residual_radius_certificates h) y hy0 hy1 C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.remaining_iff
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.remaining_of_residual_radius_certificates
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.b13_remaining_of_residual_radius_certificates
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.chart_radius_of_residual_radius_certificates
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.b13_remaining_of_residual_radius_certificates
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.chart_radius_of_residual_radius_certificates
