import N11Formalization.EnergyTerminalBatchB12
import N11Formalization.EnergyRefineAll

/-! DRAFT (energy line 2026-10-15): B12 plus refinement-certified terminals. NOT compiled. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB12.paidIDs ∪ EnergyRefineAll.newIDs

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011,(DBMSourceTree.data n).terminal=true →
    n∉Patch120SharpDispatch.sharpIDs → n∉paidIDs →
    ∀ (y : Fin 9 → ℝ),(∀ q,0 ≤ y q) → (∑ q,y q=1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r

theorem remaining12_of_remaining13 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB12.RemainingTerminalRadius := by
  intro n ht hs hp y hy0 hy1 hc C Z r hf
  by_cases hn : n ∈ EnergyRefineAll.newIDs
  · exact (EnergyRefineAll.new_radius n hn y hy0 hy1 hc C Z r hf).le
  · have hp13 : n ∉ paidIDs := by
      simp only [paidIDs, Finset.mem_union, not_or]
      exact ⟨hp, hn⟩
    exact h n ht hs hp13 y hy0 hy1 hc C Z r hf

theorem remaining11_of_remaining13 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB11.RemainingTerminalRadius :=
  EnergyTerminalBatchB12.remaining11_of_remaining12 (remaining12_of_remaining13 h)

end
end N11Formalization.EnergyTerminalBatchB13
#print axioms N11Formalization.EnergyTerminalBatchB13.remaining11_of_remaining13
