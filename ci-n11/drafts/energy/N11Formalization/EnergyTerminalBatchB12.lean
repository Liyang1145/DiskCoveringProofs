import N11Formalization.EnergyTerminalBatchB11
import N11Formalization.Paid16GeneralHAll

/-! Generated (energy line 2026-10-15): B11 paid terminals plus the Paid16GeneralH*
single-cell packets. NOT compiled, NOT paid. RemainingTerminalRadius (B12) stays explicit;
`remaining11_of_remaining12` reduces the B11 obligation to it. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB12
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB11.paidIDs ∪ Paid16GeneralHAll.newIDs

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011,(DBMSourceTree.data n).terminal=true →
    n∉Patch120SharpDispatch.sharpIDs → n∉paidIDs →
    ∀ (y : Fin 9 → ℝ),(∀ q,0 ≤ y q) → (∑ q,y q=1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r

theorem remaining11_of_remaining12 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB11.RemainingTerminalRadius := by
  intro n ht hs hp y hy0 hy1 hc C Z r hf
  by_cases hn : n ∈ Paid16GeneralHAll.newIDs
  · exact (Paid16GeneralHAll.new_radius n hn y hy0 hy1 hc C Z r hf).le
  · have hp12 : n ∉ paidIDs := by
      simp only [paidIDs, Finset.mem_union, not_or]
      exact ⟨hp, hn⟩
    exact h n ht hs hp12 y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB12
#print axioms N11Formalization.EnergyTerminalBatchB12.remaining11_of_remaining12
