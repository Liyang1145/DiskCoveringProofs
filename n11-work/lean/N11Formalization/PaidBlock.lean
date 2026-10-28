import N11Formalization.EnergyTerminalBatchB11

/-! Union algebra for concretely paid terminal blocks. A `Block` carries exactly
the three facts a dispatch module consumes: the id set, terminality of every id,
and the strict radius bound for every id on the closed simplex. `union` is
proof-only assembly: it adds no hypothesis and assumes no terminal. -/
set_option autoImplicit false
namespace N11Formalization.PaidBlock
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

structure Block where
  ids : Finset (Fin 5011)
  terminal : ∀ n, n ∈ ids → (DBMSourceTree.data n).terminal = true
  radius : ∀ n, n ∈ ids →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius < r

def Block.union (A B : Block) : Block where
  ids := A.ids ∪ B.ids
  terminal := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · exact A.terminal n h
    · exact B.terminal n h
  radius := by
    intro n hn y hy0 hy1 hc C Z r hf
    rcases Finset.mem_union.mp hn with h | h
    · exact A.radius n h y hy0 hy1 hc C Z r hf
    · exact B.radius n h y hy0 hy1 hc C Z r hf

end
end N11Formalization.PaidBlock
#check @N11Formalization.PaidBlock.Block
#check @N11Formalization.PaidBlock.Block.union
#print axioms N11Formalization.PaidBlock.Block.union
