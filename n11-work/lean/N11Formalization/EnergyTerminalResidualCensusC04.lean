import N11Formalization.EnergyTerminalResidualCensusBase

/-! Census part 4/4: source-index equivalence blocks congruent to
3 modulo 4.  Every kernel decision below covers at most 100 source
indices. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

theorem mem_iff_block03 (n : Fin 5011)
    (hlo : 300 ≤ n.val) (hhi : n.val < 400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block07 (n : Fin 5011)
    (hlo : 700 ≤ n.val) (hhi : n.val < 800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block11 (n : Fin 5011)
    (hlo : 1100 ≤ n.val) (hhi : n.val < 1200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block15 (n : Fin 5011)
    (hlo : 1500 ≤ n.val) (hhi : n.val < 1600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block19 (n : Fin 5011)
    (hlo : 1900 ≤ n.val) (hhi : n.val < 2000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block23 (n : Fin 5011)
    (hlo : 2300 ≤ n.val) (hhi : n.val < 2400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block27 (n : Fin 5011)
    (hlo : 2700 ≤ n.val) (hhi : n.val < 2800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block31 (n : Fin 5011)
    (hlo : 3100 ≤ n.val) (hhi : n.val < 3200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block35 (n : Fin 5011)
    (hlo : 3500 ≤ n.val) (hhi : n.val < 3600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block39 (n : Fin 5011)
    (hlo : 3900 ≤ n.val) (hhi : n.val < 4000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block43 (n : Fin 5011)
    (hlo : 4300 ≤ n.val) (hhi : n.val < 4400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block47 (n : Fin 5011)
    (hlo : 4700 ≤ n.val) (hhi : n.val < 4800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

end
end N11Formalization.EnergyTerminalResidualCensus
