import N11Formalization.EnergyTerminalResidualCensusBase

/-! Census part 3/4: source-index equivalence blocks congruent to
2 modulo 4.  Every kernel decision below covers at most 100 source
indices. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

theorem mem_iff_block02 (n : Fin 5011)
    (hlo : 200 ≤ n.val) (hhi : n.val < 300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block06 (n : Fin 5011)
    (hlo : 600 ≤ n.val) (hhi : n.val < 700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block10 (n : Fin 5011)
    (hlo : 1000 ≤ n.val) (hhi : n.val < 1100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block14 (n : Fin 5011)
    (hlo : 1400 ≤ n.val) (hhi : n.val < 1500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block18 (n : Fin 5011)
    (hlo : 1800 ≤ n.val) (hhi : n.val < 1900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block22 (n : Fin 5011)
    (hlo : 2200 ≤ n.val) (hhi : n.val < 2300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block26 (n : Fin 5011)
    (hlo : 2600 ≤ n.val) (hhi : n.val < 2700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block30 (n : Fin 5011)
    (hlo : 3000 ≤ n.val) (hhi : n.val < 3100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block34 (n : Fin 5011)
    (hlo : 3400 ≤ n.val) (hhi : n.val < 3500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block38 (n : Fin 5011)
    (hlo : 3800 ≤ n.val) (hhi : n.val < 3900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block42 (n : Fin 5011)
    (hlo : 4200 ≤ n.val) (hhi : n.val < 4300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block46 (n : Fin 5011)
    (hlo : 4600 ≤ n.val) (hhi : n.val < 4700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem mem_iff_block50 (n : Fin 5011)
    (hlo : 5000 ≤ n.val) (hhi : n.val < 5011) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

end
end N11Formalization.EnergyTerminalResidualCensus
