import N11Formalization.EnergyTerminalResidualCensusBase

/-! Census part 2/4: source-index equivalence blocks congruent to
1 modulo 4.  Every kernel decision below covers at most 100 source
indices. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

theorem mem_iff_block01 (n : Fin 5011)
    (hlo : 100 ≤ n.val) (hhi : n.val < 200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block05 (n : Fin 5011)
    (hlo : 500 ≤ n.val) (hhi : n.val < 600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block09 (n : Fin 5011)
    (hlo : 900 ≤ n.val) (hhi : n.val < 1000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block13 (n : Fin 5011)
    (hlo : 1300 ≤ n.val) (hhi : n.val < 1400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block17 (n : Fin 5011)
    (hlo : 1700 ≤ n.val) (hhi : n.val < 1800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block21 (n : Fin 5011)
    (hlo : 2100 ≤ n.val) (hhi : n.val < 2200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block25 (n : Fin 5011)
    (hlo : 2500 ≤ n.val) (hhi : n.val < 2600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block29 (n : Fin 5011)
    (hlo : 2900 ≤ n.val) (hhi : n.val < 3000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block33 (n : Fin 5011)
    (hlo : 3300 ≤ n.val) (hhi : n.val < 3400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block37 (n : Fin 5011)
    (hlo : 3700 ≤ n.val) (hhi : n.val < 3800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block41 (n : Fin 5011)
    (hlo : 4100 ≤ n.val) (hhi : n.val < 4200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block45 (n : Fin 5011)
    (hlo : 4500 ≤ n.val) (hhi : n.val < 4600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block49 (n : Fin 5011)
    (hlo : 4900 ≤ n.val) (hhi : n.val < 5000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

end
end N11Formalization.EnergyTerminalResidualCensus
