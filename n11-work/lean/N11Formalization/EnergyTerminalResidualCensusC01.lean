import N11Formalization.EnergyTerminalResidualCensusBase

/-! Census part 1/4: source-index equivalence blocks congruent to
0 modulo 4.  Every kernel decision below covers at most 100 source
indices. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

theorem mem_iff_block00 (n : Fin 5011)
    (hlo : 0 ≤ n.val) (hhi : n.val < 100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block04 (n : Fin 5011)
    (hlo : 400 ≤ n.val) (hhi : n.val < 500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block08 (n : Fin 5011)
    (hlo : 800 ≤ n.val) (hhi : n.val < 900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block12 (n : Fin 5011)
    (hlo : 1200 ≤ n.val) (hhi : n.val < 1300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block16 (n : Fin 5011)
    (hlo : 1600 ≤ n.val) (hhi : n.val < 1700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block20 (n : Fin 5011)
    (hlo : 2000 ≤ n.val) (hhi : n.val < 2100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block24 (n : Fin 5011)
    (hlo : 2400 ≤ n.val) (hhi : n.val < 2500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block28 (n : Fin 5011)
    (hlo : 2800 ≤ n.val) (hhi : n.val < 2900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block32 (n : Fin 5011)
    (hlo : 3200 ≤ n.val) (hhi : n.val < 3300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block36 (n : Fin 5011)
    (hlo : 3600 ≤ n.val) (hhi : n.val < 3700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block40 (n : Fin 5011)
    (hlo : 4000 ≤ n.val) (hhi : n.val < 4100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block44 (n : Fin 5011)
    (hlo : 4400 ≤ n.val) (hhi : n.val < 4500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

theorem mem_iff_block48 (n : Fin 5011)
    (hlo : 4800 ≤ n.val) (hhi : n.val < 4900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert

end
end N11Formalization.EnergyTerminalResidualCensus
