import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
import N11Formalization.EnergyTerminalResidualCensusRefineSixteen

/-! Exact conditional census after the sixteen-refinement repair: 373
terminal ids remain.  The four literal chunks keep kernel decisions below
the measured size guard; the equality proof is split into separate ten-index
kernel checks and 100-index dispatch facts.  This module proves cardinality
only, not radius payment. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus
noncomputable section

abbrev residual373 : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs

def residual373 : Finset (Fin 5011) :=
  chunk0 ∪ (chunk1 ∪ (chunk2 ∪ chunk3))

private theorem mem_sub_000 (n : Fin 5011)
    (hlo : 0 ≤ n.val) (hhi : n.val < 10) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_001 (n : Fin 5011)
    (hlo : 10 ≤ n.val) (hhi : n.val < 20) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_002 (n : Fin 5011)
    (hlo : 20 ≤ n.val) (hhi : n.val < 30) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_003 (n : Fin 5011)
    (hlo : 30 ≤ n.val) (hhi : n.val < 40) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_004 (n : Fin 5011)
    (hlo : 40 ≤ n.val) (hhi : n.val < 50) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_005 (n : Fin 5011)
    (hlo : 50 ≤ n.val) (hhi : n.val < 60) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_006 (n : Fin 5011)
    (hlo : 60 ≤ n.val) (hhi : n.val < 70) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_007 (n : Fin 5011)
    (hlo : 70 ≤ n.val) (hhi : n.val < 80) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_008 (n : Fin 5011)
    (hlo : 80 ≤ n.val) (hhi : n.val < 90) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_009 (n : Fin 5011)
    (hlo : 90 ≤ n.val) (hhi : n.val < 100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_010 (n : Fin 5011)
    (hlo : 100 ≤ n.val) (hhi : n.val < 110) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_011 (n : Fin 5011)
    (hlo : 110 ≤ n.val) (hhi : n.val < 120) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_012 (n : Fin 5011)
    (hlo : 120 ≤ n.val) (hhi : n.val < 130) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_013 (n : Fin 5011)
    (hlo : 130 ≤ n.val) (hhi : n.val < 140) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_014 (n : Fin 5011)
    (hlo : 140 ≤ n.val) (hhi : n.val < 150) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_015 (n : Fin 5011)
    (hlo : 150 ≤ n.val) (hhi : n.val < 160) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_016 (n : Fin 5011)
    (hlo : 160 ≤ n.val) (hhi : n.val < 170) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_017 (n : Fin 5011)
    (hlo : 170 ≤ n.val) (hhi : n.val < 180) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_018 (n : Fin 5011)
    (hlo : 180 ≤ n.val) (hhi : n.val < 190) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_019 (n : Fin 5011)
    (hlo : 190 ≤ n.val) (hhi : n.val < 200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_020 (n : Fin 5011)
    (hlo : 200 ≤ n.val) (hhi : n.val < 210) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_021 (n : Fin 5011)
    (hlo : 210 ≤ n.val) (hhi : n.val < 220) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_022 (n : Fin 5011)
    (hlo : 220 ≤ n.val) (hhi : n.val < 230) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_023 (n : Fin 5011)
    (hlo : 230 ≤ n.val) (hhi : n.val < 240) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_024 (n : Fin 5011)
    (hlo : 240 ≤ n.val) (hhi : n.val < 250) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_025 (n : Fin 5011)
    (hlo : 250 ≤ n.val) (hhi : n.val < 260) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_026 (n : Fin 5011)
    (hlo : 260 ≤ n.val) (hhi : n.val < 270) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_027 (n : Fin 5011)
    (hlo : 270 ≤ n.val) (hhi : n.val < 280) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_028 (n : Fin 5011)
    (hlo : 280 ≤ n.val) (hhi : n.val < 290) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_029 (n : Fin 5011)
    (hlo : 290 ≤ n.val) (hhi : n.val < 300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_030 (n : Fin 5011)
    (hlo : 300 ≤ n.val) (hhi : n.val < 310) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_031 (n : Fin 5011)
    (hlo : 310 ≤ n.val) (hhi : n.val < 320) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_032 (n : Fin 5011)
    (hlo : 320 ≤ n.val) (hhi : n.val < 330) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_033 (n : Fin 5011)
    (hlo : 330 ≤ n.val) (hhi : n.val < 340) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_034 (n : Fin 5011)
    (hlo : 340 ≤ n.val) (hhi : n.val < 350) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_035 (n : Fin 5011)
    (hlo : 350 ≤ n.val) (hhi : n.val < 360) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_036 (n : Fin 5011)
    (hlo : 360 ≤ n.val) (hhi : n.val < 370) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_037 (n : Fin 5011)
    (hlo : 370 ≤ n.val) (hhi : n.val < 380) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_038 (n : Fin 5011)
    (hlo : 380 ≤ n.val) (hhi : n.val < 390) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_039 (n : Fin 5011)
    (hlo : 390 ≤ n.val) (hhi : n.val < 400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_040 (n : Fin 5011)
    (hlo : 400 ≤ n.val) (hhi : n.val < 410) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_041 (n : Fin 5011)
    (hlo : 410 ≤ n.val) (hhi : n.val < 420) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_042 (n : Fin 5011)
    (hlo : 420 ≤ n.val) (hhi : n.val < 430) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_043 (n : Fin 5011)
    (hlo : 430 ≤ n.val) (hhi : n.val < 440) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_044 (n : Fin 5011)
    (hlo : 440 ≤ n.val) (hhi : n.val < 450) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_045 (n : Fin 5011)
    (hlo : 450 ≤ n.val) (hhi : n.val < 460) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_046 (n : Fin 5011)
    (hlo : 460 ≤ n.val) (hhi : n.val < 470) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_047 (n : Fin 5011)
    (hlo : 470 ≤ n.val) (hhi : n.val < 480) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_048 (n : Fin 5011)
    (hlo : 480 ≤ n.val) (hhi : n.val < 490) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_049 (n : Fin 5011)
    (hlo : 490 ≤ n.val) (hhi : n.val < 500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_050 (n : Fin 5011)
    (hlo : 500 ≤ n.val) (hhi : n.val < 510) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_051 (n : Fin 5011)
    (hlo : 510 ≤ n.val) (hhi : n.val < 520) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_052 (n : Fin 5011)
    (hlo : 520 ≤ n.val) (hhi : n.val < 530) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_053 (n : Fin 5011)
    (hlo : 530 ≤ n.val) (hhi : n.val < 540) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_054 (n : Fin 5011)
    (hlo : 540 ≤ n.val) (hhi : n.val < 550) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_055 (n : Fin 5011)
    (hlo : 550 ≤ n.val) (hhi : n.val < 560) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_056 (n : Fin 5011)
    (hlo : 560 ≤ n.val) (hhi : n.val < 570) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_057 (n : Fin 5011)
    (hlo : 570 ≤ n.val) (hhi : n.val < 580) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_058 (n : Fin 5011)
    (hlo : 580 ≤ n.val) (hhi : n.val < 590) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_059 (n : Fin 5011)
    (hlo : 590 ≤ n.val) (hhi : n.val < 600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_060 (n : Fin 5011)
    (hlo : 600 ≤ n.val) (hhi : n.val < 610) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_061 (n : Fin 5011)
    (hlo : 610 ≤ n.val) (hhi : n.val < 620) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_062 (n : Fin 5011)
    (hlo : 620 ≤ n.val) (hhi : n.val < 630) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_063 (n : Fin 5011)
    (hlo : 630 ≤ n.val) (hhi : n.val < 640) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_064 (n : Fin 5011)
    (hlo : 640 ≤ n.val) (hhi : n.val < 650) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_065 (n : Fin 5011)
    (hlo : 650 ≤ n.val) (hhi : n.val < 660) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_066 (n : Fin 5011)
    (hlo : 660 ≤ n.val) (hhi : n.val < 670) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_067 (n : Fin 5011)
    (hlo : 670 ≤ n.val) (hhi : n.val < 680) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_068 (n : Fin 5011)
    (hlo : 680 ≤ n.val) (hhi : n.val < 690) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_069 (n : Fin 5011)
    (hlo : 690 ≤ n.val) (hhi : n.val < 700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_070 (n : Fin 5011)
    (hlo : 700 ≤ n.val) (hhi : n.val < 710) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_071 (n : Fin 5011)
    (hlo : 710 ≤ n.val) (hhi : n.val < 720) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_072 (n : Fin 5011)
    (hlo : 720 ≤ n.val) (hhi : n.val < 730) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_073 (n : Fin 5011)
    (hlo : 730 ≤ n.val) (hhi : n.val < 740) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_074 (n : Fin 5011)
    (hlo : 740 ≤ n.val) (hhi : n.val < 750) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_075 (n : Fin 5011)
    (hlo : 750 ≤ n.val) (hhi : n.val < 760) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_076 (n : Fin 5011)
    (hlo : 760 ≤ n.val) (hhi : n.val < 770) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_077 (n : Fin 5011)
    (hlo : 770 ≤ n.val) (hhi : n.val < 780) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_078 (n : Fin 5011)
    (hlo : 780 ≤ n.val) (hhi : n.val < 790) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_079 (n : Fin 5011)
    (hlo : 790 ≤ n.val) (hhi : n.val < 800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_080 (n : Fin 5011)
    (hlo : 800 ≤ n.val) (hhi : n.val < 810) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_081 (n : Fin 5011)
    (hlo : 810 ≤ n.val) (hhi : n.val < 820) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_082 (n : Fin 5011)
    (hlo : 820 ≤ n.val) (hhi : n.val < 830) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_083 (n : Fin 5011)
    (hlo : 830 ≤ n.val) (hhi : n.val < 840) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_084 (n : Fin 5011)
    (hlo : 840 ≤ n.val) (hhi : n.val < 850) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_085 (n : Fin 5011)
    (hlo : 850 ≤ n.val) (hhi : n.val < 860) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_086 (n : Fin 5011)
    (hlo : 860 ≤ n.val) (hhi : n.val < 870) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_087 (n : Fin 5011)
    (hlo : 870 ≤ n.val) (hhi : n.val < 880) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_088 (n : Fin 5011)
    (hlo : 880 ≤ n.val) (hhi : n.val < 890) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_089 (n : Fin 5011)
    (hlo : 890 ≤ n.val) (hhi : n.val < 900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_090 (n : Fin 5011)
    (hlo : 900 ≤ n.val) (hhi : n.val < 910) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_091 (n : Fin 5011)
    (hlo : 910 ≤ n.val) (hhi : n.val < 920) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_092 (n : Fin 5011)
    (hlo : 920 ≤ n.val) (hhi : n.val < 930) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_093 (n : Fin 5011)
    (hlo : 930 ≤ n.val) (hhi : n.val < 940) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_094 (n : Fin 5011)
    (hlo : 940 ≤ n.val) (hhi : n.val < 950) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_095 (n : Fin 5011)
    (hlo : 950 ≤ n.val) (hhi : n.val < 960) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_096 (n : Fin 5011)
    (hlo : 960 ≤ n.val) (hhi : n.val < 970) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_097 (n : Fin 5011)
    (hlo : 970 ≤ n.val) (hhi : n.val < 980) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_098 (n : Fin 5011)
    (hlo : 980 ≤ n.val) (hhi : n.val < 990) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_099 (n : Fin 5011)
    (hlo : 990 ≤ n.val) (hhi : n.val < 1000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_100 (n : Fin 5011)
    (hlo : 1000 ≤ n.val) (hhi : n.val < 1010) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_101 (n : Fin 5011)
    (hlo : 1010 ≤ n.val) (hhi : n.val < 1020) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_102 (n : Fin 5011)
    (hlo : 1020 ≤ n.val) (hhi : n.val < 1030) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_103 (n : Fin 5011)
    (hlo : 1030 ≤ n.val) (hhi : n.val < 1040) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_104 (n : Fin 5011)
    (hlo : 1040 ≤ n.val) (hhi : n.val < 1050) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_105 (n : Fin 5011)
    (hlo : 1050 ≤ n.val) (hhi : n.val < 1060) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_106 (n : Fin 5011)
    (hlo : 1060 ≤ n.val) (hhi : n.val < 1070) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_107 (n : Fin 5011)
    (hlo : 1070 ≤ n.val) (hhi : n.val < 1080) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_108 (n : Fin 5011)
    (hlo : 1080 ≤ n.val) (hhi : n.val < 1090) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_109 (n : Fin 5011)
    (hlo : 1090 ≤ n.val) (hhi : n.val < 1100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_110 (n : Fin 5011)
    (hlo : 1100 ≤ n.val) (hhi : n.val < 1110) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_111 (n : Fin 5011)
    (hlo : 1110 ≤ n.val) (hhi : n.val < 1120) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_112 (n : Fin 5011)
    (hlo : 1120 ≤ n.val) (hhi : n.val < 1130) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_113 (n : Fin 5011)
    (hlo : 1130 ≤ n.val) (hhi : n.val < 1140) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_114 (n : Fin 5011)
    (hlo : 1140 ≤ n.val) (hhi : n.val < 1150) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_115 (n : Fin 5011)
    (hlo : 1150 ≤ n.val) (hhi : n.val < 1160) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_116 (n : Fin 5011)
    (hlo : 1160 ≤ n.val) (hhi : n.val < 1170) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_117 (n : Fin 5011)
    (hlo : 1170 ≤ n.val) (hhi : n.val < 1180) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_118 (n : Fin 5011)
    (hlo : 1180 ≤ n.val) (hhi : n.val < 1190) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_119 (n : Fin 5011)
    (hlo : 1190 ≤ n.val) (hhi : n.val < 1200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_120 (n : Fin 5011)
    (hlo : 1200 ≤ n.val) (hhi : n.val < 1210) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_121 (n : Fin 5011)
    (hlo : 1210 ≤ n.val) (hhi : n.val < 1220) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_122 (n : Fin 5011)
    (hlo : 1220 ≤ n.val) (hhi : n.val < 1230) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_123 (n : Fin 5011)
    (hlo : 1230 ≤ n.val) (hhi : n.val < 1240) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_124 (n : Fin 5011)
    (hlo : 1240 ≤ n.val) (hhi : n.val < 1250) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_125 (n : Fin 5011)
    (hlo : 1250 ≤ n.val) (hhi : n.val < 1260) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_126 (n : Fin 5011)
    (hlo : 1260 ≤ n.val) (hhi : n.val < 1270) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_127 (n : Fin 5011)
    (hlo : 1270 ≤ n.val) (hhi : n.val < 1280) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_128 (n : Fin 5011)
    (hlo : 1280 ≤ n.val) (hhi : n.val < 1290) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_129 (n : Fin 5011)
    (hlo : 1290 ≤ n.val) (hhi : n.val < 1300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_130 (n : Fin 5011)
    (hlo : 1300 ≤ n.val) (hhi : n.val < 1310) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_131 (n : Fin 5011)
    (hlo : 1310 ≤ n.val) (hhi : n.val < 1320) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_132 (n : Fin 5011)
    (hlo : 1320 ≤ n.val) (hhi : n.val < 1330) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_133 (n : Fin 5011)
    (hlo : 1330 ≤ n.val) (hhi : n.val < 1340) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_134 (n : Fin 5011)
    (hlo : 1340 ≤ n.val) (hhi : n.val < 1350) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_135 (n : Fin 5011)
    (hlo : 1350 ≤ n.val) (hhi : n.val < 1360) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_136 (n : Fin 5011)
    (hlo : 1360 ≤ n.val) (hhi : n.val < 1370) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_137 (n : Fin 5011)
    (hlo : 1370 ≤ n.val) (hhi : n.val < 1380) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_138 (n : Fin 5011)
    (hlo : 1380 ≤ n.val) (hhi : n.val < 1390) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_139 (n : Fin 5011)
    (hlo : 1390 ≤ n.val) (hhi : n.val < 1400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_140 (n : Fin 5011)
    (hlo : 1400 ≤ n.val) (hhi : n.val < 1410) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_141 (n : Fin 5011)
    (hlo : 1410 ≤ n.val) (hhi : n.val < 1420) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_142 (n : Fin 5011)
    (hlo : 1420 ≤ n.val) (hhi : n.val < 1430) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_143 (n : Fin 5011)
    (hlo : 1430 ≤ n.val) (hhi : n.val < 1440) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_144 (n : Fin 5011)
    (hlo : 1440 ≤ n.val) (hhi : n.val < 1450) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_145 (n : Fin 5011)
    (hlo : 1450 ≤ n.val) (hhi : n.val < 1460) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_146 (n : Fin 5011)
    (hlo : 1460 ≤ n.val) (hhi : n.val < 1470) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_147 (n : Fin 5011)
    (hlo : 1470 ≤ n.val) (hhi : n.val < 1480) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_148 (n : Fin 5011)
    (hlo : 1480 ≤ n.val) (hhi : n.val < 1490) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_149 (n : Fin 5011)
    (hlo : 1490 ≤ n.val) (hhi : n.val < 1500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_150 (n : Fin 5011)
    (hlo : 1500 ≤ n.val) (hhi : n.val < 1510) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_151 (n : Fin 5011)
    (hlo : 1510 ≤ n.val) (hhi : n.val < 1520) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_152 (n : Fin 5011)
    (hlo : 1520 ≤ n.val) (hhi : n.val < 1530) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_153 (n : Fin 5011)
    (hlo : 1530 ≤ n.val) (hhi : n.val < 1540) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_154 (n : Fin 5011)
    (hlo : 1540 ≤ n.val) (hhi : n.val < 1550) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_155 (n : Fin 5011)
    (hlo : 1550 ≤ n.val) (hhi : n.val < 1560) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_156 (n : Fin 5011)
    (hlo : 1560 ≤ n.val) (hhi : n.val < 1570) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_157 (n : Fin 5011)
    (hlo : 1570 ≤ n.val) (hhi : n.val < 1580) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_158 (n : Fin 5011)
    (hlo : 1580 ≤ n.val) (hhi : n.val < 1590) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_159 (n : Fin 5011)
    (hlo : 1590 ≤ n.val) (hhi : n.val < 1600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_160 (n : Fin 5011)
    (hlo : 1600 ≤ n.val) (hhi : n.val < 1610) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_161 (n : Fin 5011)
    (hlo : 1610 ≤ n.val) (hhi : n.val < 1620) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_162 (n : Fin 5011)
    (hlo : 1620 ≤ n.val) (hhi : n.val < 1630) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_163 (n : Fin 5011)
    (hlo : 1630 ≤ n.val) (hhi : n.val < 1640) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_164 (n : Fin 5011)
    (hlo : 1640 ≤ n.val) (hhi : n.val < 1650) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_165 (n : Fin 5011)
    (hlo : 1650 ≤ n.val) (hhi : n.val < 1660) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_166 (n : Fin 5011)
    (hlo : 1660 ≤ n.val) (hhi : n.val < 1670) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_167 (n : Fin 5011)
    (hlo : 1670 ≤ n.val) (hhi : n.val < 1680) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_168 (n : Fin 5011)
    (hlo : 1680 ≤ n.val) (hhi : n.val < 1690) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_169 (n : Fin 5011)
    (hlo : 1690 ≤ n.val) (hhi : n.val < 1700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_170 (n : Fin 5011)
    (hlo : 1700 ≤ n.val) (hhi : n.val < 1710) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_171 (n : Fin 5011)
    (hlo : 1710 ≤ n.val) (hhi : n.val < 1720) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_172 (n : Fin 5011)
    (hlo : 1720 ≤ n.val) (hhi : n.val < 1730) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_173 (n : Fin 5011)
    (hlo : 1730 ≤ n.val) (hhi : n.val < 1740) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_174 (n : Fin 5011)
    (hlo : 1740 ≤ n.val) (hhi : n.val < 1750) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_175 (n : Fin 5011)
    (hlo : 1750 ≤ n.val) (hhi : n.val < 1760) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_176 (n : Fin 5011)
    (hlo : 1760 ≤ n.val) (hhi : n.val < 1770) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_177 (n : Fin 5011)
    (hlo : 1770 ≤ n.val) (hhi : n.val < 1780) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_178 (n : Fin 5011)
    (hlo : 1780 ≤ n.val) (hhi : n.val < 1790) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_179 (n : Fin 5011)
    (hlo : 1790 ≤ n.val) (hhi : n.val < 1800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_180 (n : Fin 5011)
    (hlo : 1800 ≤ n.val) (hhi : n.val < 1810) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_181 (n : Fin 5011)
    (hlo : 1810 ≤ n.val) (hhi : n.val < 1820) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_182 (n : Fin 5011)
    (hlo : 1820 ≤ n.val) (hhi : n.val < 1830) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_183 (n : Fin 5011)
    (hlo : 1830 ≤ n.val) (hhi : n.val < 1840) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_184 (n : Fin 5011)
    (hlo : 1840 ≤ n.val) (hhi : n.val < 1850) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_185 (n : Fin 5011)
    (hlo : 1850 ≤ n.val) (hhi : n.val < 1860) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_186 (n : Fin 5011)
    (hlo : 1860 ≤ n.val) (hhi : n.val < 1870) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_187 (n : Fin 5011)
    (hlo : 1870 ≤ n.val) (hhi : n.val < 1880) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_188 (n : Fin 5011)
    (hlo : 1880 ≤ n.val) (hhi : n.val < 1890) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_189 (n : Fin 5011)
    (hlo : 1890 ≤ n.val) (hhi : n.val < 1900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_190 (n : Fin 5011)
    (hlo : 1900 ≤ n.val) (hhi : n.val < 1910) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_191 (n : Fin 5011)
    (hlo : 1910 ≤ n.val) (hhi : n.val < 1920) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_192 (n : Fin 5011)
    (hlo : 1920 ≤ n.val) (hhi : n.val < 1930) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_193 (n : Fin 5011)
    (hlo : 1930 ≤ n.val) (hhi : n.val < 1940) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_194 (n : Fin 5011)
    (hlo : 1940 ≤ n.val) (hhi : n.val < 1950) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_195 (n : Fin 5011)
    (hlo : 1950 ≤ n.val) (hhi : n.val < 1960) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_196 (n : Fin 5011)
    (hlo : 1960 ≤ n.val) (hhi : n.val < 1970) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_197 (n : Fin 5011)
    (hlo : 1970 ≤ n.val) (hhi : n.val < 1980) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_198 (n : Fin 5011)
    (hlo : 1980 ≤ n.val) (hhi : n.val < 1990) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_199 (n : Fin 5011)
    (hlo : 1990 ≤ n.val) (hhi : n.val < 2000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_200 (n : Fin 5011)
    (hlo : 2000 ≤ n.val) (hhi : n.val < 2010) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_201 (n : Fin 5011)
    (hlo : 2010 ≤ n.val) (hhi : n.val < 2020) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_202 (n : Fin 5011)
    (hlo : 2020 ≤ n.val) (hhi : n.val < 2030) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_203 (n : Fin 5011)
    (hlo : 2030 ≤ n.val) (hhi : n.val < 2040) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_204 (n : Fin 5011)
    (hlo : 2040 ≤ n.val) (hhi : n.val < 2050) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_205 (n : Fin 5011)
    (hlo : 2050 ≤ n.val) (hhi : n.val < 2060) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_206 (n : Fin 5011)
    (hlo : 2060 ≤ n.val) (hhi : n.val < 2070) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_207 (n : Fin 5011)
    (hlo : 2070 ≤ n.val) (hhi : n.val < 2080) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_208 (n : Fin 5011)
    (hlo : 2080 ≤ n.val) (hhi : n.val < 2090) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_209 (n : Fin 5011)
    (hlo : 2090 ≤ n.val) (hhi : n.val < 2100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_210 (n : Fin 5011)
    (hlo : 2100 ≤ n.val) (hhi : n.val < 2110) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_211 (n : Fin 5011)
    (hlo : 2110 ≤ n.val) (hhi : n.val < 2120) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_212 (n : Fin 5011)
    (hlo : 2120 ≤ n.val) (hhi : n.val < 2130) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_213 (n : Fin 5011)
    (hlo : 2130 ≤ n.val) (hhi : n.val < 2140) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_214 (n : Fin 5011)
    (hlo : 2140 ≤ n.val) (hhi : n.val < 2150) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_215 (n : Fin 5011)
    (hlo : 2150 ≤ n.val) (hhi : n.val < 2160) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_216 (n : Fin 5011)
    (hlo : 2160 ≤ n.val) (hhi : n.val < 2170) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_217 (n : Fin 5011)
    (hlo : 2170 ≤ n.val) (hhi : n.val < 2180) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_218 (n : Fin 5011)
    (hlo : 2180 ≤ n.val) (hhi : n.val < 2190) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_219 (n : Fin 5011)
    (hlo : 2190 ≤ n.val) (hhi : n.val < 2200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_220 (n : Fin 5011)
    (hlo : 2200 ≤ n.val) (hhi : n.val < 2210) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_221 (n : Fin 5011)
    (hlo : 2210 ≤ n.val) (hhi : n.val < 2220) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_222 (n : Fin 5011)
    (hlo : 2220 ≤ n.val) (hhi : n.val < 2230) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_223 (n : Fin 5011)
    (hlo : 2230 ≤ n.val) (hhi : n.val < 2240) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_224 (n : Fin 5011)
    (hlo : 2240 ≤ n.val) (hhi : n.val < 2250) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_225 (n : Fin 5011)
    (hlo : 2250 ≤ n.val) (hhi : n.val < 2260) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_226 (n : Fin 5011)
    (hlo : 2260 ≤ n.val) (hhi : n.val < 2270) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_227 (n : Fin 5011)
    (hlo : 2270 ≤ n.val) (hhi : n.val < 2280) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_228 (n : Fin 5011)
    (hlo : 2280 ≤ n.val) (hhi : n.val < 2290) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_229 (n : Fin 5011)
    (hlo : 2290 ≤ n.val) (hhi : n.val < 2300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_230 (n : Fin 5011)
    (hlo : 2300 ≤ n.val) (hhi : n.val < 2310) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_231 (n : Fin 5011)
    (hlo : 2310 ≤ n.val) (hhi : n.val < 2320) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_232 (n : Fin 5011)
    (hlo : 2320 ≤ n.val) (hhi : n.val < 2330) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_233 (n : Fin 5011)
    (hlo : 2330 ≤ n.val) (hhi : n.val < 2340) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_234 (n : Fin 5011)
    (hlo : 2340 ≤ n.val) (hhi : n.val < 2350) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_235 (n : Fin 5011)
    (hlo : 2350 ≤ n.val) (hhi : n.val < 2360) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_236 (n : Fin 5011)
    (hlo : 2360 ≤ n.val) (hhi : n.val < 2370) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_237 (n : Fin 5011)
    (hlo : 2370 ≤ n.val) (hhi : n.val < 2380) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_238 (n : Fin 5011)
    (hlo : 2380 ≤ n.val) (hhi : n.val < 2390) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_239 (n : Fin 5011)
    (hlo : 2390 ≤ n.val) (hhi : n.val < 2400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_240 (n : Fin 5011)
    (hlo : 2400 ≤ n.val) (hhi : n.val < 2410) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_241 (n : Fin 5011)
    (hlo : 2410 ≤ n.val) (hhi : n.val < 2420) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_242 (n : Fin 5011)
    (hlo : 2420 ≤ n.val) (hhi : n.val < 2430) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_243 (n : Fin 5011)
    (hlo : 2430 ≤ n.val) (hhi : n.val < 2440) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_244 (n : Fin 5011)
    (hlo : 2440 ≤ n.val) (hhi : n.val < 2450) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_245 (n : Fin 5011)
    (hlo : 2450 ≤ n.val) (hhi : n.val < 2460) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_246 (n : Fin 5011)
    (hlo : 2460 ≤ n.val) (hhi : n.val < 2470) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_247 (n : Fin 5011)
    (hlo : 2470 ≤ n.val) (hhi : n.val < 2480) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_248 (n : Fin 5011)
    (hlo : 2480 ≤ n.val) (hhi : n.val < 2490) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_249 (n : Fin 5011)
    (hlo : 2490 ≤ n.val) (hhi : n.val < 2500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_250 (n : Fin 5011)
    (hlo : 2500 ≤ n.val) (hhi : n.val < 2510) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_251 (n : Fin 5011)
    (hlo : 2510 ≤ n.val) (hhi : n.val < 2520) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_252 (n : Fin 5011)
    (hlo : 2520 ≤ n.val) (hhi : n.val < 2530) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_253 (n : Fin 5011)
    (hlo : 2530 ≤ n.val) (hhi : n.val < 2540) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_254 (n : Fin 5011)
    (hlo : 2540 ≤ n.val) (hhi : n.val < 2550) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_255 (n : Fin 5011)
    (hlo : 2550 ≤ n.val) (hhi : n.val < 2560) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_256 (n : Fin 5011)
    (hlo : 2560 ≤ n.val) (hhi : n.val < 2570) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_257 (n : Fin 5011)
    (hlo : 2570 ≤ n.val) (hhi : n.val < 2580) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_258 (n : Fin 5011)
    (hlo : 2580 ≤ n.val) (hhi : n.val < 2590) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_259 (n : Fin 5011)
    (hlo : 2590 ≤ n.val) (hhi : n.val < 2600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_260 (n : Fin 5011)
    (hlo : 2600 ≤ n.val) (hhi : n.val < 2610) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_261 (n : Fin 5011)
    (hlo : 2610 ≤ n.val) (hhi : n.val < 2620) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_262 (n : Fin 5011)
    (hlo : 2620 ≤ n.val) (hhi : n.val < 2630) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_263 (n : Fin 5011)
    (hlo : 2630 ≤ n.val) (hhi : n.val < 2640) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_264 (n : Fin 5011)
    (hlo : 2640 ≤ n.val) (hhi : n.val < 2650) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_265 (n : Fin 5011)
    (hlo : 2650 ≤ n.val) (hhi : n.val < 2660) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_266 (n : Fin 5011)
    (hlo : 2660 ≤ n.val) (hhi : n.val < 2670) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_267 (n : Fin 5011)
    (hlo : 2670 ≤ n.val) (hhi : n.val < 2680) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_268 (n : Fin 5011)
    (hlo : 2680 ≤ n.val) (hhi : n.val < 2690) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_269 (n : Fin 5011)
    (hlo : 2690 ≤ n.val) (hhi : n.val < 2700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_270 (n : Fin 5011)
    (hlo : 2700 ≤ n.val) (hhi : n.val < 2710) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_271 (n : Fin 5011)
    (hlo : 2710 ≤ n.val) (hhi : n.val < 2720) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_272 (n : Fin 5011)
    (hlo : 2720 ≤ n.val) (hhi : n.val < 2730) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_273 (n : Fin 5011)
    (hlo : 2730 ≤ n.val) (hhi : n.val < 2740) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_274 (n : Fin 5011)
    (hlo : 2740 ≤ n.val) (hhi : n.val < 2750) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_275 (n : Fin 5011)
    (hlo : 2750 ≤ n.val) (hhi : n.val < 2760) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_276 (n : Fin 5011)
    (hlo : 2760 ≤ n.val) (hhi : n.val < 2770) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_277 (n : Fin 5011)
    (hlo : 2770 ≤ n.val) (hhi : n.val < 2780) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_278 (n : Fin 5011)
    (hlo : 2780 ≤ n.val) (hhi : n.val < 2790) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_279 (n : Fin 5011)
    (hlo : 2790 ≤ n.val) (hhi : n.val < 2800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_280 (n : Fin 5011)
    (hlo : 2800 ≤ n.val) (hhi : n.val < 2810) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_281 (n : Fin 5011)
    (hlo : 2810 ≤ n.val) (hhi : n.val < 2820) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_282 (n : Fin 5011)
    (hlo : 2820 ≤ n.val) (hhi : n.val < 2830) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_283 (n : Fin 5011)
    (hlo : 2830 ≤ n.val) (hhi : n.val < 2840) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_284 (n : Fin 5011)
    (hlo : 2840 ≤ n.val) (hhi : n.val < 2850) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_285 (n : Fin 5011)
    (hlo : 2850 ≤ n.val) (hhi : n.val < 2860) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_286 (n : Fin 5011)
    (hlo : 2860 ≤ n.val) (hhi : n.val < 2870) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_287 (n : Fin 5011)
    (hlo : 2870 ≤ n.val) (hhi : n.val < 2880) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_288 (n : Fin 5011)
    (hlo : 2880 ≤ n.val) (hhi : n.val < 2890) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_289 (n : Fin 5011)
    (hlo : 2890 ≤ n.val) (hhi : n.val < 2900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_290 (n : Fin 5011)
    (hlo : 2900 ≤ n.val) (hhi : n.val < 2910) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_291 (n : Fin 5011)
    (hlo : 2910 ≤ n.val) (hhi : n.val < 2920) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_292 (n : Fin 5011)
    (hlo : 2920 ≤ n.val) (hhi : n.val < 2930) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_293 (n : Fin 5011)
    (hlo : 2930 ≤ n.val) (hhi : n.val < 2940) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_294 (n : Fin 5011)
    (hlo : 2940 ≤ n.val) (hhi : n.val < 2950) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_295 (n : Fin 5011)
    (hlo : 2950 ≤ n.val) (hhi : n.val < 2960) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_296 (n : Fin 5011)
    (hlo : 2960 ≤ n.val) (hhi : n.val < 2970) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_297 (n : Fin 5011)
    (hlo : 2970 ≤ n.val) (hhi : n.val < 2980) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_298 (n : Fin 5011)
    (hlo : 2980 ≤ n.val) (hhi : n.val < 2990) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_299 (n : Fin 5011)
    (hlo : 2990 ≤ n.val) (hhi : n.val < 3000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_300 (n : Fin 5011)
    (hlo : 3000 ≤ n.val) (hhi : n.val < 3010) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_301 (n : Fin 5011)
    (hlo : 3010 ≤ n.val) (hhi : n.val < 3020) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_302 (n : Fin 5011)
    (hlo : 3020 ≤ n.val) (hhi : n.val < 3030) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_303 (n : Fin 5011)
    (hlo : 3030 ≤ n.val) (hhi : n.val < 3040) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_304 (n : Fin 5011)
    (hlo : 3040 ≤ n.val) (hhi : n.val < 3050) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_305 (n : Fin 5011)
    (hlo : 3050 ≤ n.val) (hhi : n.val < 3060) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_306 (n : Fin 5011)
    (hlo : 3060 ≤ n.val) (hhi : n.val < 3070) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_307 (n : Fin 5011)
    (hlo : 3070 ≤ n.val) (hhi : n.val < 3080) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_308 (n : Fin 5011)
    (hlo : 3080 ≤ n.val) (hhi : n.val < 3090) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_309 (n : Fin 5011)
    (hlo : 3090 ≤ n.val) (hhi : n.val < 3100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_310 (n : Fin 5011)
    (hlo : 3100 ≤ n.val) (hhi : n.val < 3110) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_311 (n : Fin 5011)
    (hlo : 3110 ≤ n.val) (hhi : n.val < 3120) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_312 (n : Fin 5011)
    (hlo : 3120 ≤ n.val) (hhi : n.val < 3130) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_313 (n : Fin 5011)
    (hlo : 3130 ≤ n.val) (hhi : n.val < 3140) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_314 (n : Fin 5011)
    (hlo : 3140 ≤ n.val) (hhi : n.val < 3150) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_315 (n : Fin 5011)
    (hlo : 3150 ≤ n.val) (hhi : n.val < 3160) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_316 (n : Fin 5011)
    (hlo : 3160 ≤ n.val) (hhi : n.val < 3170) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_317 (n : Fin 5011)
    (hlo : 3170 ≤ n.val) (hhi : n.val < 3180) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_318 (n : Fin 5011)
    (hlo : 3180 ≤ n.val) (hhi : n.val < 3190) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_319 (n : Fin 5011)
    (hlo : 3190 ≤ n.val) (hhi : n.val < 3200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_320 (n : Fin 5011)
    (hlo : 3200 ≤ n.val) (hhi : n.val < 3210) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_321 (n : Fin 5011)
    (hlo : 3210 ≤ n.val) (hhi : n.val < 3220) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_322 (n : Fin 5011)
    (hlo : 3220 ≤ n.val) (hhi : n.val < 3230) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_323 (n : Fin 5011)
    (hlo : 3230 ≤ n.val) (hhi : n.val < 3240) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_324 (n : Fin 5011)
    (hlo : 3240 ≤ n.val) (hhi : n.val < 3250) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_325 (n : Fin 5011)
    (hlo : 3250 ≤ n.val) (hhi : n.val < 3260) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_326 (n : Fin 5011)
    (hlo : 3260 ≤ n.val) (hhi : n.val < 3270) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_327 (n : Fin 5011)
    (hlo : 3270 ≤ n.val) (hhi : n.val < 3280) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_328 (n : Fin 5011)
    (hlo : 3280 ≤ n.val) (hhi : n.val < 3290) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_329 (n : Fin 5011)
    (hlo : 3290 ≤ n.val) (hhi : n.val < 3300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_330 (n : Fin 5011)
    (hlo : 3300 ≤ n.val) (hhi : n.val < 3310) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_331 (n : Fin 5011)
    (hlo : 3310 ≤ n.val) (hhi : n.val < 3320) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_332 (n : Fin 5011)
    (hlo : 3320 ≤ n.val) (hhi : n.val < 3330) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_333 (n : Fin 5011)
    (hlo : 3330 ≤ n.val) (hhi : n.val < 3340) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_334 (n : Fin 5011)
    (hlo : 3340 ≤ n.val) (hhi : n.val < 3350) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_335 (n : Fin 5011)
    (hlo : 3350 ≤ n.val) (hhi : n.val < 3360) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_336 (n : Fin 5011)
    (hlo : 3360 ≤ n.val) (hhi : n.val < 3370) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_337 (n : Fin 5011)
    (hlo : 3370 ≤ n.val) (hhi : n.val < 3380) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_338 (n : Fin 5011)
    (hlo : 3380 ≤ n.val) (hhi : n.val < 3390) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_339 (n : Fin 5011)
    (hlo : 3390 ≤ n.val) (hhi : n.val < 3400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_340 (n : Fin 5011)
    (hlo : 3400 ≤ n.val) (hhi : n.val < 3410) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_341 (n : Fin 5011)
    (hlo : 3410 ≤ n.val) (hhi : n.val < 3420) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_342 (n : Fin 5011)
    (hlo : 3420 ≤ n.val) (hhi : n.val < 3430) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_343 (n : Fin 5011)
    (hlo : 3430 ≤ n.val) (hhi : n.val < 3440) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_344 (n : Fin 5011)
    (hlo : 3440 ≤ n.val) (hhi : n.val < 3450) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_345 (n : Fin 5011)
    (hlo : 3450 ≤ n.val) (hhi : n.val < 3460) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_346 (n : Fin 5011)
    (hlo : 3460 ≤ n.val) (hhi : n.val < 3470) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_347 (n : Fin 5011)
    (hlo : 3470 ≤ n.val) (hhi : n.val < 3480) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_348 (n : Fin 5011)
    (hlo : 3480 ≤ n.val) (hhi : n.val < 3490) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_349 (n : Fin 5011)
    (hlo : 3490 ≤ n.val) (hhi : n.val < 3500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_350 (n : Fin 5011)
    (hlo : 3500 ≤ n.val) (hhi : n.val < 3510) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_351 (n : Fin 5011)
    (hlo : 3510 ≤ n.val) (hhi : n.val < 3520) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_352 (n : Fin 5011)
    (hlo : 3520 ≤ n.val) (hhi : n.val < 3530) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_353 (n : Fin 5011)
    (hlo : 3530 ≤ n.val) (hhi : n.val < 3540) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_354 (n : Fin 5011)
    (hlo : 3540 ≤ n.val) (hhi : n.val < 3550) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_355 (n : Fin 5011)
    (hlo : 3550 ≤ n.val) (hhi : n.val < 3560) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_356 (n : Fin 5011)
    (hlo : 3560 ≤ n.val) (hhi : n.val < 3570) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_357 (n : Fin 5011)
    (hlo : 3570 ≤ n.val) (hhi : n.val < 3580) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_358 (n : Fin 5011)
    (hlo : 3580 ≤ n.val) (hhi : n.val < 3590) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_359 (n : Fin 5011)
    (hlo : 3590 ≤ n.val) (hhi : n.val < 3600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_360 (n : Fin 5011)
    (hlo : 3600 ≤ n.val) (hhi : n.val < 3610) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_361 (n : Fin 5011)
    (hlo : 3610 ≤ n.val) (hhi : n.val < 3620) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_362 (n : Fin 5011)
    (hlo : 3620 ≤ n.val) (hhi : n.val < 3630) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_363 (n : Fin 5011)
    (hlo : 3630 ≤ n.val) (hhi : n.val < 3640) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_364 (n : Fin 5011)
    (hlo : 3640 ≤ n.val) (hhi : n.val < 3650) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_365 (n : Fin 5011)
    (hlo : 3650 ≤ n.val) (hhi : n.val < 3660) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_366 (n : Fin 5011)
    (hlo : 3660 ≤ n.val) (hhi : n.val < 3670) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_367 (n : Fin 5011)
    (hlo : 3670 ≤ n.val) (hhi : n.val < 3680) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_368 (n : Fin 5011)
    (hlo : 3680 ≤ n.val) (hhi : n.val < 3690) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_369 (n : Fin 5011)
    (hlo : 3690 ≤ n.val) (hhi : n.val < 3700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_370 (n : Fin 5011)
    (hlo : 3700 ≤ n.val) (hhi : n.val < 3710) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_371 (n : Fin 5011)
    (hlo : 3710 ≤ n.val) (hhi : n.val < 3720) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_372 (n : Fin 5011)
    (hlo : 3720 ≤ n.val) (hhi : n.val < 3730) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_373 (n : Fin 5011)
    (hlo : 3730 ≤ n.val) (hhi : n.val < 3740) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_374 (n : Fin 5011)
    (hlo : 3740 ≤ n.val) (hhi : n.val < 3750) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_375 (n : Fin 5011)
    (hlo : 3750 ≤ n.val) (hhi : n.val < 3760) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_376 (n : Fin 5011)
    (hlo : 3760 ≤ n.val) (hhi : n.val < 3770) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_377 (n : Fin 5011)
    (hlo : 3770 ≤ n.val) (hhi : n.val < 3780) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_378 (n : Fin 5011)
    (hlo : 3780 ≤ n.val) (hhi : n.val < 3790) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_379 (n : Fin 5011)
    (hlo : 3790 ≤ n.val) (hhi : n.val < 3800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_380 (n : Fin 5011)
    (hlo : 3800 ≤ n.val) (hhi : n.val < 3810) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_381 (n : Fin 5011)
    (hlo : 3810 ≤ n.val) (hhi : n.val < 3820) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_382 (n : Fin 5011)
    (hlo : 3820 ≤ n.val) (hhi : n.val < 3830) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_383 (n : Fin 5011)
    (hlo : 3830 ≤ n.val) (hhi : n.val < 3840) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_384 (n : Fin 5011)
    (hlo : 3840 ≤ n.val) (hhi : n.val < 3850) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_385 (n : Fin 5011)
    (hlo : 3850 ≤ n.val) (hhi : n.val < 3860) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_386 (n : Fin 5011)
    (hlo : 3860 ≤ n.val) (hhi : n.val < 3870) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_387 (n : Fin 5011)
    (hlo : 3870 ≤ n.val) (hhi : n.val < 3880) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_388 (n : Fin 5011)
    (hlo : 3880 ≤ n.val) (hhi : n.val < 3890) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_389 (n : Fin 5011)
    (hlo : 3890 ≤ n.val) (hhi : n.val < 3900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_390 (n : Fin 5011)
    (hlo : 3900 ≤ n.val) (hhi : n.val < 3910) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_391 (n : Fin 5011)
    (hlo : 3910 ≤ n.val) (hhi : n.val < 3920) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_392 (n : Fin 5011)
    (hlo : 3920 ≤ n.val) (hhi : n.val < 3930) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_393 (n : Fin 5011)
    (hlo : 3930 ≤ n.val) (hhi : n.val < 3940) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_394 (n : Fin 5011)
    (hlo : 3940 ≤ n.val) (hhi : n.val < 3950) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_395 (n : Fin 5011)
    (hlo : 3950 ≤ n.val) (hhi : n.val < 3960) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_396 (n : Fin 5011)
    (hlo : 3960 ≤ n.val) (hhi : n.val < 3970) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_397 (n : Fin 5011)
    (hlo : 3970 ≤ n.val) (hhi : n.val < 3980) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_398 (n : Fin 5011)
    (hlo : 3980 ≤ n.val) (hhi : n.val < 3990) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_399 (n : Fin 5011)
    (hlo : 3990 ≤ n.val) (hhi : n.val < 4000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_400 (n : Fin 5011)
    (hlo : 4000 ≤ n.val) (hhi : n.val < 4010) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_401 (n : Fin 5011)
    (hlo : 4010 ≤ n.val) (hhi : n.val < 4020) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_402 (n : Fin 5011)
    (hlo : 4020 ≤ n.val) (hhi : n.val < 4030) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_403 (n : Fin 5011)
    (hlo : 4030 ≤ n.val) (hhi : n.val < 4040) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_404 (n : Fin 5011)
    (hlo : 4040 ≤ n.val) (hhi : n.val < 4050) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_405 (n : Fin 5011)
    (hlo : 4050 ≤ n.val) (hhi : n.val < 4060) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_406 (n : Fin 5011)
    (hlo : 4060 ≤ n.val) (hhi : n.val < 4070) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_407 (n : Fin 5011)
    (hlo : 4070 ≤ n.val) (hhi : n.val < 4080) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_408 (n : Fin 5011)
    (hlo : 4080 ≤ n.val) (hhi : n.val < 4090) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_409 (n : Fin 5011)
    (hlo : 4090 ≤ n.val) (hhi : n.val < 4100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_410 (n : Fin 5011)
    (hlo : 4100 ≤ n.val) (hhi : n.val < 4110) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_411 (n : Fin 5011)
    (hlo : 4110 ≤ n.val) (hhi : n.val < 4120) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_412 (n : Fin 5011)
    (hlo : 4120 ≤ n.val) (hhi : n.val < 4130) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_413 (n : Fin 5011)
    (hlo : 4130 ≤ n.val) (hhi : n.val < 4140) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_414 (n : Fin 5011)
    (hlo : 4140 ≤ n.val) (hhi : n.val < 4150) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_415 (n : Fin 5011)
    (hlo : 4150 ≤ n.val) (hhi : n.val < 4160) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_416 (n : Fin 5011)
    (hlo : 4160 ≤ n.val) (hhi : n.val < 4170) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_417 (n : Fin 5011)
    (hlo : 4170 ≤ n.val) (hhi : n.val < 4180) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_418 (n : Fin 5011)
    (hlo : 4180 ≤ n.val) (hhi : n.val < 4190) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_419 (n : Fin 5011)
    (hlo : 4190 ≤ n.val) (hhi : n.val < 4200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_420 (n : Fin 5011)
    (hlo : 4200 ≤ n.val) (hhi : n.val < 4210) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_421 (n : Fin 5011)
    (hlo : 4210 ≤ n.val) (hhi : n.val < 4220) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_422 (n : Fin 5011)
    (hlo : 4220 ≤ n.val) (hhi : n.val < 4230) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_423 (n : Fin 5011)
    (hlo : 4230 ≤ n.val) (hhi : n.val < 4240) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_424 (n : Fin 5011)
    (hlo : 4240 ≤ n.val) (hhi : n.val < 4250) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_425 (n : Fin 5011)
    (hlo : 4250 ≤ n.val) (hhi : n.val < 4260) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_426 (n : Fin 5011)
    (hlo : 4260 ≤ n.val) (hhi : n.val < 4270) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_427 (n : Fin 5011)
    (hlo : 4270 ≤ n.val) (hhi : n.val < 4280) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_428 (n : Fin 5011)
    (hlo : 4280 ≤ n.val) (hhi : n.val < 4290) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_429 (n : Fin 5011)
    (hlo : 4290 ≤ n.val) (hhi : n.val < 4300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_430 (n : Fin 5011)
    (hlo : 4300 ≤ n.val) (hhi : n.val < 4310) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_431 (n : Fin 5011)
    (hlo : 4310 ≤ n.val) (hhi : n.val < 4320) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_432 (n : Fin 5011)
    (hlo : 4320 ≤ n.val) (hhi : n.val < 4330) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_433 (n : Fin 5011)
    (hlo : 4330 ≤ n.val) (hhi : n.val < 4340) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_434 (n : Fin 5011)
    (hlo : 4340 ≤ n.val) (hhi : n.val < 4350) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_435 (n : Fin 5011)
    (hlo : 4350 ≤ n.val) (hhi : n.val < 4360) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_436 (n : Fin 5011)
    (hlo : 4360 ≤ n.val) (hhi : n.val < 4370) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_437 (n : Fin 5011)
    (hlo : 4370 ≤ n.val) (hhi : n.val < 4380) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_438 (n : Fin 5011)
    (hlo : 4380 ≤ n.val) (hhi : n.val < 4390) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_439 (n : Fin 5011)
    (hlo : 4390 ≤ n.val) (hhi : n.val < 4400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_440 (n : Fin 5011)
    (hlo : 4400 ≤ n.val) (hhi : n.val < 4410) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_441 (n : Fin 5011)
    (hlo : 4410 ≤ n.val) (hhi : n.val < 4420) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_442 (n : Fin 5011)
    (hlo : 4420 ≤ n.val) (hhi : n.val < 4430) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_443 (n : Fin 5011)
    (hlo : 4430 ≤ n.val) (hhi : n.val < 4440) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_444 (n : Fin 5011)
    (hlo : 4440 ≤ n.val) (hhi : n.val < 4450) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_445 (n : Fin 5011)
    (hlo : 4450 ≤ n.val) (hhi : n.val < 4460) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_446 (n : Fin 5011)
    (hlo : 4460 ≤ n.val) (hhi : n.val < 4470) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_447 (n : Fin 5011)
    (hlo : 4470 ≤ n.val) (hhi : n.val < 4480) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_448 (n : Fin 5011)
    (hlo : 4480 ≤ n.val) (hhi : n.val < 4490) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_449 (n : Fin 5011)
    (hlo : 4490 ≤ n.val) (hhi : n.val < 4500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_450 (n : Fin 5011)
    (hlo : 4500 ≤ n.val) (hhi : n.val < 4510) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_451 (n : Fin 5011)
    (hlo : 4510 ≤ n.val) (hhi : n.val < 4520) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_452 (n : Fin 5011)
    (hlo : 4520 ≤ n.val) (hhi : n.val < 4530) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_453 (n : Fin 5011)
    (hlo : 4530 ≤ n.val) (hhi : n.val < 4540) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_454 (n : Fin 5011)
    (hlo : 4540 ≤ n.val) (hhi : n.val < 4550) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_455 (n : Fin 5011)
    (hlo : 4550 ≤ n.val) (hhi : n.val < 4560) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_456 (n : Fin 5011)
    (hlo : 4560 ≤ n.val) (hhi : n.val < 4570) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_457 (n : Fin 5011)
    (hlo : 4570 ≤ n.val) (hhi : n.val < 4580) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_458 (n : Fin 5011)
    (hlo : 4580 ≤ n.val) (hhi : n.val < 4590) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_459 (n : Fin 5011)
    (hlo : 4590 ≤ n.val) (hhi : n.val < 4600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_460 (n : Fin 5011)
    (hlo : 4600 ≤ n.val) (hhi : n.val < 4610) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_461 (n : Fin 5011)
    (hlo : 4610 ≤ n.val) (hhi : n.val < 4620) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_462 (n : Fin 5011)
    (hlo : 4620 ≤ n.val) (hhi : n.val < 4630) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_463 (n : Fin 5011)
    (hlo : 4630 ≤ n.val) (hhi : n.val < 4640) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_464 (n : Fin 5011)
    (hlo : 4640 ≤ n.val) (hhi : n.val < 4650) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_465 (n : Fin 5011)
    (hlo : 4650 ≤ n.val) (hhi : n.val < 4660) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_466 (n : Fin 5011)
    (hlo : 4660 ≤ n.val) (hhi : n.val < 4670) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_467 (n : Fin 5011)
    (hlo : 4670 ≤ n.val) (hhi : n.val < 4680) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_468 (n : Fin 5011)
    (hlo : 4680 ≤ n.val) (hhi : n.val < 4690) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_469 (n : Fin 5011)
    (hlo : 4690 ≤ n.val) (hhi : n.val < 4700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_470 (n : Fin 5011)
    (hlo : 4700 ≤ n.val) (hhi : n.val < 4710) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_471 (n : Fin 5011)
    (hlo : 4710 ≤ n.val) (hhi : n.val < 4720) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_472 (n : Fin 5011)
    (hlo : 4720 ≤ n.val) (hhi : n.val < 4730) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_473 (n : Fin 5011)
    (hlo : 4730 ≤ n.val) (hhi : n.val < 4740) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_474 (n : Fin 5011)
    (hlo : 4740 ≤ n.val) (hhi : n.val < 4750) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_475 (n : Fin 5011)
    (hlo : 4750 ≤ n.val) (hhi : n.val < 4760) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_476 (n : Fin 5011)
    (hlo : 4760 ≤ n.val) (hhi : n.val < 4770) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_477 (n : Fin 5011)
    (hlo : 4770 ≤ n.val) (hhi : n.val < 4780) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_478 (n : Fin 5011)
    (hlo : 4780 ≤ n.val) (hhi : n.val < 4790) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_479 (n : Fin 5011)
    (hlo : 4790 ≤ n.val) (hhi : n.val < 4800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_480 (n : Fin 5011)
    (hlo : 4800 ≤ n.val) (hhi : n.val < 4810) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_481 (n : Fin 5011)
    (hlo : 4810 ≤ n.val) (hhi : n.val < 4820) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_482 (n : Fin 5011)
    (hlo : 4820 ≤ n.val) (hhi : n.val < 4830) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_483 (n : Fin 5011)
    (hlo : 4830 ≤ n.val) (hhi : n.val < 4840) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_484 (n : Fin 5011)
    (hlo : 4840 ≤ n.val) (hhi : n.val < 4850) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_485 (n : Fin 5011)
    (hlo : 4850 ≤ n.val) (hhi : n.val < 4860) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_486 (n : Fin 5011)
    (hlo : 4860 ≤ n.val) (hhi : n.val < 4870) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_487 (n : Fin 5011)
    (hlo : 4870 ≤ n.val) (hhi : n.val < 4880) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_488 (n : Fin 5011)
    (hlo : 4880 ≤ n.val) (hhi : n.val < 4890) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_489 (n : Fin 5011)
    (hlo : 4890 ≤ n.val) (hhi : n.val < 4900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_490 (n : Fin 5011)
    (hlo : 4900 ≤ n.val) (hhi : n.val < 4910) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_491 (n : Fin 5011)
    (hlo : 4910 ≤ n.val) (hhi : n.val < 4920) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_492 (n : Fin 5011)
    (hlo : 4920 ≤ n.val) (hhi : n.val < 4930) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_493 (n : Fin 5011)
    (hlo : 4930 ≤ n.val) (hhi : n.val < 4940) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_494 (n : Fin 5011)
    (hlo : 4940 ≤ n.val) (hhi : n.val < 4950) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_495 (n : Fin 5011)
    (hlo : 4950 ≤ n.val) (hhi : n.val < 4960) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_496 (n : Fin 5011)
    (hlo : 4960 ≤ n.val) (hhi : n.val < 4970) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_497 (n : Fin 5011)
    (hlo : 4970 ≤ n.val) (hhi : n.val < 4980) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_498 (n : Fin 5011)
    (hlo : 4980 ≤ n.val) (hhi : n.val < 4990) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_499 (n : Fin 5011)
    (hlo : 4990 ≤ n.val) (hhi : n.val < 5000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_500 (n : Fin 5011)
    (hlo : 5000 ≤ n.val) (hhi : n.val < 5010) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
private theorem mem_sub_501 (n : Fin 5011)
    (hlo : 5010 ≤ n.val) (hhi : n.val < 5011) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;> decide +kernel +revert
theorem mem_iff_block00
    (n : Fin 5011)
    (hlo : 0 ≤ n.val) (hhi : n.val < 100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 10 ∨ (10 ≤ n.val ∧ n.val < 20) ∨ (20 ≤ n.val ∧ n.val < 30) ∨ (30 ≤ n.val ∧ n.val < 40) ∨ (40 ≤ n.val ∧ n.val < 50) ∨ (50 ≤ n.val ∧ n.val < 60) ∨ (60 ≤ n.val ∧ n.val < 70) ∨ (70 ≤ n.val ∧ n.val < 80) ∨ (80 ≤ n.val ∧ n.val < 90) ∨ (90 ≤ n.val ∧ n.val < 100) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_000 n hlo h0
  · exact mem_sub_001 n h1.1 h1.2
  · exact mem_sub_002 n h2.1 h2.2
  · exact mem_sub_003 n h3.1 h3.2
  · exact mem_sub_004 n h4.1 h4.2
  · exact mem_sub_005 n h5.1 h5.2
  · exact mem_sub_006 n h6.1 h6.2
  · exact mem_sub_007 n h7.1 h7.2
  · exact mem_sub_008 n h8.1 h8.2
  · exact mem_sub_009 n h9.1 h9.2

theorem mem_iff_block01
    (n : Fin 5011)
    (hlo : 100 ≤ n.val) (hhi : n.val < 200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 20 ∨ (110 ≤ n.val ∧ n.val < 120) ∨ (120 ≤ n.val ∧ n.val < 130) ∨ (130 ≤ n.val ∧ n.val < 140) ∨ (140 ≤ n.val ∧ n.val < 150) ∨ (150 ≤ n.val ∧ n.val < 160) ∨ (160 ≤ n.val ∧ n.val < 170) ∨ (170 ≤ n.val ∧ n.val < 180) ∨ (180 ≤ n.val ∧ n.val < 190) ∨ (190 ≤ n.val ∧ n.val < 200) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_010 n hlo h0
  · exact mem_sub_011 n h1.1 h1.2
  · exact mem_sub_012 n h2.1 h2.2
  · exact mem_sub_013 n h3.1 h3.2
  · exact mem_sub_014 n h4.1 h4.2
  · exact mem_sub_015 n h5.1 h5.2
  · exact mem_sub_016 n h6.1 h6.2
  · exact mem_sub_017 n h7.1 h7.2
  · exact mem_sub_018 n h8.1 h8.2
  · exact mem_sub_019 n h9.1 h9.2

theorem mem_iff_block02
    (n : Fin 5011)
    (hlo : 200 ≤ n.val) (hhi : n.val < 300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 30 ∨ (210 ≤ n.val ∧ n.val < 220) ∨ (220 ≤ n.val ∧ n.val < 230) ∨ (230 ≤ n.val ∧ n.val < 240) ∨ (240 ≤ n.val ∧ n.val < 250) ∨ (250 ≤ n.val ∧ n.val < 260) ∨ (260 ≤ n.val ∧ n.val < 270) ∨ (270 ≤ n.val ∧ n.val < 280) ∨ (280 ≤ n.val ∧ n.val < 290) ∨ (290 ≤ n.val ∧ n.val < 300) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_020 n hlo h0
  · exact mem_sub_021 n h1.1 h1.2
  · exact mem_sub_022 n h2.1 h2.2
  · exact mem_sub_023 n h3.1 h3.2
  · exact mem_sub_024 n h4.1 h4.2
  · exact mem_sub_025 n h5.1 h5.2
  · exact mem_sub_026 n h6.1 h6.2
  · exact mem_sub_027 n h7.1 h7.2
  · exact mem_sub_028 n h8.1 h8.2
  · exact mem_sub_029 n h9.1 h9.2

theorem mem_iff_block03
    (n : Fin 5011)
    (hlo : 300 ≤ n.val) (hhi : n.val < 400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 40 ∨ (310 ≤ n.val ∧ n.val < 320) ∨ (320 ≤ n.val ∧ n.val < 330) ∨ (330 ≤ n.val ∧ n.val < 340) ∨ (340 ≤ n.val ∧ n.val < 350) ∨ (350 ≤ n.val ∧ n.val < 360) ∨ (360 ≤ n.val ∧ n.val < 370) ∨ (370 ≤ n.val ∧ n.val < 380) ∨ (380 ≤ n.val ∧ n.val < 390) ∨ (390 ≤ n.val ∧ n.val < 400) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_030 n hlo h0
  · exact mem_sub_031 n h1.1 h1.2
  · exact mem_sub_032 n h2.1 h2.2
  · exact mem_sub_033 n h3.1 h3.2
  · exact mem_sub_034 n h4.1 h4.2
  · exact mem_sub_035 n h5.1 h5.2
  · exact mem_sub_036 n h6.1 h6.2
  · exact mem_sub_037 n h7.1 h7.2
  · exact mem_sub_038 n h8.1 h8.2
  · exact mem_sub_039 n h9.1 h9.2

theorem mem_iff_block04
    (n : Fin 5011)
    (hlo : 400 ≤ n.val) (hhi : n.val < 500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 50 ∨ (410 ≤ n.val ∧ n.val < 420) ∨ (420 ≤ n.val ∧ n.val < 430) ∨ (430 ≤ n.val ∧ n.val < 440) ∨ (440 ≤ n.val ∧ n.val < 450) ∨ (450 ≤ n.val ∧ n.val < 460) ∨ (460 ≤ n.val ∧ n.val < 470) ∨ (470 ≤ n.val ∧ n.val < 480) ∨ (480 ≤ n.val ∧ n.val < 490) ∨ (490 ≤ n.val ∧ n.val < 500) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_040 n hlo h0
  · exact mem_sub_041 n h1.1 h1.2
  · exact mem_sub_042 n h2.1 h2.2
  · exact mem_sub_043 n h3.1 h3.2
  · exact mem_sub_044 n h4.1 h4.2
  · exact mem_sub_045 n h5.1 h5.2
  · exact mem_sub_046 n h6.1 h6.2
  · exact mem_sub_047 n h7.1 h7.2
  · exact mem_sub_048 n h8.1 h8.2
  · exact mem_sub_049 n h9.1 h9.2

theorem mem_iff_block05
    (n : Fin 5011)
    (hlo : 500 ≤ n.val) (hhi : n.val < 600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 60 ∨ (510 ≤ n.val ∧ n.val < 520) ∨ (520 ≤ n.val ∧ n.val < 530) ∨ (530 ≤ n.val ∧ n.val < 540) ∨ (540 ≤ n.val ∧ n.val < 550) ∨ (550 ≤ n.val ∧ n.val < 560) ∨ (560 ≤ n.val ∧ n.val < 570) ∨ (570 ≤ n.val ∧ n.val < 580) ∨ (580 ≤ n.val ∧ n.val < 590) ∨ (590 ≤ n.val ∧ n.val < 600) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_050 n hlo h0
  · exact mem_sub_051 n h1.1 h1.2
  · exact mem_sub_052 n h2.1 h2.2
  · exact mem_sub_053 n h3.1 h3.2
  · exact mem_sub_054 n h4.1 h4.2
  · exact mem_sub_055 n h5.1 h5.2
  · exact mem_sub_056 n h6.1 h6.2
  · exact mem_sub_057 n h7.1 h7.2
  · exact mem_sub_058 n h8.1 h8.2
  · exact mem_sub_059 n h9.1 h9.2

theorem mem_iff_block06
    (n : Fin 5011)
    (hlo : 600 ≤ n.val) (hhi : n.val < 700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 70 ∨ (610 ≤ n.val ∧ n.val < 620) ∨ (620 ≤ n.val ∧ n.val < 630) ∨ (630 ≤ n.val ∧ n.val < 640) ∨ (640 ≤ n.val ∧ n.val < 650) ∨ (650 ≤ n.val ∧ n.val < 660) ∨ (660 ≤ n.val ∧ n.val < 670) ∨ (670 ≤ n.val ∧ n.val < 680) ∨ (680 ≤ n.val ∧ n.val < 690) ∨ (690 ≤ n.val ∧ n.val < 700) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_060 n hlo h0
  · exact mem_sub_061 n h1.1 h1.2
  · exact mem_sub_062 n h2.1 h2.2
  · exact mem_sub_063 n h3.1 h3.2
  · exact mem_sub_064 n h4.1 h4.2
  · exact mem_sub_065 n h5.1 h5.2
  · exact mem_sub_066 n h6.1 h6.2
  · exact mem_sub_067 n h7.1 h7.2
  · exact mem_sub_068 n h8.1 h8.2
  · exact mem_sub_069 n h9.1 h9.2

theorem mem_iff_block07
    (n : Fin 5011)
    (hlo : 700 ≤ n.val) (hhi : n.val < 800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 80 ∨ (710 ≤ n.val ∧ n.val < 720) ∨ (720 ≤ n.val ∧ n.val < 730) ∨ (730 ≤ n.val ∧ n.val < 740) ∨ (740 ≤ n.val ∧ n.val < 750) ∨ (750 ≤ n.val ∧ n.val < 760) ∨ (760 ≤ n.val ∧ n.val < 770) ∨ (770 ≤ n.val ∧ n.val < 780) ∨ (780 ≤ n.val ∧ n.val < 790) ∨ (790 ≤ n.val ∧ n.val < 800) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_070 n hlo h0
  · exact mem_sub_071 n h1.1 h1.2
  · exact mem_sub_072 n h2.1 h2.2
  · exact mem_sub_073 n h3.1 h3.2
  · exact mem_sub_074 n h4.1 h4.2
  · exact mem_sub_075 n h5.1 h5.2
  · exact mem_sub_076 n h6.1 h6.2
  · exact mem_sub_077 n h7.1 h7.2
  · exact mem_sub_078 n h8.1 h8.2
  · exact mem_sub_079 n h9.1 h9.2

theorem mem_iff_block08
    (n : Fin 5011)
    (hlo : 800 ≤ n.val) (hhi : n.val < 900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 90 ∨ (810 ≤ n.val ∧ n.val < 820) ∨ (820 ≤ n.val ∧ n.val < 830) ∨ (830 ≤ n.val ∧ n.val < 840) ∨ (840 ≤ n.val ∧ n.val < 850) ∨ (850 ≤ n.val ∧ n.val < 860) ∨ (860 ≤ n.val ∧ n.val < 870) ∨ (870 ≤ n.val ∧ n.val < 880) ∨ (880 ≤ n.val ∧ n.val < 890) ∨ (890 ≤ n.val ∧ n.val < 900) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_080 n hlo h0
  · exact mem_sub_081 n h1.1 h1.2
  · exact mem_sub_082 n h2.1 h2.2
  · exact mem_sub_083 n h3.1 h3.2
  · exact mem_sub_084 n h4.1 h4.2
  · exact mem_sub_085 n h5.1 h5.2
  · exact mem_sub_086 n h6.1 h6.2
  · exact mem_sub_087 n h7.1 h7.2
  · exact mem_sub_088 n h8.1 h8.2
  · exact mem_sub_089 n h9.1 h9.2

theorem mem_iff_block09
    (n : Fin 5011)
    (hlo : 900 ≤ n.val) (hhi : n.val < 1000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 100 ∨ (910 ≤ n.val ∧ n.val < 920) ∨ (920 ≤ n.val ∧ n.val < 930) ∨ (930 ≤ n.val ∧ n.val < 940) ∨ (940 ≤ n.val ∧ n.val < 950) ∨ (950 ≤ n.val ∧ n.val < 960) ∨ (960 ≤ n.val ∧ n.val < 970) ∨ (970 ≤ n.val ∧ n.val < 980) ∨ (980 ≤ n.val ∧ n.val < 990) ∨ (990 ≤ n.val ∧ n.val < 1000) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_090 n hlo h0
  · exact mem_sub_091 n h1.1 h1.2
  · exact mem_sub_092 n h2.1 h2.2
  · exact mem_sub_093 n h3.1 h3.2
  · exact mem_sub_094 n h4.1 h4.2
  · exact mem_sub_095 n h5.1 h5.2
  · exact mem_sub_096 n h6.1 h6.2
  · exact mem_sub_097 n h7.1 h7.2
  · exact mem_sub_098 n h8.1 h8.2
  · exact mem_sub_099 n h9.1 h9.2

theorem mem_iff_block10
    (n : Fin 5011)
    (hlo : 1000 ≤ n.val) (hhi : n.val < 1100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 110 ∨ (1010 ≤ n.val ∧ n.val < 1020) ∨ (1020 ≤ n.val ∧ n.val < 1030) ∨ (1030 ≤ n.val ∧ n.val < 1040) ∨ (1040 ≤ n.val ∧ n.val < 1050) ∨ (1050 ≤ n.val ∧ n.val < 1060) ∨ (1060 ≤ n.val ∧ n.val < 1070) ∨ (1070 ≤ n.val ∧ n.val < 1080) ∨ (1080 ≤ n.val ∧ n.val < 1090) ∨ (1090 ≤ n.val ∧ n.val < 1100) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_100 n hlo h0
  · exact mem_sub_101 n h1.1 h1.2
  · exact mem_sub_102 n h2.1 h2.2
  · exact mem_sub_103 n h3.1 h3.2
  · exact mem_sub_104 n h4.1 h4.2
  · exact mem_sub_105 n h5.1 h5.2
  · exact mem_sub_106 n h6.1 h6.2
  · exact mem_sub_107 n h7.1 h7.2
  · exact mem_sub_108 n h8.1 h8.2
  · exact mem_sub_109 n h9.1 h9.2

theorem mem_iff_block11
    (n : Fin 5011)
    (hlo : 1100 ≤ n.val) (hhi : n.val < 1200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 120 ∨ (1110 ≤ n.val ∧ n.val < 1120) ∨ (1120 ≤ n.val ∧ n.val < 1130) ∨ (1130 ≤ n.val ∧ n.val < 1140) ∨ (1140 ≤ n.val ∧ n.val < 1150) ∨ (1150 ≤ n.val ∧ n.val < 1160) ∨ (1160 ≤ n.val ∧ n.val < 1170) ∨ (1170 ≤ n.val ∧ n.val < 1180) ∨ (1180 ≤ n.val ∧ n.val < 1190) ∨ (1190 ≤ n.val ∧ n.val < 1200) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_110 n hlo h0
  · exact mem_sub_111 n h1.1 h1.2
  · exact mem_sub_112 n h2.1 h2.2
  · exact mem_sub_113 n h3.1 h3.2
  · exact mem_sub_114 n h4.1 h4.2
  · exact mem_sub_115 n h5.1 h5.2
  · exact mem_sub_116 n h6.1 h6.2
  · exact mem_sub_117 n h7.1 h7.2
  · exact mem_sub_118 n h8.1 h8.2
  · exact mem_sub_119 n h9.1 h9.2

theorem mem_iff_block12
    (n : Fin 5011)
    (hlo : 1200 ≤ n.val) (hhi : n.val < 1300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 130 ∨ (1210 ≤ n.val ∧ n.val < 1220) ∨ (1220 ≤ n.val ∧ n.val < 1230) ∨ (1230 ≤ n.val ∧ n.val < 1240) ∨ (1240 ≤ n.val ∧ n.val < 1250) ∨ (1250 ≤ n.val ∧ n.val < 1260) ∨ (1260 ≤ n.val ∧ n.val < 1270) ∨ (1270 ≤ n.val ∧ n.val < 1280) ∨ (1280 ≤ n.val ∧ n.val < 1290) ∨ (1290 ≤ n.val ∧ n.val < 1300) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_120 n hlo h0
  · exact mem_sub_121 n h1.1 h1.2
  · exact mem_sub_122 n h2.1 h2.2
  · exact mem_sub_123 n h3.1 h3.2
  · exact mem_sub_124 n h4.1 h4.2
  · exact mem_sub_125 n h5.1 h5.2
  · exact mem_sub_126 n h6.1 h6.2
  · exact mem_sub_127 n h7.1 h7.2
  · exact mem_sub_128 n h8.1 h8.2
  · exact mem_sub_129 n h9.1 h9.2

theorem mem_iff_block13
    (n : Fin 5011)
    (hlo : 1300 ≤ n.val) (hhi : n.val < 1400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 140 ∨ (1310 ≤ n.val ∧ n.val < 1320) ∨ (1320 ≤ n.val ∧ n.val < 1330) ∨ (1330 ≤ n.val ∧ n.val < 1340) ∨ (1340 ≤ n.val ∧ n.val < 1350) ∨ (1350 ≤ n.val ∧ n.val < 1360) ∨ (1360 ≤ n.val ∧ n.val < 1370) ∨ (1370 ≤ n.val ∧ n.val < 1380) ∨ (1380 ≤ n.val ∧ n.val < 1390) ∨ (1390 ≤ n.val ∧ n.val < 1400) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_130 n hlo h0
  · exact mem_sub_131 n h1.1 h1.2
  · exact mem_sub_132 n h2.1 h2.2
  · exact mem_sub_133 n h3.1 h3.2
  · exact mem_sub_134 n h4.1 h4.2
  · exact mem_sub_135 n h5.1 h5.2
  · exact mem_sub_136 n h6.1 h6.2
  · exact mem_sub_137 n h7.1 h7.2
  · exact mem_sub_138 n h8.1 h8.2
  · exact mem_sub_139 n h9.1 h9.2

theorem mem_iff_block14
    (n : Fin 5011)
    (hlo : 1400 ≤ n.val) (hhi : n.val < 1500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 150 ∨ (1410 ≤ n.val ∧ n.val < 1420) ∨ (1420 ≤ n.val ∧ n.val < 1430) ∨ (1430 ≤ n.val ∧ n.val < 1440) ∨ (1440 ≤ n.val ∧ n.val < 1450) ∨ (1450 ≤ n.val ∧ n.val < 1460) ∨ (1460 ≤ n.val ∧ n.val < 1470) ∨ (1470 ≤ n.val ∧ n.val < 1480) ∨ (1480 ≤ n.val ∧ n.val < 1490) ∨ (1490 ≤ n.val ∧ n.val < 1500) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_140 n hlo h0
  · exact mem_sub_141 n h1.1 h1.2
  · exact mem_sub_142 n h2.1 h2.2
  · exact mem_sub_143 n h3.1 h3.2
  · exact mem_sub_144 n h4.1 h4.2
  · exact mem_sub_145 n h5.1 h5.2
  · exact mem_sub_146 n h6.1 h6.2
  · exact mem_sub_147 n h7.1 h7.2
  · exact mem_sub_148 n h8.1 h8.2
  · exact mem_sub_149 n h9.1 h9.2

theorem mem_iff_block15
    (n : Fin 5011)
    (hlo : 1500 ≤ n.val) (hhi : n.val < 1600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 160 ∨ (1510 ≤ n.val ∧ n.val < 1520) ∨ (1520 ≤ n.val ∧ n.val < 1530) ∨ (1530 ≤ n.val ∧ n.val < 1540) ∨ (1540 ≤ n.val ∧ n.val < 1550) ∨ (1550 ≤ n.val ∧ n.val < 1560) ∨ (1560 ≤ n.val ∧ n.val < 1570) ∨ (1570 ≤ n.val ∧ n.val < 1580) ∨ (1580 ≤ n.val ∧ n.val < 1590) ∨ (1590 ≤ n.val ∧ n.val < 1600) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_150 n hlo h0
  · exact mem_sub_151 n h1.1 h1.2
  · exact mem_sub_152 n h2.1 h2.2
  · exact mem_sub_153 n h3.1 h3.2
  · exact mem_sub_154 n h4.1 h4.2
  · exact mem_sub_155 n h5.1 h5.2
  · exact mem_sub_156 n h6.1 h6.2
  · exact mem_sub_157 n h7.1 h7.2
  · exact mem_sub_158 n h8.1 h8.2
  · exact mem_sub_159 n h9.1 h9.2

theorem mem_iff_block16
    (n : Fin 5011)
    (hlo : 1600 ≤ n.val) (hhi : n.val < 1700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 170 ∨ (1610 ≤ n.val ∧ n.val < 1620) ∨ (1620 ≤ n.val ∧ n.val < 1630) ∨ (1630 ≤ n.val ∧ n.val < 1640) ∨ (1640 ≤ n.val ∧ n.val < 1650) ∨ (1650 ≤ n.val ∧ n.val < 1660) ∨ (1660 ≤ n.val ∧ n.val < 1670) ∨ (1670 ≤ n.val ∧ n.val < 1680) ∨ (1680 ≤ n.val ∧ n.val < 1690) ∨ (1690 ≤ n.val ∧ n.val < 1700) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_160 n hlo h0
  · exact mem_sub_161 n h1.1 h1.2
  · exact mem_sub_162 n h2.1 h2.2
  · exact mem_sub_163 n h3.1 h3.2
  · exact mem_sub_164 n h4.1 h4.2
  · exact mem_sub_165 n h5.1 h5.2
  · exact mem_sub_166 n h6.1 h6.2
  · exact mem_sub_167 n h7.1 h7.2
  · exact mem_sub_168 n h8.1 h8.2
  · exact mem_sub_169 n h9.1 h9.2

theorem mem_iff_block17
    (n : Fin 5011)
    (hlo : 1700 ≤ n.val) (hhi : n.val < 1800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 180 ∨ (1710 ≤ n.val ∧ n.val < 1720) ∨ (1720 ≤ n.val ∧ n.val < 1730) ∨ (1730 ≤ n.val ∧ n.val < 1740) ∨ (1740 ≤ n.val ∧ n.val < 1750) ∨ (1750 ≤ n.val ∧ n.val < 1760) ∨ (1760 ≤ n.val ∧ n.val < 1770) ∨ (1770 ≤ n.val ∧ n.val < 1780) ∨ (1780 ≤ n.val ∧ n.val < 1790) ∨ (1790 ≤ n.val ∧ n.val < 1800) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_170 n hlo h0
  · exact mem_sub_171 n h1.1 h1.2
  · exact mem_sub_172 n h2.1 h2.2
  · exact mem_sub_173 n h3.1 h3.2
  · exact mem_sub_174 n h4.1 h4.2
  · exact mem_sub_175 n h5.1 h5.2
  · exact mem_sub_176 n h6.1 h6.2
  · exact mem_sub_177 n h7.1 h7.2
  · exact mem_sub_178 n h8.1 h8.2
  · exact mem_sub_179 n h9.1 h9.2

theorem mem_iff_block18
    (n : Fin 5011)
    (hlo : 1800 ≤ n.val) (hhi : n.val < 1900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 190 ∨ (1810 ≤ n.val ∧ n.val < 1820) ∨ (1820 ≤ n.val ∧ n.val < 1830) ∨ (1830 ≤ n.val ∧ n.val < 1840) ∨ (1840 ≤ n.val ∧ n.val < 1850) ∨ (1850 ≤ n.val ∧ n.val < 1860) ∨ (1860 ≤ n.val ∧ n.val < 1870) ∨ (1870 ≤ n.val ∧ n.val < 1880) ∨ (1880 ≤ n.val ∧ n.val < 1890) ∨ (1890 ≤ n.val ∧ n.val < 1900) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_180 n hlo h0
  · exact mem_sub_181 n h1.1 h1.2
  · exact mem_sub_182 n h2.1 h2.2
  · exact mem_sub_183 n h3.1 h3.2
  · exact mem_sub_184 n h4.1 h4.2
  · exact mem_sub_185 n h5.1 h5.2
  · exact mem_sub_186 n h6.1 h6.2
  · exact mem_sub_187 n h7.1 h7.2
  · exact mem_sub_188 n h8.1 h8.2
  · exact mem_sub_189 n h9.1 h9.2

theorem mem_iff_block19
    (n : Fin 5011)
    (hlo : 1900 ≤ n.val) (hhi : n.val < 2000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 200 ∨ (1910 ≤ n.val ∧ n.val < 1920) ∨ (1920 ≤ n.val ∧ n.val < 1930) ∨ (1930 ≤ n.val ∧ n.val < 1940) ∨ (1940 ≤ n.val ∧ n.val < 1950) ∨ (1950 ≤ n.val ∧ n.val < 1960) ∨ (1960 ≤ n.val ∧ n.val < 1970) ∨ (1970 ≤ n.val ∧ n.val < 1980) ∨ (1980 ≤ n.val ∧ n.val < 1990) ∨ (1990 ≤ n.val ∧ n.val < 2000) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_190 n hlo h0
  · exact mem_sub_191 n h1.1 h1.2
  · exact mem_sub_192 n h2.1 h2.2
  · exact mem_sub_193 n h3.1 h3.2
  · exact mem_sub_194 n h4.1 h4.2
  · exact mem_sub_195 n h5.1 h5.2
  · exact mem_sub_196 n h6.1 h6.2
  · exact mem_sub_197 n h7.1 h7.2
  · exact mem_sub_198 n h8.1 h8.2
  · exact mem_sub_199 n h9.1 h9.2

theorem mem_iff_block20
    (n : Fin 5011)
    (hlo : 2000 ≤ n.val) (hhi : n.val < 2100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 210 ∨ (2010 ≤ n.val ∧ n.val < 2020) ∨ (2020 ≤ n.val ∧ n.val < 2030) ∨ (2030 ≤ n.val ∧ n.val < 2040) ∨ (2040 ≤ n.val ∧ n.val < 2050) ∨ (2050 ≤ n.val ∧ n.val < 2060) ∨ (2060 ≤ n.val ∧ n.val < 2070) ∨ (2070 ≤ n.val ∧ n.val < 2080) ∨ (2080 ≤ n.val ∧ n.val < 2090) ∨ (2090 ≤ n.val ∧ n.val < 2100) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_200 n hlo h0
  · exact mem_sub_201 n h1.1 h1.2
  · exact mem_sub_202 n h2.1 h2.2
  · exact mem_sub_203 n h3.1 h3.2
  · exact mem_sub_204 n h4.1 h4.2
  · exact mem_sub_205 n h5.1 h5.2
  · exact mem_sub_206 n h6.1 h6.2
  · exact mem_sub_207 n h7.1 h7.2
  · exact mem_sub_208 n h8.1 h8.2
  · exact mem_sub_209 n h9.1 h9.2

theorem mem_iff_block21
    (n : Fin 5011)
    (hlo : 2100 ≤ n.val) (hhi : n.val < 2200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 220 ∨ (2110 ≤ n.val ∧ n.val < 2120) ∨ (2120 ≤ n.val ∧ n.val < 2130) ∨ (2130 ≤ n.val ∧ n.val < 2140) ∨ (2140 ≤ n.val ∧ n.val < 2150) ∨ (2150 ≤ n.val ∧ n.val < 2160) ∨ (2160 ≤ n.val ∧ n.val < 2170) ∨ (2170 ≤ n.val ∧ n.val < 2180) ∨ (2180 ≤ n.val ∧ n.val < 2190) ∨ (2190 ≤ n.val ∧ n.val < 2200) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_210 n hlo h0
  · exact mem_sub_211 n h1.1 h1.2
  · exact mem_sub_212 n h2.1 h2.2
  · exact mem_sub_213 n h3.1 h3.2
  · exact mem_sub_214 n h4.1 h4.2
  · exact mem_sub_215 n h5.1 h5.2
  · exact mem_sub_216 n h6.1 h6.2
  · exact mem_sub_217 n h7.1 h7.2
  · exact mem_sub_218 n h8.1 h8.2
  · exact mem_sub_219 n h9.1 h9.2

theorem mem_iff_block22
    (n : Fin 5011)
    (hlo : 2200 ≤ n.val) (hhi : n.val < 2300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 230 ∨ (2210 ≤ n.val ∧ n.val < 2220) ∨ (2220 ≤ n.val ∧ n.val < 2230) ∨ (2230 ≤ n.val ∧ n.val < 2240) ∨ (2240 ≤ n.val ∧ n.val < 2250) ∨ (2250 ≤ n.val ∧ n.val < 2260) ∨ (2260 ≤ n.val ∧ n.val < 2270) ∨ (2270 ≤ n.val ∧ n.val < 2280) ∨ (2280 ≤ n.val ∧ n.val < 2290) ∨ (2290 ≤ n.val ∧ n.val < 2300) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_220 n hlo h0
  · exact mem_sub_221 n h1.1 h1.2
  · exact mem_sub_222 n h2.1 h2.2
  · exact mem_sub_223 n h3.1 h3.2
  · exact mem_sub_224 n h4.1 h4.2
  · exact mem_sub_225 n h5.1 h5.2
  · exact mem_sub_226 n h6.1 h6.2
  · exact mem_sub_227 n h7.1 h7.2
  · exact mem_sub_228 n h8.1 h8.2
  · exact mem_sub_229 n h9.1 h9.2

theorem mem_iff_block23
    (n : Fin 5011)
    (hlo : 2300 ≤ n.val) (hhi : n.val < 2400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 240 ∨ (2310 ≤ n.val ∧ n.val < 2320) ∨ (2320 ≤ n.val ∧ n.val < 2330) ∨ (2330 ≤ n.val ∧ n.val < 2340) ∨ (2340 ≤ n.val ∧ n.val < 2350) ∨ (2350 ≤ n.val ∧ n.val < 2360) ∨ (2360 ≤ n.val ∧ n.val < 2370) ∨ (2370 ≤ n.val ∧ n.val < 2380) ∨ (2380 ≤ n.val ∧ n.val < 2390) ∨ (2390 ≤ n.val ∧ n.val < 2400) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_230 n hlo h0
  · exact mem_sub_231 n h1.1 h1.2
  · exact mem_sub_232 n h2.1 h2.2
  · exact mem_sub_233 n h3.1 h3.2
  · exact mem_sub_234 n h4.1 h4.2
  · exact mem_sub_235 n h5.1 h5.2
  · exact mem_sub_236 n h6.1 h6.2
  · exact mem_sub_237 n h7.1 h7.2
  · exact mem_sub_238 n h8.1 h8.2
  · exact mem_sub_239 n h9.1 h9.2

theorem mem_iff_block24
    (n : Fin 5011)
    (hlo : 2400 ≤ n.val) (hhi : n.val < 2500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 250 ∨ (2410 ≤ n.val ∧ n.val < 2420) ∨ (2420 ≤ n.val ∧ n.val < 2430) ∨ (2430 ≤ n.val ∧ n.val < 2440) ∨ (2440 ≤ n.val ∧ n.val < 2450) ∨ (2450 ≤ n.val ∧ n.val < 2460) ∨ (2460 ≤ n.val ∧ n.val < 2470) ∨ (2470 ≤ n.val ∧ n.val < 2480) ∨ (2480 ≤ n.val ∧ n.val < 2490) ∨ (2490 ≤ n.val ∧ n.val < 2500) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_240 n hlo h0
  · exact mem_sub_241 n h1.1 h1.2
  · exact mem_sub_242 n h2.1 h2.2
  · exact mem_sub_243 n h3.1 h3.2
  · exact mem_sub_244 n h4.1 h4.2
  · exact mem_sub_245 n h5.1 h5.2
  · exact mem_sub_246 n h6.1 h6.2
  · exact mem_sub_247 n h7.1 h7.2
  · exact mem_sub_248 n h8.1 h8.2
  · exact mem_sub_249 n h9.1 h9.2

theorem mem_iff_block25
    (n : Fin 5011)
    (hlo : 2500 ≤ n.val) (hhi : n.val < 2600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 260 ∨ (2510 ≤ n.val ∧ n.val < 2520) ∨ (2520 ≤ n.val ∧ n.val < 2530) ∨ (2530 ≤ n.val ∧ n.val < 2540) ∨ (2540 ≤ n.val ∧ n.val < 2550) ∨ (2550 ≤ n.val ∧ n.val < 2560) ∨ (2560 ≤ n.val ∧ n.val < 2570) ∨ (2570 ≤ n.val ∧ n.val < 2580) ∨ (2580 ≤ n.val ∧ n.val < 2590) ∨ (2590 ≤ n.val ∧ n.val < 2600) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_250 n hlo h0
  · exact mem_sub_251 n h1.1 h1.2
  · exact mem_sub_252 n h2.1 h2.2
  · exact mem_sub_253 n h3.1 h3.2
  · exact mem_sub_254 n h4.1 h4.2
  · exact mem_sub_255 n h5.1 h5.2
  · exact mem_sub_256 n h6.1 h6.2
  · exact mem_sub_257 n h7.1 h7.2
  · exact mem_sub_258 n h8.1 h8.2
  · exact mem_sub_259 n h9.1 h9.2

theorem mem_iff_block26
    (n : Fin 5011)
    (hlo : 2600 ≤ n.val) (hhi : n.val < 2700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 270 ∨ (2610 ≤ n.val ∧ n.val < 2620) ∨ (2620 ≤ n.val ∧ n.val < 2630) ∨ (2630 ≤ n.val ∧ n.val < 2640) ∨ (2640 ≤ n.val ∧ n.val < 2650) ∨ (2650 ≤ n.val ∧ n.val < 2660) ∨ (2660 ≤ n.val ∧ n.val < 2670) ∨ (2670 ≤ n.val ∧ n.val < 2680) ∨ (2680 ≤ n.val ∧ n.val < 2690) ∨ (2690 ≤ n.val ∧ n.val < 2700) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_260 n hlo h0
  · exact mem_sub_261 n h1.1 h1.2
  · exact mem_sub_262 n h2.1 h2.2
  · exact mem_sub_263 n h3.1 h3.2
  · exact mem_sub_264 n h4.1 h4.2
  · exact mem_sub_265 n h5.1 h5.2
  · exact mem_sub_266 n h6.1 h6.2
  · exact mem_sub_267 n h7.1 h7.2
  · exact mem_sub_268 n h8.1 h8.2
  · exact mem_sub_269 n h9.1 h9.2

theorem mem_iff_block27
    (n : Fin 5011)
    (hlo : 2700 ≤ n.val) (hhi : n.val < 2800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 280 ∨ (2710 ≤ n.val ∧ n.val < 2720) ∨ (2720 ≤ n.val ∧ n.val < 2730) ∨ (2730 ≤ n.val ∧ n.val < 2740) ∨ (2740 ≤ n.val ∧ n.val < 2750) ∨ (2750 ≤ n.val ∧ n.val < 2760) ∨ (2760 ≤ n.val ∧ n.val < 2770) ∨ (2770 ≤ n.val ∧ n.val < 2780) ∨ (2780 ≤ n.val ∧ n.val < 2790) ∨ (2790 ≤ n.val ∧ n.val < 2800) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_270 n hlo h0
  · exact mem_sub_271 n h1.1 h1.2
  · exact mem_sub_272 n h2.1 h2.2
  · exact mem_sub_273 n h3.1 h3.2
  · exact mem_sub_274 n h4.1 h4.2
  · exact mem_sub_275 n h5.1 h5.2
  · exact mem_sub_276 n h6.1 h6.2
  · exact mem_sub_277 n h7.1 h7.2
  · exact mem_sub_278 n h8.1 h8.2
  · exact mem_sub_279 n h9.1 h9.2

theorem mem_iff_block28
    (n : Fin 5011)
    (hlo : 2800 ≤ n.val) (hhi : n.val < 2900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 290 ∨ (2810 ≤ n.val ∧ n.val < 2820) ∨ (2820 ≤ n.val ∧ n.val < 2830) ∨ (2830 ≤ n.val ∧ n.val < 2840) ∨ (2840 ≤ n.val ∧ n.val < 2850) ∨ (2850 ≤ n.val ∧ n.val < 2860) ∨ (2860 ≤ n.val ∧ n.val < 2870) ∨ (2870 ≤ n.val ∧ n.val < 2880) ∨ (2880 ≤ n.val ∧ n.val < 2890) ∨ (2890 ≤ n.val ∧ n.val < 2900) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_280 n hlo h0
  · exact mem_sub_281 n h1.1 h1.2
  · exact mem_sub_282 n h2.1 h2.2
  · exact mem_sub_283 n h3.1 h3.2
  · exact mem_sub_284 n h4.1 h4.2
  · exact mem_sub_285 n h5.1 h5.2
  · exact mem_sub_286 n h6.1 h6.2
  · exact mem_sub_287 n h7.1 h7.2
  · exact mem_sub_288 n h8.1 h8.2
  · exact mem_sub_289 n h9.1 h9.2

theorem mem_iff_block29
    (n : Fin 5011)
    (hlo : 2900 ≤ n.val) (hhi : n.val < 3000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 300 ∨ (2910 ≤ n.val ∧ n.val < 2920) ∨ (2920 ≤ n.val ∧ n.val < 2930) ∨ (2930 ≤ n.val ∧ n.val < 2940) ∨ (2940 ≤ n.val ∧ n.val < 2950) ∨ (2950 ≤ n.val ∧ n.val < 2960) ∨ (2960 ≤ n.val ∧ n.val < 2970) ∨ (2970 ≤ n.val ∧ n.val < 2980) ∨ (2980 ≤ n.val ∧ n.val < 2990) ∨ (2990 ≤ n.val ∧ n.val < 3000) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_290 n hlo h0
  · exact mem_sub_291 n h1.1 h1.2
  · exact mem_sub_292 n h2.1 h2.2
  · exact mem_sub_293 n h3.1 h3.2
  · exact mem_sub_294 n h4.1 h4.2
  · exact mem_sub_295 n h5.1 h5.2
  · exact mem_sub_296 n h6.1 h6.2
  · exact mem_sub_297 n h7.1 h7.2
  · exact mem_sub_298 n h8.1 h8.2
  · exact mem_sub_299 n h9.1 h9.2

theorem mem_iff_block30
    (n : Fin 5011)
    (hlo : 3000 ≤ n.val) (hhi : n.val < 3100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 310 ∨ (3010 ≤ n.val ∧ n.val < 3020) ∨ (3020 ≤ n.val ∧ n.val < 3030) ∨ (3030 ≤ n.val ∧ n.val < 3040) ∨ (3040 ≤ n.val ∧ n.val < 3050) ∨ (3050 ≤ n.val ∧ n.val < 3060) ∨ (3060 ≤ n.val ∧ n.val < 3070) ∨ (3070 ≤ n.val ∧ n.val < 3080) ∨ (3080 ≤ n.val ∧ n.val < 3090) ∨ (3090 ≤ n.val ∧ n.val < 3100) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_300 n hlo h0
  · exact mem_sub_301 n h1.1 h1.2
  · exact mem_sub_302 n h2.1 h2.2
  · exact mem_sub_303 n h3.1 h3.2
  · exact mem_sub_304 n h4.1 h4.2
  · exact mem_sub_305 n h5.1 h5.2
  · exact mem_sub_306 n h6.1 h6.2
  · exact mem_sub_307 n h7.1 h7.2
  · exact mem_sub_308 n h8.1 h8.2
  · exact mem_sub_309 n h9.1 h9.2

theorem mem_iff_block31
    (n : Fin 5011)
    (hlo : 3100 ≤ n.val) (hhi : n.val < 3200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 320 ∨ (3110 ≤ n.val ∧ n.val < 3120) ∨ (3120 ≤ n.val ∧ n.val < 3130) ∨ (3130 ≤ n.val ∧ n.val < 3140) ∨ (3140 ≤ n.val ∧ n.val < 3150) ∨ (3150 ≤ n.val ∧ n.val < 3160) ∨ (3160 ≤ n.val ∧ n.val < 3170) ∨ (3170 ≤ n.val ∧ n.val < 3180) ∨ (3180 ≤ n.val ∧ n.val < 3190) ∨ (3190 ≤ n.val ∧ n.val < 3200) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_310 n hlo h0
  · exact mem_sub_311 n h1.1 h1.2
  · exact mem_sub_312 n h2.1 h2.2
  · exact mem_sub_313 n h3.1 h3.2
  · exact mem_sub_314 n h4.1 h4.2
  · exact mem_sub_315 n h5.1 h5.2
  · exact mem_sub_316 n h6.1 h6.2
  · exact mem_sub_317 n h7.1 h7.2
  · exact mem_sub_318 n h8.1 h8.2
  · exact mem_sub_319 n h9.1 h9.2

theorem mem_iff_block32
    (n : Fin 5011)
    (hlo : 3200 ≤ n.val) (hhi : n.val < 3300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 330 ∨ (3210 ≤ n.val ∧ n.val < 3220) ∨ (3220 ≤ n.val ∧ n.val < 3230) ∨ (3230 ≤ n.val ∧ n.val < 3240) ∨ (3240 ≤ n.val ∧ n.val < 3250) ∨ (3250 ≤ n.val ∧ n.val < 3260) ∨ (3260 ≤ n.val ∧ n.val < 3270) ∨ (3270 ≤ n.val ∧ n.val < 3280) ∨ (3280 ≤ n.val ∧ n.val < 3290) ∨ (3290 ≤ n.val ∧ n.val < 3300) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_320 n hlo h0
  · exact mem_sub_321 n h1.1 h1.2
  · exact mem_sub_322 n h2.1 h2.2
  · exact mem_sub_323 n h3.1 h3.2
  · exact mem_sub_324 n h4.1 h4.2
  · exact mem_sub_325 n h5.1 h5.2
  · exact mem_sub_326 n h6.1 h6.2
  · exact mem_sub_327 n h7.1 h7.2
  · exact mem_sub_328 n h8.1 h8.2
  · exact mem_sub_329 n h9.1 h9.2

theorem mem_iff_block33
    (n : Fin 5011)
    (hlo : 3300 ≤ n.val) (hhi : n.val < 3400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 340 ∨ (3310 ≤ n.val ∧ n.val < 3320) ∨ (3320 ≤ n.val ∧ n.val < 3330) ∨ (3330 ≤ n.val ∧ n.val < 3340) ∨ (3340 ≤ n.val ∧ n.val < 3350) ∨ (3350 ≤ n.val ∧ n.val < 3360) ∨ (3360 ≤ n.val ∧ n.val < 3370) ∨ (3370 ≤ n.val ∧ n.val < 3380) ∨ (3380 ≤ n.val ∧ n.val < 3390) ∨ (3390 ≤ n.val ∧ n.val < 3400) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_330 n hlo h0
  · exact mem_sub_331 n h1.1 h1.2
  · exact mem_sub_332 n h2.1 h2.2
  · exact mem_sub_333 n h3.1 h3.2
  · exact mem_sub_334 n h4.1 h4.2
  · exact mem_sub_335 n h5.1 h5.2
  · exact mem_sub_336 n h6.1 h6.2
  · exact mem_sub_337 n h7.1 h7.2
  · exact mem_sub_338 n h8.1 h8.2
  · exact mem_sub_339 n h9.1 h9.2

theorem mem_iff_block34
    (n : Fin 5011)
    (hlo : 3400 ≤ n.val) (hhi : n.val < 3500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 350 ∨ (3410 ≤ n.val ∧ n.val < 3420) ∨ (3420 ≤ n.val ∧ n.val < 3430) ∨ (3430 ≤ n.val ∧ n.val < 3440) ∨ (3440 ≤ n.val ∧ n.val < 3450) ∨ (3450 ≤ n.val ∧ n.val < 3460) ∨ (3460 ≤ n.val ∧ n.val < 3470) ∨ (3470 ≤ n.val ∧ n.val < 3480) ∨ (3480 ≤ n.val ∧ n.val < 3490) ∨ (3490 ≤ n.val ∧ n.val < 3500) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_340 n hlo h0
  · exact mem_sub_341 n h1.1 h1.2
  · exact mem_sub_342 n h2.1 h2.2
  · exact mem_sub_343 n h3.1 h3.2
  · exact mem_sub_344 n h4.1 h4.2
  · exact mem_sub_345 n h5.1 h5.2
  · exact mem_sub_346 n h6.1 h6.2
  · exact mem_sub_347 n h7.1 h7.2
  · exact mem_sub_348 n h8.1 h8.2
  · exact mem_sub_349 n h9.1 h9.2

theorem mem_iff_block35
    (n : Fin 5011)
    (hlo : 3500 ≤ n.val) (hhi : n.val < 3600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 360 ∨ (3510 ≤ n.val ∧ n.val < 3520) ∨ (3520 ≤ n.val ∧ n.val < 3530) ∨ (3530 ≤ n.val ∧ n.val < 3540) ∨ (3540 ≤ n.val ∧ n.val < 3550) ∨ (3550 ≤ n.val ∧ n.val < 3560) ∨ (3560 ≤ n.val ∧ n.val < 3570) ∨ (3570 ≤ n.val ∧ n.val < 3580) ∨ (3580 ≤ n.val ∧ n.val < 3590) ∨ (3590 ≤ n.val ∧ n.val < 3600) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_350 n hlo h0
  · exact mem_sub_351 n h1.1 h1.2
  · exact mem_sub_352 n h2.1 h2.2
  · exact mem_sub_353 n h3.1 h3.2
  · exact mem_sub_354 n h4.1 h4.2
  · exact mem_sub_355 n h5.1 h5.2
  · exact mem_sub_356 n h6.1 h6.2
  · exact mem_sub_357 n h7.1 h7.2
  · exact mem_sub_358 n h8.1 h8.2
  · exact mem_sub_359 n h9.1 h9.2

theorem mem_iff_block36
    (n : Fin 5011)
    (hlo : 3600 ≤ n.val) (hhi : n.val < 3700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 370 ∨ (3610 ≤ n.val ∧ n.val < 3620) ∨ (3620 ≤ n.val ∧ n.val < 3630) ∨ (3630 ≤ n.val ∧ n.val < 3640) ∨ (3640 ≤ n.val ∧ n.val < 3650) ∨ (3650 ≤ n.val ∧ n.val < 3660) ∨ (3660 ≤ n.val ∧ n.val < 3670) ∨ (3670 ≤ n.val ∧ n.val < 3680) ∨ (3680 ≤ n.val ∧ n.val < 3690) ∨ (3690 ≤ n.val ∧ n.val < 3700) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_360 n hlo h0
  · exact mem_sub_361 n h1.1 h1.2
  · exact mem_sub_362 n h2.1 h2.2
  · exact mem_sub_363 n h3.1 h3.2
  · exact mem_sub_364 n h4.1 h4.2
  · exact mem_sub_365 n h5.1 h5.2
  · exact mem_sub_366 n h6.1 h6.2
  · exact mem_sub_367 n h7.1 h7.2
  · exact mem_sub_368 n h8.1 h8.2
  · exact mem_sub_369 n h9.1 h9.2

theorem mem_iff_block37
    (n : Fin 5011)
    (hlo : 3700 ≤ n.val) (hhi : n.val < 3800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 380 ∨ (3710 ≤ n.val ∧ n.val < 3720) ∨ (3720 ≤ n.val ∧ n.val < 3730) ∨ (3730 ≤ n.val ∧ n.val < 3740) ∨ (3740 ≤ n.val ∧ n.val < 3750) ∨ (3750 ≤ n.val ∧ n.val < 3760) ∨ (3760 ≤ n.val ∧ n.val < 3770) ∨ (3770 ≤ n.val ∧ n.val < 3780) ∨ (3780 ≤ n.val ∧ n.val < 3790) ∨ (3790 ≤ n.val ∧ n.val < 3800) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_370 n hlo h0
  · exact mem_sub_371 n h1.1 h1.2
  · exact mem_sub_372 n h2.1 h2.2
  · exact mem_sub_373 n h3.1 h3.2
  · exact mem_sub_374 n h4.1 h4.2
  · exact mem_sub_375 n h5.1 h5.2
  · exact mem_sub_376 n h6.1 h6.2
  · exact mem_sub_377 n h7.1 h7.2
  · exact mem_sub_378 n h8.1 h8.2
  · exact mem_sub_379 n h9.1 h9.2

theorem mem_iff_block38
    (n : Fin 5011)
    (hlo : 3800 ≤ n.val) (hhi : n.val < 3900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 390 ∨ (3810 ≤ n.val ∧ n.val < 3820) ∨ (3820 ≤ n.val ∧ n.val < 3830) ∨ (3830 ≤ n.val ∧ n.val < 3840) ∨ (3840 ≤ n.val ∧ n.val < 3850) ∨ (3850 ≤ n.val ∧ n.val < 3860) ∨ (3860 ≤ n.val ∧ n.val < 3870) ∨ (3870 ≤ n.val ∧ n.val < 3880) ∨ (3880 ≤ n.val ∧ n.val < 3890) ∨ (3890 ≤ n.val ∧ n.val < 3900) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_380 n hlo h0
  · exact mem_sub_381 n h1.1 h1.2
  · exact mem_sub_382 n h2.1 h2.2
  · exact mem_sub_383 n h3.1 h3.2
  · exact mem_sub_384 n h4.1 h4.2
  · exact mem_sub_385 n h5.1 h5.2
  · exact mem_sub_386 n h6.1 h6.2
  · exact mem_sub_387 n h7.1 h7.2
  · exact mem_sub_388 n h8.1 h8.2
  · exact mem_sub_389 n h9.1 h9.2

theorem mem_iff_block39
    (n : Fin 5011)
    (hlo : 3900 ≤ n.val) (hhi : n.val < 4000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 400 ∨ (3910 ≤ n.val ∧ n.val < 3920) ∨ (3920 ≤ n.val ∧ n.val < 3930) ∨ (3930 ≤ n.val ∧ n.val < 3940) ∨ (3940 ≤ n.val ∧ n.val < 3950) ∨ (3950 ≤ n.val ∧ n.val < 3960) ∨ (3960 ≤ n.val ∧ n.val < 3970) ∨ (3970 ≤ n.val ∧ n.val < 3980) ∨ (3980 ≤ n.val ∧ n.val < 3990) ∨ (3990 ≤ n.val ∧ n.val < 4000) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_390 n hlo h0
  · exact mem_sub_391 n h1.1 h1.2
  · exact mem_sub_392 n h2.1 h2.2
  · exact mem_sub_393 n h3.1 h3.2
  · exact mem_sub_394 n h4.1 h4.2
  · exact mem_sub_395 n h5.1 h5.2
  · exact mem_sub_396 n h6.1 h6.2
  · exact mem_sub_397 n h7.1 h7.2
  · exact mem_sub_398 n h8.1 h8.2
  · exact mem_sub_399 n h9.1 h9.2

theorem mem_iff_block40
    (n : Fin 5011)
    (hlo : 4000 ≤ n.val) (hhi : n.val < 4100) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 410 ∨ (4010 ≤ n.val ∧ n.val < 4020) ∨ (4020 ≤ n.val ∧ n.val < 4030) ∨ (4030 ≤ n.val ∧ n.val < 4040) ∨ (4040 ≤ n.val ∧ n.val < 4050) ∨ (4050 ≤ n.val ∧ n.val < 4060) ∨ (4060 ≤ n.val ∧ n.val < 4070) ∨ (4070 ≤ n.val ∧ n.val < 4080) ∨ (4080 ≤ n.val ∧ n.val < 4090) ∨ (4090 ≤ n.val ∧ n.val < 4100) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_400 n hlo h0
  · exact mem_sub_401 n h1.1 h1.2
  · exact mem_sub_402 n h2.1 h2.2
  · exact mem_sub_403 n h3.1 h3.2
  · exact mem_sub_404 n h4.1 h4.2
  · exact mem_sub_405 n h5.1 h5.2
  · exact mem_sub_406 n h6.1 h6.2
  · exact mem_sub_407 n h7.1 h7.2
  · exact mem_sub_408 n h8.1 h8.2
  · exact mem_sub_409 n h9.1 h9.2

theorem mem_iff_block41
    (n : Fin 5011)
    (hlo : 4100 ≤ n.val) (hhi : n.val < 4200) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 420 ∨ (4110 ≤ n.val ∧ n.val < 4120) ∨ (4120 ≤ n.val ∧ n.val < 4130) ∨ (4130 ≤ n.val ∧ n.val < 4140) ∨ (4140 ≤ n.val ∧ n.val < 4150) ∨ (4150 ≤ n.val ∧ n.val < 4160) ∨ (4160 ≤ n.val ∧ n.val < 4170) ∨ (4170 ≤ n.val ∧ n.val < 4180) ∨ (4180 ≤ n.val ∧ n.val < 4190) ∨ (4190 ≤ n.val ∧ n.val < 4200) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_410 n hlo h0
  · exact mem_sub_411 n h1.1 h1.2
  · exact mem_sub_412 n h2.1 h2.2
  · exact mem_sub_413 n h3.1 h3.2
  · exact mem_sub_414 n h4.1 h4.2
  · exact mem_sub_415 n h5.1 h5.2
  · exact mem_sub_416 n h6.1 h6.2
  · exact mem_sub_417 n h7.1 h7.2
  · exact mem_sub_418 n h8.1 h8.2
  · exact mem_sub_419 n h9.1 h9.2

theorem mem_iff_block42
    (n : Fin 5011)
    (hlo : 4200 ≤ n.val) (hhi : n.val < 4300) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 430 ∨ (4210 ≤ n.val ∧ n.val < 4220) ∨ (4220 ≤ n.val ∧ n.val < 4230) ∨ (4230 ≤ n.val ∧ n.val < 4240) ∨ (4240 ≤ n.val ∧ n.val < 4250) ∨ (4250 ≤ n.val ∧ n.val < 4260) ∨ (4260 ≤ n.val ∧ n.val < 4270) ∨ (4270 ≤ n.val ∧ n.val < 4280) ∨ (4280 ≤ n.val ∧ n.val < 4290) ∨ (4290 ≤ n.val ∧ n.val < 4300) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_420 n hlo h0
  · exact mem_sub_421 n h1.1 h1.2
  · exact mem_sub_422 n h2.1 h2.2
  · exact mem_sub_423 n h3.1 h3.2
  · exact mem_sub_424 n h4.1 h4.2
  · exact mem_sub_425 n h5.1 h5.2
  · exact mem_sub_426 n h6.1 h6.2
  · exact mem_sub_427 n h7.1 h7.2
  · exact mem_sub_428 n h8.1 h8.2
  · exact mem_sub_429 n h9.1 h9.2

theorem mem_iff_block43
    (n : Fin 5011)
    (hlo : 4300 ≤ n.val) (hhi : n.val < 4400) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 440 ∨ (4310 ≤ n.val ∧ n.val < 4320) ∨ (4320 ≤ n.val ∧ n.val < 4330) ∨ (4330 ≤ n.val ∧ n.val < 4340) ∨ (4340 ≤ n.val ∧ n.val < 4350) ∨ (4350 ≤ n.val ∧ n.val < 4360) ∨ (4360 ≤ n.val ∧ n.val < 4370) ∨ (4370 ≤ n.val ∧ n.val < 4380) ∨ (4380 ≤ n.val ∧ n.val < 4390) ∨ (4390 ≤ n.val ∧ n.val < 4400) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_430 n hlo h0
  · exact mem_sub_431 n h1.1 h1.2
  · exact mem_sub_432 n h2.1 h2.2
  · exact mem_sub_433 n h3.1 h3.2
  · exact mem_sub_434 n h4.1 h4.2
  · exact mem_sub_435 n h5.1 h5.2
  · exact mem_sub_436 n h6.1 h6.2
  · exact mem_sub_437 n h7.1 h7.2
  · exact mem_sub_438 n h8.1 h8.2
  · exact mem_sub_439 n h9.1 h9.2

theorem mem_iff_block44
    (n : Fin 5011)
    (hlo : 4400 ≤ n.val) (hhi : n.val < 4500) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 450 ∨ (4410 ≤ n.val ∧ n.val < 4420) ∨ (4420 ≤ n.val ∧ n.val < 4430) ∨ (4430 ≤ n.val ∧ n.val < 4440) ∨ (4440 ≤ n.val ∧ n.val < 4450) ∨ (4450 ≤ n.val ∧ n.val < 4460) ∨ (4460 ≤ n.val ∧ n.val < 4470) ∨ (4470 ≤ n.val ∧ n.val < 4480) ∨ (4480 ≤ n.val ∧ n.val < 4490) ∨ (4490 ≤ n.val ∧ n.val < 4500) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_440 n hlo h0
  · exact mem_sub_441 n h1.1 h1.2
  · exact mem_sub_442 n h2.1 h2.2
  · exact mem_sub_443 n h3.1 h3.2
  · exact mem_sub_444 n h4.1 h4.2
  · exact mem_sub_445 n h5.1 h5.2
  · exact mem_sub_446 n h6.1 h6.2
  · exact mem_sub_447 n h7.1 h7.2
  · exact mem_sub_448 n h8.1 h8.2
  · exact mem_sub_449 n h9.1 h9.2

theorem mem_iff_block45
    (n : Fin 5011)
    (hlo : 4500 ≤ n.val) (hhi : n.val < 4600) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 460 ∨ (4510 ≤ n.val ∧ n.val < 4520) ∨ (4520 ≤ n.val ∧ n.val < 4530) ∨ (4530 ≤ n.val ∧ n.val < 4540) ∨ (4540 ≤ n.val ∧ n.val < 4550) ∨ (4550 ≤ n.val ∧ n.val < 4560) ∨ (4560 ≤ n.val ∧ n.val < 4570) ∨ (4570 ≤ n.val ∧ n.val < 4580) ∨ (4580 ≤ n.val ∧ n.val < 4590) ∨ (4590 ≤ n.val ∧ n.val < 4600) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_450 n hlo h0
  · exact mem_sub_451 n h1.1 h1.2
  · exact mem_sub_452 n h2.1 h2.2
  · exact mem_sub_453 n h3.1 h3.2
  · exact mem_sub_454 n h4.1 h4.2
  · exact mem_sub_455 n h5.1 h5.2
  · exact mem_sub_456 n h6.1 h6.2
  · exact mem_sub_457 n h7.1 h7.2
  · exact mem_sub_458 n h8.1 h8.2
  · exact mem_sub_459 n h9.1 h9.2

theorem mem_iff_block46
    (n : Fin 5011)
    (hlo : 4600 ≤ n.val) (hhi : n.val < 4700) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 470 ∨ (4610 ≤ n.val ∧ n.val < 4620) ∨ (4620 ≤ n.val ∧ n.val < 4630) ∨ (4630 ≤ n.val ∧ n.val < 4640) ∨ (4640 ≤ n.val ∧ n.val < 4650) ∨ (4650 ≤ n.val ∧ n.val < 4660) ∨ (4660 ≤ n.val ∧ n.val < 4670) ∨ (4670 ≤ n.val ∧ n.val < 4680) ∨ (4680 ≤ n.val ∧ n.val < 4690) ∨ (4690 ≤ n.val ∧ n.val < 4700) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_460 n hlo h0
  · exact mem_sub_461 n h1.1 h1.2
  · exact mem_sub_462 n h2.1 h2.2
  · exact mem_sub_463 n h3.1 h3.2
  · exact mem_sub_464 n h4.1 h4.2
  · exact mem_sub_465 n h5.1 h5.2
  · exact mem_sub_466 n h6.1 h6.2
  · exact mem_sub_467 n h7.1 h7.2
  · exact mem_sub_468 n h8.1 h8.2
  · exact mem_sub_469 n h9.1 h9.2

theorem mem_iff_block47
    (n : Fin 5011)
    (hlo : 4700 ≤ n.val) (hhi : n.val < 4800) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 480 ∨ (4710 ≤ n.val ∧ n.val < 4720) ∨ (4720 ≤ n.val ∧ n.val < 4730) ∨ (4730 ≤ n.val ∧ n.val < 4740) ∨ (4740 ≤ n.val ∧ n.val < 4750) ∨ (4750 ≤ n.val ∧ n.val < 4760) ∨ (4760 ≤ n.val ∧ n.val < 4770) ∨ (4770 ≤ n.val ∧ n.val < 4780) ∨ (4780 ≤ n.val ∧ n.val < 4790) ∨ (4790 ≤ n.val ∧ n.val < 4800) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_470 n hlo h0
  · exact mem_sub_471 n h1.1 h1.2
  · exact mem_sub_472 n h2.1 h2.2
  · exact mem_sub_473 n h3.1 h3.2
  · exact mem_sub_474 n h4.1 h4.2
  · exact mem_sub_475 n h5.1 h5.2
  · exact mem_sub_476 n h6.1 h6.2
  · exact mem_sub_477 n h7.1 h7.2
  · exact mem_sub_478 n h8.1 h8.2
  · exact mem_sub_479 n h9.1 h9.2

theorem mem_iff_block48
    (n : Fin 5011)
    (hlo : 4800 ≤ n.val) (hhi : n.val < 4900) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 490 ∨ (4810 ≤ n.val ∧ n.val < 4820) ∨ (4820 ≤ n.val ∧ n.val < 4830) ∨ (4830 ≤ n.val ∧ n.val < 4840) ∨ (4840 ≤ n.val ∧ n.val < 4850) ∨ (4850 ≤ n.val ∧ n.val < 4860) ∨ (4860 ≤ n.val ∧ n.val < 4870) ∨ (4870 ≤ n.val ∧ n.val < 4880) ∨ (4880 ≤ n.val ∧ n.val < 4890) ∨ (4890 ≤ n.val ∧ n.val < 4900) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_480 n hlo h0
  · exact mem_sub_481 n h1.1 h1.2
  · exact mem_sub_482 n h2.1 h2.2
  · exact mem_sub_483 n h3.1 h3.2
  · exact mem_sub_484 n h4.1 h4.2
  · exact mem_sub_485 n h5.1 h5.2
  · exact mem_sub_486 n h6.1 h6.2
  · exact mem_sub_487 n h7.1 h7.2
  · exact mem_sub_488 n h8.1 h8.2
  · exact mem_sub_489 n h9.1 h9.2

theorem mem_iff_block49
    (n : Fin 5011)
    (hlo : 4900 ≤ n.val) (hhi : n.val < 5000) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 500 ∨ (4910 ≤ n.val ∧ n.val < 4920) ∨ (4920 ≤ n.val ∧ n.val < 4930) ∨ (4930 ≤ n.val ∧ n.val < 4940) ∨ (4940 ≤ n.val ∧ n.val < 4950) ∨ (4950 ≤ n.val ∧ n.val < 4960) ∨ (4960 ≤ n.val ∧ n.val < 4970) ∨ (4970 ≤ n.val ∧ n.val < 4980) ∨ (4980 ≤ n.val ∧ n.val < 4990) ∨ (4990 ≤ n.val ∧ n.val < 5000) := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact mem_sub_490 n hlo h0
  · exact mem_sub_491 n h1.1 h1.2
  · exact mem_sub_492 n h2.1 h2.2
  · exact mem_sub_493 n h3.1 h3.2
  · exact mem_sub_494 n h4.1 h4.2
  · exact mem_sub_495 n h5.1 h5.2
  · exact mem_sub_496 n h6.1 h6.2
  · exact mem_sub_497 n h7.1 h7.2
  · exact mem_sub_498 n h8.1 h8.2
  · exact mem_sub_499 n h9.1 h9.2

theorem mem_iff_block50 (n : Fin 5011) (hlo : 5000 ≤ n.val) :
    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      n ∈ residual373 := by
  have hcases : n.val < 5010 ∨ n.val = 5010 := by omega
  rcases hcases with h0 | h1
  · exact mem_sub_500 n hlo h0
  · exact mem_sub_501 n (by omega) n.isLt

theorem residualIDs_eq_residual373 :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs = residual373 := by
  ext n
  rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff,
    EnergyTerminalResidualCensusRefineSixteen.mem_refinedResidualIDs_iff,
    repair_paidIDs_eq_refineSixteen_paidIDs]
  rfl

theorem residual373_card : residual373.card = 373 :=
  EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs_card

theorem residualIDs_card :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs.card = 373 := by
  rw [residualIDs_eq_residual373, residual373_card]

theorem remaining_of_residual373_radius_certificates
    (h : ∀ n, n ∈ residual373 →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13RefineSixteenRepair.RemainingTerminalRadius :=
  EnergyTerminalBatchB13RefineSixteenResidual.remaining_of_residual_radius_certificates
    (fun n hn => h n ((residualIDs_eq_residual373).mp hn))

theorem b13_remaining_of_residual373_radius_certificates
    (h : ∀ n, n ∈ residual373 →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  EnergyTerminalBatchB13RefineSixteenResidual.b13_remaining_of_residual_radius_certificates
    (fun n hn => h n ((residualIDs_eq_residual373).mp hn))
end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.residualIDs_card
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.b13_remaining_of_residual373_radius_certificates
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.residualIDs_card
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.b13_remaining_of_residual373_radius_certificates
