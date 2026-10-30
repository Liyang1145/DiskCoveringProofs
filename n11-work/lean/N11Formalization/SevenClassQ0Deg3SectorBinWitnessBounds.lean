import N11Formalization.SevenClassQ0Deg3SectorBinWitness

/-! Lane A: all 72 emitted sector-bin witnesses lie in their assigned bins. -/
set_option autoImplicit false
namespace N11Formalization.SevenClassQ0Deg3SectorBinWitnessBounds

open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness

theorem sectorBinWitness_mem_bin (i : Fin 9) (j : Fin 8) :
    binFirst j ≤ (sectorBinWitness i j).val ∧
      (sectorBinWitness i j).val ≤ binLast j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [sectorBinWitness, binFirst, binLast, binHi]

end N11Formalization.SevenClassQ0Deg3SectorBinWitnessBounds
#check @N11Formalization.SevenClassQ0Deg3SectorBinWitnessBounds.sectorBinWitness_mem_bin
#print axioms N11Formalization.SevenClassQ0Deg3SectorBinWitnessBounds.sectorBinWitness_mem_bin
