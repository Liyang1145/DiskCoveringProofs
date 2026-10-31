import N11Formalization.SevenClassQ0Deg3SectorBins67AllRows
import N11Formalization.SevenClassQ0Deg3SectorBinWitness

/-! Lane A: assembles the eight all-row bin shapes into the paid sector shape.

Each `sectorAt_binj_unimodal` theorem is the exact conjunctive record used by
`SectorBinUnimodal`.  The 72-bin peak table is already proved in the witness
module.  This module removes those two hypotheses from the sector reduction;
it does not assert the separate strict-total or area obligations. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorAssembler

open SevenClassQ0Deg3UpperTables
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorBins01AllRows
open SevenClassQ0Deg3SectorBins2AllRows
open SevenClassQ0Deg3SectorBins3AllRows
open SevenClassQ0Deg3SectorBins4AllRows
open SevenClassQ0Deg3SectorBins5AllRows
open SevenClassQ0Deg3SectorBins67AllRows

theorem sectorBinUnimodal : SectorBinUnimodal sectorBinWitness := by
  intro i j
  fin_cases j <;>
    first
    | exact sectorAt_bin0_unimodal i
    | exact sectorAt_bin1_unimodal i
    | exact sectorAt_bin2_unimodal i
    | exact sectorAt_bin3_unimodal i
    | exact sectorAt_bin4_unimodal i
    | exact sectorAt_bin5_unimodal i
    | exact sectorAt_bin6_unimodal i
    | exact sectorAt_bin7_unimodal i

theorem sectorValid : SectorValid :=
  sectorValid_of_bin_unimodal sectorBinWitness sectorBinUnimodal sectorBinPeakValid

end N11Formalization.SevenClassQ0Deg3SectorAssembler
#check @N11Formalization.SevenClassQ0Deg3SectorAssembler.sectorBinUnimodal
#check @N11Formalization.SevenClassQ0Deg3SectorAssembler.sectorValid
#print axioms N11Formalization.SevenClassQ0Deg3SectorAssembler.sectorBinUnimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorAssembler.sectorValid
