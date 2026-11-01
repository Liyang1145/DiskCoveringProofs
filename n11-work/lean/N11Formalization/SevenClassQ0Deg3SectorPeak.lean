import N11Formalization.SevenClassQ0Deg3SectorPeakBase
import N11Formalization.SevenClassQ0Deg3SectorPeak00
import N11Formalization.SevenClassQ0Deg3SectorPeak01
import N11Formalization.SevenClassQ0Deg3SectorPeak02
import N11Formalization.SevenClassQ0Deg3SectorPeak03
import N11Formalization.SevenClassQ0Deg3SectorPeak04
import N11Formalization.SevenClassQ0Deg3SectorPeak05
import N11Formalization.SevenClassQ0Deg3SectorPeak06
import N11Formalization.SevenClassQ0Deg3SectorPeak07
import N11Formalization.SevenClassQ0Deg3SectorPeak08

/-! Lane A: thin assembler for the bounded sector-peak modules. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorPeak

open SevenClassQ0Deg3Bins

theorem sectorPeakValid_all : ∀ i : Fin 9, SectorPeakValid i := by
  intro i
  fin_cases i <;>
    first
    | exact sectorPeakValid_0
    | exact sectorPeakValid_1
    | exact sectorPeakValid_2
    | exact sectorPeakValid_3
    | exact sectorPeakValid_4
    | exact sectorPeakValid_5
    | exact sectorPeakValid_6
    | exact sectorPeakValid_7
    | exact sectorPeakValid_8

/-- All sector obligations reduce to the two explicit shape halves. -/
theorem sectorValid_of_shape (hshape : SectorUnimodal) : SectorValid :=
  sectorValid_of_unimodal hshape sectorPeakValid_all

end N11Formalization.SevenClassQ0Deg3SectorPeak
#check @N11Formalization.SevenClassQ0Deg3SectorPeak.sectorValid_of_unimodal
#check @N11Formalization.SevenClassQ0Deg3SectorPeak.sectorValid_of_shape
#print axioms N11Formalization.SevenClassQ0Deg3SectorPeak.sectorValid_of_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorPeak.sectorPeakValid_all
