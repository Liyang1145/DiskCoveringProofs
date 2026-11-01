import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodalBase
import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodalPeaks0To6
import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodalPeaks7To13
import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodalPeaks14To20

/-! Lane A: thin assembler for the bounded q0 edge-peak modules. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal

/-- All 21 peaks are exactly the separately checked comparisons above. -/
theorem edgePeakValid_all : ∀ i : Fin 21, EdgePeakValid i := by
  intro i
  fin_cases i <;>
    first
    | exact edgePeakValid_0
    | exact edgePeakValid_1
    | exact edgePeakValid_2
    | exact edgePeakValid_3
    | exact edgePeakValid_4
    | exact edgePeakValid_5
    | exact edgePeakValid_6
    | exact edgePeakValid_7
    | exact edgePeakValid_8
    | exact edgePeakValid_9
    | exact edgePeakValid_10
    | exact edgePeakValid_11
    | exact edgePeakValid_12
    | exact edgePeakValid_13
    | exact edgePeakValid_14
    | exact edgePeakValid_15
    | exact edgePeakValid_16
    | exact edgePeakValid_17
    | exact edgePeakValid_18
    | exact edgePeakValid_19
    | exact edgePeakValid_20

/-- Once the two monotonicity sides are proved for every edge, the peak checks
above pay all 21 × 2049 grid inequalities. -/
theorem edgeValid_of_monotone (h : EdgeMonotone) : EdgeValid :=
  edgeValid_of_unimodal fun i => ⟨(h i).1, (h i).2, edgePeakValid_all i⟩

end N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal
#check @N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_unimodal
#check @N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_monotone
#print axioms N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgeValid_of_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal.edgePeakValid_all
