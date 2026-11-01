import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodalBase

/-! Bounded edge-peak check 12. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal

open MetricAreaRationalCertificate
open SevenClassQ0Deg3UpperTables

attribute [local simp] edgeUpper nodeQ edgeCoeff tableEdges

theorem edgePeakValid_12 : EdgePeakValid 12 := by
  unfold EdgePeakValid
  rw [show edgeWitness 12 = (0 : Fin 2049) by decide +kernel]
  rw [show edgeMaxAt 12 = (0/1) by rfl]
  norm_num [EdgePeakValid, edgeUpper, edgeCoeff, tableEdges, mu, edgeMaxAt,
    nodeQ, sinHiNLag, sinTQ, Finset.sum_range_succ,
    RatInterval.piHi, Fin.val_ofNat, Fin.val_mk]

end N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal
