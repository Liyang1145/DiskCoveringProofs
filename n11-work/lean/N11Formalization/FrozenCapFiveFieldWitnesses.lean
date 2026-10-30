import N11Formalization.FrozenCapRationalCore
import N11Formalization.PaidCellCertificateMCap

/-! Exact five-field rescue witnesses for residual nodes 2356 and 2360.
Generated from the exact-rational recheck report by
`ops/lanes/C/emit_five_field_certificates.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveFieldWitnesses
open Finset ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

def y5_2356 : Fin 9 → ℚ := ![(0 : ℚ), (1 : ℚ) / 8, (0 : ℚ), (1 : ℚ) / 8, (1 : ℚ) / 4, (0 : ℚ), (1 : ℚ) / 4, (0 : ℚ), (1 : ℚ) / 4]

theorem nonneg_2356 : ∀ q, 0 ≤ y5_2356 q := by
  intro q; fin_cases q <;> norm_num [y5_2356]

theorem sum_2356 : (∑ q : Fin 9, y5_2356 q) = 1 := by
  norm_num [y5_2356, Fin.sum_univ_succ]

theorem endpoint_2356 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2356 q) = E_2356 q := by
  fin_cases q <;> norm_num [G_2356, E_2356, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

theorem strict_gain_2356 : F0_2356 + ∑ q : Fin 9, y5_2356 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2356 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2356]
  norm_num [F0_2356, y5_2356, E_2356, N11Formalization.FlashCosineLeaf284Bridge.T]

def y5_2360 : Fin 9 → ℚ := ![(0 : ℚ), (1 : ℚ) / 8, (0 : ℚ), (3 : ℚ) / 16, (3 : ℚ) / 16, (0 : ℚ), (1 : ℚ) / 4, (0 : ℚ), (1 : ℚ) / 4]

theorem nonneg_2360 : ∀ q, 0 ≤ y5_2360 q := by
  intro q; fin_cases q <;> norm_num [y5_2360]

theorem sum_2360 : (∑ q : Fin 9, y5_2360 q) = 1 := by
  norm_num [y5_2360, Fin.sum_univ_succ]

theorem endpoint_2360 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2360 q) = E_2360 q := by
  fin_cases q <;> norm_num [G_2360, E_2360, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

theorem strict_gain_2360 : F0_2360 + ∑ q : Fin 9, y5_2360 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2360 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2360]
  norm_num [F0_2360, y5_2360, E_2360, N11Formalization.FlashCosineLeaf284Bridge.T]

end
end N11Formalization.FrozenCapFiveFieldWitnesses

#check @N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2356
#check @N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2360
#print axioms N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2356
#print axioms N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2360
