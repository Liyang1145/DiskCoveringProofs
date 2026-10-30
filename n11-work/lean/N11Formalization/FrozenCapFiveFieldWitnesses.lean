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

def H5_2356 : Fin 9 → ℚ := ![(0 : ℚ), (38236545044229700502011612553289438023461276455202812310870663578471 : ℚ) / 180143985094459552029810360320000000000000000000000000000000000000000000, (0 : ℚ), (-53120303717179569537308234306894519098273468124021292197975772096413 : ℚ) / 1801439850944595520298103603200000000000000000000000000000000000000000000, (-163262210991559728605323918393547003473837333723818775064893045053 : ℚ) / 5629499534201861000931573760000000000000000000000000000000000000000000, (0 : ℚ), (44492678024028440706386207334311805906792994102163971375785124438079 : ℚ) / 900719925472297760149051801600000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ)]

theorem weighted_terms_2356 (q : Fin 9) : y5_2356 q * E_2356 q = H5_2356 q := by
  fin_cases q <;> norm_num [y5_2356, E_2356, H5_2356]

theorem strict_gain_2356 : F0_2356 + ∑ q : Fin 9, y5_2356 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2356 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2356]
  have hsum : (∑ q : Fin 9, y5_2356 q * E_2356 q) = ∑ q : Fin 9, H5_2356 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2356 q
  rw [hsum]
  norm_num [F0_2356, H5_2356, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

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

def H5_2360 : Fin 9 → ℚ := ![(0 : ℚ), (290891447272937283450907290774745600581721467339119342126806766528591 : ℚ) / 1801439850944595520298103603200000000000000000000000000000000000000000000, (0 : ℚ), (290838343569225923481709479953316933541270936873031877027 : ℚ) / 450359962736148880074525900800000000000000000000000000000000000000000000, (183102438653079017684568317285465959774479963339283166620728268092147 : ℚ) / 3602879701889191040596207206400000000000000000000000000000000000000000000, (0 : ℚ), (37686854512002951410056464309533805765457602920735020061132196694941 : ℚ) / 450359962736148880074525900800000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ)]

theorem weighted_terms_2360 (q : Fin 9) : y5_2360 q * E_2360 q = H5_2360 q := by
  fin_cases q <;> norm_num [y5_2360, E_2360, H5_2360]

theorem strict_gain_2360 : F0_2360 + ∑ q : Fin 9, y5_2360 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2360 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2360]
  have hsum : (∑ q : Fin 9, y5_2360 q * E_2360 q) = ∑ q : Fin 9, H5_2360 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2360 q
  rw [hsum]
  norm_num [F0_2360, H5_2360, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

end
end N11Formalization.FrozenCapFiveFieldWitnesses

#check @N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2356
#check @N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2360
#print axioms N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2356
#print axioms N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2360
