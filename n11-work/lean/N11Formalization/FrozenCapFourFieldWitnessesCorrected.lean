import N11Formalization.FrozenCapRationalCore
import N11Formalization.PaidCellCertificateMCap

/-! Corrected four-field rescue witnesses from `residual_mixture_faces4.py`.
These reuse the exact `F0`, `G`, and `E` data from the green rational core;
only the unit-sum mixture `y` changes. Generated deterministically by
`ops/lanes/C/emit_four_field_witnesses.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldWitnessesCorrected
open Finset
open ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

def y4_1409 : Fin 9 → ℚ :=
  ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (3 : ℚ) / 8, (1 : ℚ) / 8, (0 : ℚ), (0 : ℚ), (1 : ℚ) / 8, (3 : ℚ) / 8]

theorem nonneg_1409 : ∀ q, 0 ≤ y4_1409 q := by
  intro q; fin_cases q <;> norm_num [y4_1409]

theorem sum_1409 : (∑ q : Fin 9, y4_1409 q) = 1 := by
  norm_num [y4_1409, Fin.sum_univ_succ]

theorem endpoint_1409 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_1409 q) = E_1409 q := by
  fin_cases q <;> norm_num [G_1409, E_1409, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H4_1409 : Fin 9 → ℚ := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (-176690814294415957349674512725418540333109912863181833088511533625247 : ℚ) / 1801439850942794080447155404800000000000000000000000000000000000000000000, (-107540641478150957400791726232540979208772073518185479545339241170247 : ℚ) / 360287970188558816089431080960000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (-692203215221170672181156649302027301695577270132307852799191372355603 : ℚ) / 1801439850942794080447155404800000000000000000000000000000000000000000000, (0 : ℚ)]

theorem weighted_terms_1409 (q : Fin 9) : y4_1409 q * E_1409 q = H4_1409 q := by
  fin_cases q <;> norm_num [y4_1409, E_1409, H4_1409]

theorem strict_gain_1409 : F0_1409 + ∑ q : Fin 9, y4_1409 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_1409 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_1409]
  have hsum : (∑ q : Fin 9, y4_1409 q * E_1409 q) = ∑ q : Fin 9, H4_1409 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_1409 q
  rw [hsum]
  norm_num [F0_1409, H4_1409, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

def y4_2337 : Fin 9 → ℚ :=
  ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ) / 4, (1 : ℚ) / 4, (0 : ℚ), (0 : ℚ), (1 : ℚ) / 8, (3 : ℚ) / 8]

theorem nonneg_2337 : ∀ q, 0 ≤ y4_2337 q := by
  intro q; fin_cases q <;> norm_num [y4_2337]

theorem sum_2337 : (∑ q : Fin 9, y4_2337 q) = 1 := by
  norm_num [y4_2337, Fin.sum_univ_succ]

theorem endpoint_2337 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2337 q) = E_2337 q := by
  fin_cases q <;> norm_num [G_2337, E_2337, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H4_2337 : Fin 9 → ℚ := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (-57119431160942358600594165500292026900366203316969618345488765474087 : ℚ) / 300239975157732826691508633600000000000000000000000000000000000000000000, (3930566107672644616933357358051400530524294466690348806503598359481 : ℚ) / 100079991719244275563836211200000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (-29436214888005610768637344838909156470552470544311582539194290200083 : ℚ) / 200159983438488551127672422400000000000000000000000000000000000000000000, (0 : ℚ)]

theorem weighted_terms_2337 (q : Fin 9) : y4_2337 q * E_2337 q = H4_2337 q := by
  fin_cases q <;> norm_num [y4_2337, E_2337, H4_2337]

theorem strict_gain_2337 : F0_2337 + ∑ q : Fin 9, y4_2337 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2337 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2337]
  have hsum : (∑ q : Fin 9, y4_2337 q * E_2337 q) = ∑ q : Fin 9, H4_2337 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2337 q
  rw [hsum]
  norm_num [F0_2337, H4_2337, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

def y4_2341 : Fin 9 → ℚ :=
  ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ) / 4, (1 : ℚ) / 4, (0 : ℚ), (0 : ℚ), (1 : ℚ) / 8, (3 : ℚ) / 8]

theorem nonneg_2341 : ∀ q, 0 ≤ y4_2341 q := by
  intro q; fin_cases q <;> norm_num [y4_2341]

theorem sum_2341 : (∑ q : Fin 9, y4_2341 q) = 1 := by
  norm_num [y4_2341, Fin.sum_univ_succ]

theorem endpoint_2341 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2341 q) = E_2341 q := by
  fin_cases q <;> norm_num [G_2341, E_2341, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H4_2341 : Fin 9 → ℚ := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (-222701513357322186201340017087572235779215585129206654757044412620021 : ℚ) / 900719925472297760149051801600000000000000000000000000000000000000000000, (-12172045188247991367966808415474904765418078876006449486662640225679 : ℚ) / 450359962736148880074525900800000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (-405859922016199437407982751196055802344170627442095266748899668025311 : ℚ) / 1801439850944595520298103603200000000000000000000000000000000000000000000, (0 : ℚ)]

theorem weighted_terms_2341 (q : Fin 9) : y4_2341 q * E_2341 q = H4_2341 q := by
  fin_cases q <;> norm_num [y4_2341, E_2341, H4_2341]

theorem strict_gain_2341 : F0_2341 + ∑ q : Fin 9, y4_2341 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2341 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2341]
  have hsum : (∑ q : Fin 9, y4_2341 q * E_2341 q) = ∑ q : Fin 9, H4_2341 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2341 q
  rw [hsum]
  norm_num [F0_2341, H4_2341, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

end
end N11Formalization.FrozenCapFourFieldWitnessesCorrected

#check @N11Formalization.FrozenCapFourFieldWitnessesCorrected.strict_gain_1409
#check @N11Formalization.FrozenCapFourFieldWitnessesCorrected.strict_gain_2341
#print axioms N11Formalization.FrozenCapFourFieldWitnessesCorrected.strict_gain_1409
#print axioms N11Formalization.FrozenCapFourFieldWitnessesCorrected.strict_gain_2341
