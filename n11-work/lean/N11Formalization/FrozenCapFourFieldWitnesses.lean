import N11Formalization.FrozenCapRationalCore
import N11Formalization.PaidCellCertificateMCap

/-! Corrected four-field rescue witnesses from
`ops/lanes/C/residual_mixture_faces4.py`.  These reuse the exact `F0`, `G`,
and `E` data from the green rational core; only the unit-sum mixture `y`
changes.  HOST-only
evidence, not kernel credit until CI builds this module. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldWitnesses
open Finset
open ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

def y4_1409 : Fin 9 → ℚ :=
  ![(0 : ℚ), (0 : ℚ), (1 / 4), (1 / 4), (1 / 4), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 4)]

def y4_2337 : Fin 9 → ℚ :=
  ![(0 : ℚ), (1 / 16), (0 : ℚ), (1 / 4), (0 : ℚ), (0 : ℚ), (1 / 4), (0 : ℚ), (7 / 16)]

def y4_2341 : Fin 9 → ℚ :=
  ![(0 : ℚ), (0 : ℚ), (1 / 8), (1 / 4), (0 : ℚ), (1 / 4), (0 : ℚ), (0 : ℚ), (3 / 8)]

def y4_2368 : Fin 9 → ℚ :=
  ![(0 : ℚ), (1 / 8), (0 : ℚ), (1 / 4), (0 : ℚ), (0 : ℚ), (3 / 8), (0 : ℚ), (1 / 4)]

def y4_2370 : Fin 9 → ℚ :=
  ![(0 : ℚ), (1 / 4), (0 : ℚ), (0 : ℚ), (0 : ℚ), (5 / 16), (3 / 16), (0 : ℚ), (1 / 4)]

theorem nonneg_1409 : ∀ q, 0 ≤ y4_1409 q := by
  intro q; fin_cases q <;> norm_num [y4_1409]
theorem sum_1409 : (∑ q : Fin 9, y4_1409 q) = 1 := by norm_num [y4_1409]
theorem endpoint_1409 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_1409 q) = E_1409 q := by
  fin_cases q <;> norm_num [G_1409, E_1409, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

theorem strict_gain_1409 : F0_1409 + ∑ q : Fin 9, y4_1409 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_1409 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_1409]
  norm_num [F0_1409, y4_1409, E_1409, N11Formalization.FlashCosineLeaf284Bridge.T]

theorem nonneg_2337 : ∀ q, 0 ≤ y4_2337 q := by
  intro q; fin_cases q <;> norm_num [y4_2337]
theorem sum_2337 : (∑ q : Fin 9, y4_2337 q) = 1 := by norm_num [y4_2337]
theorem endpoint_2337 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2337 q) = E_2337 q := by
  fin_cases q <;> norm_num [G_2337, E_2337, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

theorem strict_gain_2337 : F0_2337 + ∑ q : Fin 9, y4_2337 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2337 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2337]
  norm_num [F0_2337, y4_2337, E_2337, N11Formalization.FlashCosineLeaf284Bridge.T]

theorem nonneg_2341 : ∀ q, 0 ≤ y4_2341 q := by
  intro q; fin_cases q <;> norm_num [y4_2341]
theorem sum_2341 : (∑ q : Fin 9, y4_2341 q) = 1 := by norm_num [y4_2341]
theorem endpoint_2341 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2341 q) = E_2341 q := by
  fin_cases q <;> norm_num [G_2341, E_2341, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

theorem strict_gain_2341 : F0_2341 + ∑ q : Fin 9, y4_2341 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2341 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2341]
  norm_num [F0_2341, y4_2341, E_2341, N11Formalization.FlashCosineLeaf284Bridge.T]

theorem nonneg_2368 : ∀ q, 0 ≤ y4_2368 q := by
  intro q; fin_cases q <;> norm_num [y4_2368]
theorem sum_2368 : (∑ q : Fin 9, y4_2368 q) = 1 := by norm_num [y4_2368]
theorem endpoint_2368 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2368 q) = E_2368 q := by
  fin_cases q <;> norm_num [G_2368, E_2368, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

theorem strict_gain_2368 : F0_2368 + ∑ q : Fin 9, y4_2368 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2368 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2368]
  norm_num [F0_2368, y4_2368, E_2368, N11Formalization.FlashCosineLeaf284Bridge.T]

theorem nonneg_2370 : ∀ q, 0 ≤ y4_2370 q := by
  intro q; fin_cases q <;> norm_num [y4_2370]
theorem sum_2370 : (∑ q : Fin 9, y4_2370 q) = 1 := by norm_num [y4_2370]
theorem endpoint_2370 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2370 q) = E_2370 q := by
  fin_cases q <;> norm_num [G_2370, E_2370, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

theorem strict_gain_2370 : F0_2370 + ∑ q : Fin 9, y4_2370 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2370 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2370]
  norm_num [F0_2370, y4_2370, E_2370, N11Formalization.FlashCosineLeaf284Bridge.T]

end
end N11Formalization.FrozenCapFourFieldWitnesses

#check @N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_1409
#check @N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_2370
