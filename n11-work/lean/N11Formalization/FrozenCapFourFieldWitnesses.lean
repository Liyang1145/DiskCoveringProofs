import N11Formalization.FrozenCapRationalCore
import N11Formalization.PaidCellCertificateMCap

/-! Corrected four-field rescue witnesses from `residual_mixture_faces4.py`.
These reuse the exact `F0`, `G`, and `E` data from the green rational core;
only the unit-sum mixture `y` changes. Generated deterministically by
`ops/lanes/C/emit_four_field_witnesses.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldWitnesses
open Finset
open ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

def y4_1409 : Fin 9 → ℚ :=
  ![(0 : ℚ), (0 : ℚ), (1 : ℚ) / 4, (1 : ℚ) / 4, (1 : ℚ) / 4, (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ) / 4]

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

def H4_1409 : Fin 9 → ℚ := ![(0 : ℚ), (0 : ℚ), (3830450154307130290174428662259179277443144855509849782467987935957 : ℚ) / 7205759403771176321788621619200000000000000000000000000000000000000000, (-58896938098138652449891504241806180111036637621060611029503844541749 : ℚ) / 900719925471397040223577702400000000000000000000000000000000000000000000, (-107540641478150957400791726232540979208772073518185479545339241170247 : ℚ) / 180143985094279408044715540480000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]

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
  ![(0 : ℚ), (1 : ℚ) / 16, (0 : ℚ), (1 : ℚ) / 4, (0 : ℚ), (0 : ℚ), (1 : ℚ) / 4, (0 : ℚ), (7 : ℚ) / 16]

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

def H4_2337 : Fin 9 → ℚ := ![(0 : ℚ), (17487625653710963295377603076322988078820074308377623082501760188703 : ℚ) / 85782850045066521911859609600000000000000000000000000000000000000000000, (0 : ℚ), (-57119431160942358600594165500292026900366203316969618345488765474087 : ℚ) / 300239975157732826691508633600000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (71438929530695479653569251918973144939702942657477934587417067363 : ℚ) / 667199944794961837092241408000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ)]

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
  ![(0 : ℚ), (0 : ℚ), (1 : ℚ) / 8, (1 : ℚ) / 4, (0 : ℚ), (1 : ℚ) / 4, (0 : ℚ), (0 : ℚ), (3 : ℚ) / 8]

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

def H4_2341 : Fin 9 → ℚ := ![(0 : ℚ), (0 : ℚ), (296737519855937876576674101396542511401654782366007479968266516867243 : ℚ) / 1801439850944595520298103603200000000000000000000000000000000000000000000, (-222701513357322186201340017087572235779215585129206654757044412620021 : ℚ) / 900719925472297760149051801600000000000000000000000000000000000000000000, (0 : ℚ), (-6086022592984382354824268830568022211505042800441091350406454487611 : ℚ) / 225179981368074440037262950400000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (0 : ℚ)]

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

def y4_2368 : Fin 9 → ℚ :=
  ![(0 : ℚ), (1 : ℚ) / 8, (0 : ℚ), (1 : ℚ) / 4, (0 : ℚ), (0 : ℚ), (3 : ℚ) / 8, (0 : ℚ), (1 : ℚ) / 4]

theorem nonneg_2368 : ∀ q, 0 ≤ y4_2368 q := by
  intro q; fin_cases q <;> norm_num [y4_2368]

theorem sum_2368 : (∑ q : Fin 9, y4_2368 q) = 1 := by
  norm_num [y4_2368, Fin.sum_univ_succ]

theorem endpoint_2368 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2368 q) = E_2368 q := by
  fin_cases q <;> norm_num [G_2368, E_2368, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H4_2368 : Fin 9 → ℚ := ![(0 : ℚ), (212656920867228742716150343000961943601313441063141555340228396756269 : ℚ) / 112589990684037220018631475200000000000000000000000000000000000000000000, (0 : ℚ), (-109623095273000900541228768454115957358782091998325194887847921234917 : ℚ) / 900719925472297760149051801600000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (35130266923328443732279374443921555220631465084314622822654302069249 : ℚ) / 28147497671009305004657868800000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ)]

theorem weighted_terms_2368 (q : Fin 9) : y4_2368 q * E_2368 q = H4_2368 q := by
  fin_cases q <;> norm_num [y4_2368, E_2368, H4_2368]

theorem strict_gain_2368 : F0_2368 + ∑ q : Fin 9, y4_2368 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2368 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2368]
  have hsum : (∑ q : Fin 9, y4_2368 q * E_2368 q) = ∑ q : Fin 9, H4_2368 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2368 q
  rw [hsum]
  norm_num [F0_2368, H4_2368, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

def y4_2370 : Fin 9 → ℚ :=
  ![(0 : ℚ), (1 : ℚ) / 4, (0 : ℚ), (0 : ℚ), (0 : ℚ), (5 : ℚ) / 16, (3 : ℚ) / 16, (0 : ℚ), (1 : ℚ) / 4]

theorem nonneg_2370 : ∀ q, 0 ≤ y4_2370 q := by
  intro q; fin_cases q <;> norm_num [y4_2370]

theorem sum_2370 : (∑ q : Fin 9, y4_2370 q) = 1 := by
  norm_num [y4_2370, Fin.sum_univ_succ]

theorem endpoint_2370 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2370 q) = E_2370 q := by
  fin_cases q <;> norm_num [G_2370, E_2370, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H4_2370 : Fin 9 → ℚ := ![(0 : ℚ), (3187194356747073663954161438511821611268588678798025700516136977619713 : ℚ) / 900719925472297760149051801600000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ), (0 : ℚ), (495026871942298517319921173713923825259661743329706308573416940452481 : ℚ) / 720575940377838208119241441280000000000000000000000000000000000000000000, (357619630403994304109435278771119359078162690248301767850099548018737 : ℚ) / 720575940377838208119241441280000000000000000000000000000000000000000000, (0 : ℚ), (0 : ℚ)]

theorem weighted_terms_2370 (q : Fin 9) : y4_2370 q * E_2370 q = H4_2370 q := by
  fin_cases q <;> norm_num [y4_2370, E_2370, H4_2370]

theorem strict_gain_2370 : F0_2370 + ∑ q : Fin 9, y4_2370 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2370 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2370]
  have hsum : (∑ q : Fin 9, y4_2370 q * E_2370 q) = ∑ q : Fin 9, H4_2370 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2370 q
  rw [hsum]
  norm_num [F0_2370, H4_2370, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

end
end N11Formalization.FrozenCapFourFieldWitnesses

#check @N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_1409
#check @N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_2370
#print axioms N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_1409
#print axioms N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_2370
