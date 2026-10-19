/-
DCPN11Core/RootBox.lean

Exact integer arithmetic on the C891 isolating box (core Lean only, no `sorry`).

Source: `math_data/n11/root_input.json` (extracted from
`cover11/.../lead/repaired_tc_krawczyk.json`). The 12 hex centres and the common
halfwidth are exact binary64 dyadics. Every one of them is an integer multiple of
2^-82, so we store numerators over the common denominator `DEN = 2^82`.
Coordinates: p = (a0, a1, a2, a3, y0, y1, R, λ0, ..., λ4).

The rational numbers here are cross-checked against the Mathlib-side `boxCenter`
in `DCPN11/Candidate.lean` (same values, written as `n / 2^k`).
-/

namespace DCPCore.RootBox

def DEN : Int := 2 ^ 82

/-- `center_hex` scaled by 2^82 (exact). -/
def cN : List Int :=
  [1798923303253045711732736, 1648215927070454278258688, 1357971486201307277033472,
   1852132488086765730529280, 1320038028956408827871232, -722591882156218379141120,
   1837489164292903359479808, -550469526131384294309888, -123900821081827011723264,
   -32134999671245847396352, -95985931945594612350976, -127714228352410621837312]

/-- `radius_hex = 0x1.12e0be826d695p-30` scaled by 2^82 (exact). -/
def rN : Int := 4835703278458517

def lo (i : Nat) : Int := cN.getD i 0 - rN
def hi (i : Nat) : Int := cN.getD i 0 + rN

theorem cN_length : cN.length = 12 := by decide

/-- The hex value 0x1.851a7cb8a18fbp-2 of the R-centre, recomputed from its digits. -/
theorem R_center_from_hex : cN.getD 6 0 = 0x1851a7cb8a18fb * 2 ^ 28 := by decide

theorem rN_from_hex : rN = 0x112e0be826d695 := by decide

/-- R-coordinate of every box point lies strictly below 19/50 (used by C922: R* < 19/50). -/
theorem R_hi_lt_19_50 : 50 * hi 6 < 19 * DEN := by decide

/-- 0.379983852 < R < 0.379983855 on the whole box (a coarse rational enclosure of R*;
the 30-digit enclosure of the source needs the Krawczyk refinement, not just the box). -/
theorem R_enclosure : 379983852 * DEN < 10 ^ 9 * lo 6 ∧ 10 ^ 9 * hi 6 < 379983855 * DEN := by
  decide

/-- The four free half-angles a0..a3 are positive on the box. -/
theorem angles_pos : (List.range 4).all (fun i => decide (0 < lo i)) = true := by decide

/-- a0+a1+a2+a3 < 1.57 on the box; with π > 3.14 this gives a4 = π - 2Σ > 0. -/
theorem angle_sum_hi : 100 * (hi 0 + hi 1 + hi 2 + hi 3) < 157 * DEN := by decide

/-- a0+a1+a2+a3 > 1.376 on the box; with π < 3.15 this gives a4 < 0.4 < π/2. -/
theorem angle_sum_lo : 1376 * DEN < 1000 * (lo 0 + lo 1 + lo 2 + lo 3) := by decide

/-- Each half-angle a0..a3 is < 0.39 on the box, hence < π/2 and sin(a_k) < R is plausible
(the strict branch condition sin² a_k < R² itself needs interval trigonometry). -/
theorem angles_hi : (List.range 4).all (fun i => decide (100 * hi i < 39 * DEN)) = true := by
  decide

/-- Hubs are strictly interior in the crude sense |y_j| + R < 1. -/
theorem hubs_interior :
    100 * (hi 4 + hi 6) < 100 * DEN ∧ 100 * (-(lo 5) + hi 6) < 100 * DEN := by decide

/-- Hub order: y1 < 0 < y0 on the box, so the two hubs are distinct. -/
theorem hub_order : hi 5 < 0 ∧ 0 < lo 4 := by decide

/-- Hub half-separation d = (y1 - y0)/2 satisfies d² < R² (waist square root is real). -/
theorem waist_branch : hi 4 - lo 5 < 2 * lo 6 := by decide

/-- The multipliers λ0..λ4 are all strictly negative on the box (sign pattern of the KKT
point; recorded for reference). -/
theorem multipliers_neg : (List.range 5).all (fun k => decide (hi (7 + k) < 0)) = true := by
  decide

end DCPCore.RootBox
