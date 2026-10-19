/-
DCPN11/Candidate.lean  —  exact definition of R* (C891 root).

STATUS: NOT YET COMPILED (see STATUS.md). Definitions transcribe
`N11-GLOBAL-OPTIMALITY-THEOREM.md` §"Exact definition and an attaining configuration"
and `model`/`system` in `tools/mathcheck_n11.py` line by line.

  z = (a0,a1,a2,a3,y0,y1,R),   a4 = π - 2(a0+a1+a2+a3),
  a = (a0,a1,a2,a3,a4,a3,a2,a1,a0),   θ4 = 0,  θ(k+1) - θk = a k + a (k+1),
  ρk = cos a_k - √(R² - sin² a_k),    C_k = ρk (cos θk, sin θk),
  H0 = (y0,0), H1 = (y1,0),  B_k = (cos(θk+ak), sin(θk+ak)),  U_k = C_k + C_{k+1} - B_k,
  m = (y0+y1)/2, d = (y1-y0)/2, W = (m, √(R²-d²)),
  f(z) = (|U1-H1|-R, |U2-H0|-R, |U3-H0|-R, |U8-H1|-R, |W-C6|-R),
  KKT:  f(z) = 0,  e_R - Df(z)ᵀ λ = 0   (12 equations in p = (z, λ) ∈ ℝ¹²).
R* is coordinate 6 of the unique solution in the exact dyadic box `InBox`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Real

noncomputable section

namespace DCP.N11

/-- Point of the plane from Cartesian coordinates. -/
def pt (x y : ℝ) : ℂ := ⟨x, y⟩

/-- `z = (a0, a1, a2, a3, y0, y1, R)`. -/
abbrev Z := Fin 7 → ℝ

/-- Half-angle vector `a = (a0,a1,a2,a3,a4,a3,a2,a1,a0)`, `a4 = π - 2(a0+a1+a2+a3)`. -/
def halfAngle (z : Z) : Fin 9 → ℝ :=
  ![z 0, z 1, z 2, z 3, π - 2 * (z 0 + z 1 + z 2 + z 3), z 3, z 2, z 1, z 0]

/-- Centre angles: `θ4 = 0`, `θ(k+1) - θk = a k + a (k+1)` (exactly as in `model`). -/
def theta (z : Z) : Fin 9 → ℝ :=
  let a := halfAngle z
  ![-(a 3 + a 4) - (a 2 + a 3) - (a 1 + a 2) - (a 0 + a 1),
    -(a 3 + a 4) - (a 2 + a 3) - (a 1 + a 2),
    -(a 3 + a 4) - (a 2 + a 3),
    -(a 3 + a 4),
    0,
    a 4 + a 5,
    a 4 + a 5 + (a 5 + a 6),
    a 4 + a 5 + (a 5 + a 6) + (a 6 + a 7),
    a 4 + a 5 + (a 5 + a 6) + (a 6 + a 7) + (a 7 + a 8)]

/-- Radius used everywhere: `R = z 6`. -/
def Rad (z : Z) : ℝ := z 6

/-- Inner radial root `ρk = cos a_k - √(R² - sin² a_k)`. -/
def rho (z : Z) (k : Fin 9) : ℝ :=
  cos (halfAngle z k) - √(Rad z ^ 2 - sin (halfAngle z k) ^ 2)

/-- Ring centre `C_k`. -/
def ringSite (z : Z) (k : Fin 9) : ℂ :=
  pt (rho z k * cos (theta z k)) (rho z k * sin (theta z k))

def hub0 (z : Z) : ℂ := pt (z 4) 0
def hub1 (z : Z) : ℂ := pt (z 5) 0

/-- Boundary switch `B_k`. -/
def switchPt (z : Z) (k : Fin 9) : ℂ :=
  pt (cos (theta z k + halfAngle z k)) (sin (theta z k + halfAngle z k))

/-- Pin `U_k = C_k + C_{k+1} - B_k` (indices mod 9: `Fin 9` addition wraps). -/
def pin (z : Z) (k : Fin 9) : ℂ := ringSite z k + ringSite z (k + 1) - switchPt z k

/-- Waist point `W = (m, √(R² - d²))`. -/
def waist (z : Z) : ℂ :=
  pt ((z 4 + z 5) / 2) (√(Rad z ^ 2 - ((z 5 - z 4) / 2) ^ 2))

/-- The five contact constraints `f(z)`. -/
def con (z : Z) : Fin 5 → ℝ :=
  ![‖pin z 1 - hub1 z‖ - Rad z, ‖pin z 2 - hub0 z‖ - Rad z, ‖pin z 3 - hub0 z‖ - Rad z,
    ‖pin z 8 - hub1 z‖ - Rad z, ‖waist z - ringSite z 6‖ - Rad z]

/-- `p = (z, λ)`. -/
def zPart (p : Fin 12 → ℝ) : Z := fun i => p (Fin.castLE (by norm_num) i)
def lamPart (p : Fin 12 → ℝ) : Fin 5 → ℝ := fun k => p (Fin.natAdd 7 k)

/-- `∂ f_k / ∂ z_j` as a Fréchet derivative (the checker's automatic derivative). -/
def dCon (z : Z) (k : Fin 5) (j : Fin 7) : ℝ :=
  fderiv ℝ (fun w : Z => con w k) z (Pi.single j 1)

/-- The 12-equation KKT residual: rows 0..4 are `f(z)`, rows 5..11 are
`(e_R - Df(z)ᵀ λ)_j`, `j = 0..6`, with `e_R` the unit vector of coordinate `R = z 6`. -/
def kkt (p : Fin 12 → ℝ) : Fin 12 → ℝ := fun i =>
  if h : i.val < 5 then con (zPart p) ⟨i.val, h⟩
  else (if i.val = 11 then 1 else 0) -
    ∑ k : Fin 5, lamPart p k * dCon (zPart p) k ⟨i.val - 5, by omega⟩

/-- `center_hex` of `math_data/n11/root_input.json` as exact rationals. -/
def boxCenter : Fin 12 → ℚ :=
  ![(6701511529285631 : ℚ) / 18014398509481984,
    (6140082802885973 : ℚ) / 18014398509481984,
    (5058838003133637 : ℚ) / 18014398509481984,
    (6899731189335755 : ℚ) / 18014398509481984,
    (4917524862872097 : ℚ) / 18014398509481984,
    (-2691864528343895 : ℚ) / 18014398509481984,
    (6845180557269243 : ℚ) / 18014398509481984,
    (-2050658785296173 : ℚ) / 18014398509481984,
    (-7385064427961529 : ℚ) / 288230376151711744,
    (-7661580961047613 : ℚ) / 1152921504606846976,
    (-2860603688525993 : ℚ) / 144115188075855872,
    (-7612361213708557 : ℚ) / 288230376151711744]

/-- `radius_hex = 0x1.12e0be826d695p-30` (common halfwidth), exact. -/
def boxRad : ℚ := (4835703278458517 : ℚ) / 4835703278458516698824704

/-- The closed C891 isolating box. -/
def InBox (p : Fin 12 → ℝ) : Prop := ∀ i, |p i - (boxCenter i : ℝ)| ≤ (boxRad : ℝ)

/-- `R*`: the R-coordinate of the (unique, by C891) KKT root in the box. Defined without
reference to any unproved lemma; `C891_exists_unique` identifies the set as a singleton. -/
def Rstar : ℝ := sInf {R : ℝ | ∃ p, InBox p ∧ kkt p = 0 ∧ p 6 = R}

/-- **C891** (Krawczyk): the KKT system has exactly one root in the box.
Source: `repair_tc_krawczyk.py`, `repaired_tc_krawczyk.json`, `tools/mathcheck_n11.py`
`root_check`. Needs: differentiability of `con` on the box (legal sqrt branches), an interval
enclosure of the Jacobian over the box, a rational preconditioner `Y`, and the Krawczyk
inclusion `K(X) ⊂ int X` with `‖I - Y J(X)‖ < 1`; the latter is a finite rational/interval
computation (target for a verified interval library or proof by reflection). -/
theorem C891_exists_unique : ∃! p : Fin 12 → ℝ, InBox p ∧ kkt p = 0 := by
  sorry

/-- Box bounds on the R-coordinate (all are exact rational facts; the integer versions are
machine-checked in `DCPN11Core/RootBox.lean`). -/
theorem box_R_bounds {p : Fin 12 → ℝ} (hp : InBox p) :
    (379983852 : ℝ) / 10 ^ 9 < p 6 ∧ p 6 < 379983855 / 10 ^ 9 ∧ p 6 < 19 / 50 := by
  -- draft
  have h := hp 6
  rw [abs_le] at h
  simp only [boxCenter, boxRad] at h
  norm_num at h ⊢
  constructor <;> [skip; constructor] <;> linarith [h.1, h.2]

/-- `Rstar` is the R-coordinate of the C891 root. -/
theorem Rstar_spec : ∃ p, InBox p ∧ kkt p = 0 ∧ p 6 = Rstar := by
  -- draft: the defining set is the singleton {p₀ 6}
  obtain ⟨p₀, ⟨hb, hk⟩, huniq⟩ := C891_exists_unique
  have hset : {R : ℝ | ∃ p, InBox p ∧ kkt p = 0 ∧ p 6 = R} = {p₀ 6} := by
    ext R; constructor
    · rintro ⟨p, hp, hpk, rfl⟩; rw [huniq p ⟨hp, hpk⟩]; rfl
    · rintro rfl; exact ⟨p₀, hb, hk, rfl⟩
  exact ⟨p₀, hb, hk, by rw [Rstar, hset, csInf_singleton]⟩

/-- **C922 (coarse part)**: `R* < 19/50`. -/
theorem Rstar_lt_19_50 : Rstar < 19 / 50 := by
  -- draft
  obtain ⟨p, hp, -, h6⟩ := Rstar_spec
  exact h6 ▸ (box_R_bounds hp).2.2

theorem Rstar_pos : 0 < Rstar := by
  -- draft
  obtain ⟨p, hp, -, h6⟩ := Rstar_spec
  have := (box_R_bounds hp).1
  rw [← h6]; linarith [show (0:ℝ) < 379983852 / 10 ^ 9 by norm_num]

/-- The 30-digit enclosure stated in the theorem file. Needs the Krawczyk refinement
(C922 / `contract_exact_root_threshold.py`), not just the box. -/
theorem Rstar_enclosure :
    (3799838531198386897222616061358 : ℝ) / 10 ^ 31 < Rstar ∧
    Rstar < 3799838531198386897222616061364 / 10 ^ 31 := by
  sorry

end DCP.N11
