import Mathlib
open Real

noncomputable section
namespace PD

def l9 : List ℝ := [10,11,12,13,14,15,16,17,18]
def t4 : Fin 9 := ⟨4, by omega⟩
def t5 : Fin 9 := ⟨5, by omega⟩

-- getD 版本：具体下标是否 rfl？
example : l9.getD (t4 : ℕ) 0 = 14 := rfl
example : l9.getD (t4 : ℕ) 0 = l9.getD 4 0 := rfl

-- Fin.mk 版本
example : l9.getD (((4 : ℕ) : Fin 9) : ℕ) 0 = 14 := rfl

-- 用一个 canonical: `af k := l9.getD (k:ℕ) 0`
def af : Fin 9 → ℝ := fun k => l9.getD (k : ℕ) 0

def v2 : Fin 9 → ℝ := ![af t4 + af t5, af t4 - af t5, 0, 0, 0, 0, 0, 0, 0]

example : v2 t4 = af t4 + af t5 := rfl
example : v2 t4 = l9.getD 4 0 + l9.getD 5 0 := rfl

def thetaOf' (A : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![ A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8 ]

def thV : Fin 9 → ℝ := ![af t0', af t1', 0, 0, 0, 0, 0, 0, 0] where
  t0' : Fin 9 := ⟨0, by omega⟩
  t1' : Fin 9 := ⟨1, by omega⟩

example (k : Fin 9) : thetaOf' af k = af k := by
  fin_cases k <;> rfl

example (k : Fin 9) : thetaOf' af k = af k := by
  fin_cases k <;> simp [thetaOf']

example (k : Fin 9) : thetaOf' af k = thV k := by
  fin_cases k <;> simp [thetaOf', thV, af]

example (k : Fin 9) : thetaOf' af k = thV k := by
  fin_cases k <;> rfl

end PD
