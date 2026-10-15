import Mathlib
namespace ProbeFin
def foo : Fin 5 → ℕ
  | 0 => 10
  | 1 => 20
  | 2 => 30
  | 3 => 40
  | 4 => 50
example : foo 2 = 30 := by simp only [foo]
example : foo 2 = 30 := rfl
example : foo 3 = 40 := by norm_num [foo]
example : foo 4 = 50 := by decide
def bar : Fin 4 → ℚ
  | 0 => 1/2
  | 1 => 1/3
  | 2 => 1/5
  | 3 => 1/7
example : bar 2 = 1/5 := by simp only [bar]
example : (bar 1 + bar 3) = 1/3 + 1/7 := by simp only [bar]
example : (bar 2 : ℚ) < 1 := by norm_num [bar]
end ProbeFin
