import Mathlib
namespace ProbeFin2
example : ((1 : Fin 9) + 1) = 2 := by decide
example : ((1 : Fin 9) + 1) = 2 := rfl
example : ((8 : Fin 9) + 1) = 0 := by decide
example : ((2 : Fin 9) + 1) = 3 := by decide
example : ((1 + 1 : Fin 9)) = (2 : Fin 9) := by norm_num
end ProbeFin2
