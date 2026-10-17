import Mathlib

noncomputable section
namespace P7

def t4 : Fin 9 := ⟨4, by omega⟩
def thetaOf' (A : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![ 0, 0, 0, 0, 0, A 4 + A 5, 0, 0, 0 ]

-- 用自定义 t4 作下标时向量字面量是否 rfl 掉？
example : thetaOf' (fun _ => (0:ℝ)) t4 = 0 := rfl
example : thetaOf' (fun _ => (0:ℝ)) t4 = (fun _ => (0:ℝ)) 4 + (fun _ => (0:ℝ)) 5 := sorry
example : thetaOf' (fun _ => (0:ℝ)) t4 = 0 := by simp [thetaOf']

-- Fin 字面量版本
example : thetaOf' (fun _ => (0:ℝ)) (5 : Fin 9) = 0 := rfl
example : ![(1:ℝ),2,3,4,5,6,7,8,9] (5:Fin 9) = 6 := rfl
example : ![(1:ℝ),2,3,4,5,6,7,8,9] (⟨5, by omega⟩ : Fin 9) = 6 := by simp

-- Fin 9 的 -1 与 +1
example : ((t4 - 1 : Fin 9)) = (3 : Fin 9) := rfl
example : ((t4 + 1 : Fin 9)) = (5 : Fin 9) := rfl
example : ((3 : Fin 9) + 1 : Fin 9) = 4 := rfl

end P7
