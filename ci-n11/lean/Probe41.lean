import Mathlib

noncomputable section
namespace PB

def t4 : Fin 9 := ⟨4, by omega⟩
def t5 : Fin 9 := ⟨5, by omega⟩

-- 关键测试：只靠 core 的 reduce 能否消掉 Fin 的 sub/add
example : ((t5 - 1 : Fin 9) : ℕ) = 4 := by
  simp only [Fin.sub_def, t5, Fin.val_mk, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod]
  norm_num

example : ((t5 - 1 : Fin 9) : ℕ) = 4 := by
  simp [Fin.sub_def, t5]

example : ((t5 - 1 : Fin 9)) = t4 := by
  ext; simp

example : ((t5 - 1 : Fin 9)) = t4 := by
  simp

example : ((t4 + 1 : Fin 9) : ℕ) = 5 := by
  simp only [Fin.add_def, t4, Fin.val_mk, Nat.reduceAdd, Nat.reduceMod]
  norm_num

end PB
