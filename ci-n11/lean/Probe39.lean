import Mathlib

noncomputable section
namespace P9

structure BSource where
  PI : ℝ
  C : ℝ → ℝ
  S : ℝ → ℝ
  Q : ℝ → ℝ

structure SrcState where
  xa0 : ℝ
  xa1 : ℝ
  xa2 : ℝ
  xa3 : ℝ
  y0 : ℝ
  y1 : ℝ
  R : ℝ

def aList (B : BSource) (s : SrcState) : List ℝ :=
  [s.xa0, s.xa1, s.xa2, s.xa3, B.PI - 2 * (s.xa0 + s.xa1 + s.xa2 + s.xa3), s.xa3, s.xa2, s.xa1, s.xa0]

def aFun (B : BSource) (s : SrcState) : Fin 9 → ℝ := fun k => (aList B s)[(k : ℕ)]

def thetaOf (A : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![ -((A 0 + A 1) + (A 1 + A 2) + (A 2 + A 3) + (A 3 + A 4)),
     -((A 1 + A 2) + (A 2 + A 3) + (A 3 + A 4)),
     -((A 2 + A 3) + (A 3 + A 4)),
     -(A 3 + A 4),
     0,
     A 4 + A 5,
     (A 4 + A 5) + (A 5 + A 6),
     (A 4 + A 5) + (A 5 + A 6) + (A 6 + A 7),
     (A 4 + A 5) + (A 5 + A 6) + (A 6 + A 7) + (A 7 + A 8) ]

def thInit : ℝ := 0
def t4 : Fin 9 := ⟨4, by omega⟩
def t5 : Fin 9 := ⟨5, by omega⟩

def thetaUp (B : BSource) (s : SrcState) (i : Fin 9) : ℝ :=
  thetaOf (aFun B s) (i - 1) + aFun B s (i - 1) + aFun B s i

def thetaLoop (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  let up : Fin 9 → ℝ := fun i => if 4 < (i : ℕ) then thetaUp B s i else thInit
  fun i => if 3 < (i : ℕ) then up i
    else thetaOf (aFun B s) (i + 1) - (aFun B s i + aFun B s (i + 1))

-- 关键：能否显式化简 (Fin 9).sub / .add 到字面量
example : (t5 - 1 : Fin 9) = t4 := by
  simp only [Fin.sub_def, t5, t4, Fin.mk.injEq]
  norm_num

example : ((t4 + 1 : Fin 9)) = t5 := by
  simp only [Fin.add_def, t4, t5, Fin.mk.injEq]
  norm_num

example (B : BSource) (s : SrcState) :
    thetaLoop B s t5 = thInit + aFun B s t4 + aFun B s t5 := by
  simp only [thetaLoop, t5, t4, thInit, thetaUp, Fin.sub_def, Fin.val_mk, Nat.reduceLT, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceGT, Nat.mod_eq_of_lt, Nat.mod_lt, ↓reduceDIte, if_true]
  ring

end P9
