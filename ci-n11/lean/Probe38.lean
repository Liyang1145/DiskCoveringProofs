import Mathlib

noncomputable section
namespace P8

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

@[simp] theorem aList_length (B : BSource) (s : SrcState) : (aList B s).length = 9 := rfl

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

def thetaUp (B : BSource) (s : SrcState) (i : Fin 9) : ℝ :=
  thetaOf (aFun B s) (i - 1) + aFun B s (i - 1) + aFun B s i

def thetaLoop (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  let up : Fin 9 → ℝ := fun i => if 4 < (i : ℕ) then thetaUp B s i else thInit
  fun i => if 3 < (i : ℕ) then up i
    else thetaOf (aFun B s) (i + 1) - (aFun B s i + aFun B s (i + 1))

def t0 : Fin 9 := ⟨0, by omega⟩
def t1 : Fin 9 := ⟨1, by omega⟩
def t2 : Fin 9 := ⟨2, by omega⟩
def t3 : Fin 9 := ⟨3, by omega⟩
def t4 : Fin 9 := ⟨4, by omega⟩
def t5 : Fin 9 := ⟨5, by omega⟩
def t6 : Fin 9 := ⟨6, by omega⟩
def t7 : Fin 9 := ⟨7, by omega⟩
def t8 : Fin 9 := ⟨8, by omega⟩

-- 试验 1：fin_cases k + decide
example (B : BSource) (s : SrcState) (k : Fin 9) : thetaLoop B s k = thetaLoop B s k := by
  fin_cases k <;> decide

-- 试验 2：具体的 thetaLoop_5
example (B : BSource) (s : SrcState) :
    thetaLoop B s t5 = thInit + aFun B s t4 + aFun B s t5 := by
  simp only [thetaLoop, t5, thInit, thetaUp, Fin.reduceLT, ↓reduceDIte, reduceCtorEq, if_true, if_false,
    Fin.val_ofNat, Fin.val_mk, Nat.reduceLT, Nat.reduceGT, Nat.reduceSub, Nat.reduceAdd, Fin.sub_def,
    Fin.add_def, Nat.mod_eq_of_lt, Nat.mod_lt]
  ring

-- 试验 3：simp only + decide 的组合
example (B : BSource) (s : SrcState) :
    thetaLoop B s t5 = thInit + aFun B s t4 + aFun B s t5 := by
  fin_cases (t5 : Fin 9) <;> decide

end P8
