import Mathlib
open Real

noncomputable section
namespace PE

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

def aFun (B : BSource) (s : SrcState) : Fin 9 → ℝ := fun k => (aList B s).getD (k : ℕ) 0

def thInit : ℝ := 0
def inc9 (i : Fin 9) : Fin 9 := Fin.mk (((i : ℕ) + 1) % 9) (Nat.mod_lt _ (by norm_num))
def dec9 (i : Fin 9) : Fin 9 := Fin.mk (((i : ℕ) + 8) % 9) (Nat.mod_lt _ (by norm_num))

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

def thetaUpAt (B : BSource) (s : SrcState) (i j : Fin 9) : ℝ :=
  thetaOf (aFun B s) j + aFun B s j + aFun B s i

def thetaDownAt (B : BSource) (s : SrcState) (i j : Fin 9) : ℝ :=
  thetaOf (aFun B s) j - (aFun B s i + aFun B s j)

def thetaLoop (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  let up : Fin 9 → ℝ := fun i => if 4 < (i : ℕ) then thetaUpAt B s i (dec9 i) else thInit
  fun i => if 3 < (i : ℕ) then up i else thetaDownAt B s i (inc9 i)

-- 试验 1：thetaOf 与用 Fin.mk 字面量的闭式向量
def thetaV (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  ![ -((aFun B s ⟨0, by omega⟩ + aFun B s ⟨1, by omega⟩) + (aFun B s ⟨1, by omega⟩ + aFun B s ⟨2, by omega⟩)
        + (aFun B s ⟨2, by omega⟩ + aFun B s ⟨3, by omega⟩) + (aFun B s ⟨3, by omega⟩ + aFun B s ⟨4, by omega⟩)),
     -((aFun B s ⟨1, by omega⟩ + aFun B s ⟨2, by omega⟩) + (aFun B s ⟨2, by omega⟩ + aFun B s ⟨3, by omega⟩)
        + (aFun B s ⟨3, by omega⟩ + aFun B s ⟨4, by omega⟩)),
     -((aFun B s ⟨2, by omega⟩ + aFun B s ⟨3, by omega⟩) + (aFun B s ⟨3, by omega⟩ + aFun B s ⟨4, by omega⟩)),
     -(aFun B s ⟨3, by omega⟩ + aFun B s ⟨4, by omega⟩),
     0,
     aFun B s ⟨4, by omega⟩ + aFun B s ⟨5, by omega⟩,
     (aFun B s ⟨4, by omega⟩ + aFun B s ⟨5, by omega⟩) + (aFun B s ⟨5, by omega⟩ + aFun B s ⟨6, by omega⟩),
     (aFun B s ⟨4, by omega⟩ + aFun B s ⟨5, by omega⟩) + (aFun B s ⟨5, by omega⟩ + aFun B s ⟨6, by omega⟩)
       + (aFun B s ⟨6, by omega⟩ + aFun B s ⟨7, by omega⟩),
     (aFun B s ⟨4, by omega⟩ + aFun B s ⟨5, by omega⟩) + (aFun B s ⟨5, by omega⟩ + aFun B s ⟨6, by omega⟩)
       + (aFun B s ⟨6, by omega⟩ + aFun B s ⟨7, by omega⟩) + (aFun B s ⟨7, by omega⟩ + aFun B s ⟨8, by omega⟩)]

example (B : BSource) (s : SrcState) (k : Fin 9) : thetaOf (aFun B s) k = thetaV B s k := by
  fin_cases k <;> simp [thetaOf, thetaV, aFun]

-- 试验 2：循环式的抽取
def t4 : Fin 9 := ⟨4, by omega⟩
def t5 : Fin 9 := ⟨5, by omega⟩
def t3 : Fin 9 := ⟨3, by omega⟩

example (B : BSource) (s : SrcState) : thetaLoop B s t5 = thetaUpAt B s t5 t4 := by
  simp [thetaLoop, dec9, t5, t4, thInit]
example (B : BSource) (s : SrcState) : thetaLoop B s t4 = thInit := by
  simp [thetaLoop, t4]
example (B : BSource) (s : SrcState) : thetaLoop B s t3 = thetaDownAt B s t3 t4 := by
  simp [thetaLoop, inc9, t3, t4, thInit]

end PE
