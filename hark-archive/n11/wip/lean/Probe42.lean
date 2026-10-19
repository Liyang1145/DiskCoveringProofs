import Mathlib
open Real

noncomputable section
namespace PC

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

/-- 递增 1（模 9，界由 mod_lt 免费） -/
def inc9 (i : Fin 9) : Fin 9 := Fin.mk (((i : ℕ) + 1) % 9) (Nat.mod_lt _ (by norm_num))
/-- 递减 1（模 9） -/
def dec9 (i : Fin 9) : Fin 9 := Fin.mk (((i : ℕ) + 8) % 9) (Nat.mod_lt _ (by norm_num))

def thetaUpAt (B : BSource) (s : SrcState) (i j : Fin 9) : ℝ :=
  thetaOf (aFun B s) j + aFun B s j + aFun B s i

def thetaDownAt (B : BSource) (s : SrcState) (i j : Fin 9) : ℝ :=
  thetaOf (aFun B s) j - (aFun B s i + aFun B s j)

def thetaLoop (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  fun k =>
    if 4 < (k : ℕ) then thetaUpAt B s k (dec9 k)
    else if 3 < (k : ℕ) then thInit
    else thetaDownAt B s k (inc9 k)

def t4 : Fin 9 := ⟨4, by omega⟩
def t5 : Fin 9 := ⟨5, by omega⟩

-- 关键：dec9/inc9 的具体值靠 rfl 还是 simp？
example : dec9 t5 = t4 := rfl
example : inc9 t4 = t5 := rfl

example (B : BSource) (s : SrcState) : thetaLoop B s t5 = thetaUpAt B s t5 t4 := by
  simp [thetaLoop, dec9, t5, t4]

example (B : BSource) (s : SrcState) : thetaLoop B s t4 = thInit := by
  simp [thetaLoop, t4]

-- 归约到 thetaOf 的引理
def thetaV (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  ![-(aFun B s t5 + aFun B s t4) - (aFun B s t5 + aFun B s t4) - (aFun B s t5 + aFun B s t4) - (aFun B s t5 + aFun B s t4),
    -(aFun B s t5 + aFun B s t4),
    -(aFun B s t5 + aFun B s t4),
    -(aFun B s t5 + aFun B s t4),
    0,
    aFun B s t4 + aFun B s t5,
    (aFun B s t4 + aFun B s t5),
    (aFun B s t4 + aFun B s t5),
    (aFun B s t4 + aFun B s t5)]

example (B : BSource) (s : SrcState) (k : Fin 9) : thetaOf (aFun B s) k = thetaV B s k := by
  fin_cases k <;> simp [thetaOf, thetaV, aFun]

-- 关键测试：分支证明里的 simp
example (B : BSource) (s : SrcState) :
    thetaLoop B s t5 = thetaOf (aFun B s) t4 + aFun B s t4 + aFun B s t5 := by
  rw [show thetaLoop B s t5 = thetaUpAt B s t5 t4 from by simp [thetaLoop, dec9, t5, t4]]
  simp [thetaUpAt]

example (B : BSource) (s : SrcState) : thetaLoop B s t5
    = thetaV B s t5 - (thetaV B s t5 - (thetaOf (aFun B s) t4 + aFun B s t4 + aFun B s t5)) := by
  simp [thetaLoop, dec9, t5, t4, thetaUpAt, thetaV]
  ring

end PC
