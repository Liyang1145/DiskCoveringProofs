import Mathlib

noncomputable section
namespace P5

def AV : List ℝ := [1,2,3,4,5,6,7,8,9]
def t0 : Fin 9 := ⟨0, by omega⟩
def t1 : Fin 9 := ⟨1, by omega⟩
def t2 : Fin 9 := ⟨2, by omega⟩
def t3 : Fin 9 := ⟨3, by omega⟩
def t4 : Fin 9 := ⟨4, by omega⟩
def t5 : Fin 9 := ⟨5, by omega⟩
def t6 : Fin 9 := ⟨6, by omega⟩
def t7 : Fin 9 := ⟨7, by omega⟩
def t8 : Fin 9 := ⟨8, by omega⟩

def aF : Fin 9 → ℝ := fun k => AV[k]

def thetaOf' (A : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![ -((A 0 + A 1) + (A 1 + A 2) + (A 2 + A 3) + (A 3 + A 4)),
     -((A 1 + A 2) + (A 2 + A 3) + (A 3 + A 4)),
     -((A 2 + A 3) + (A 3 + A 4)),
     -(A 3 + A 4),
     0,
     A 4 + A 5,
     (A 4 + A 5) + (A 5 + A 6),
     (A 4 + A 5) + (A 5 + A 6) + (A 6 + A 7),
     (A 4 + A 5) + (A 5 + A 6) + (A 6 + A 7) + (A 7 + A 8) ]

def thetaW : Fin 9 → ℝ :=
  ![-(aF t0 + aF t1) - (aF t1 + aF t2) - (aF t2 + aF t3) - (aF t3 + aF t4),
    -(aF t1 + aF t2) - (aF t2 + aF t3) - (aF t3 + aF t4),
    -(aF t2 + aF t3) - (aF t3 + aF t4),
    -(aF t3 + aF t4),
    0,
    aF t4 + aF t5,
    (aF t4 + aF t5) + (aF t5 + aF t6),
    (aF t4 + aF t5) + (aF t5 + aF t6) + (aF t6 + aF t7),
    (aF t4 + aF t5) + (aF t5 + aF t6) + (aF t6 + aF t7) + (aF t7 + aF t8)]

-- 试验 1: fin_cases + simp（不要 ring）
example (k : Fin 9) : thetaOf' aF k = thetaW k := by
  fin_cases k <;> simp [thetaOf', thetaW]

-- 试验 2: fin_cases + simp only（打印剩余目标形态）
example (k : Fin 9) : thetaOf' aF k = thetaW k := by
  fin_cases k <;> simp only [thetaOf', thetaW, Fin.getElem_fin, List.get_eq_getElem, List.length_cons,
      List.length_nil, reduceCtorEq, ↓reduceDIte]

-- 试验 3: 用 rfl 的 Fin.getElem_fin 桥
example : (AV[(0 : Fin 9)] : ℝ) = AV[0] := rfl
example : thetaW t0 = thetaW ⟨0, by omega⟩ := rfl

end P5
