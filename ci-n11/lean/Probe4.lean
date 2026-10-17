import N11Formalization.HexFloat

open N11Formalization

def decRadiusHex : HexFloat := ⟨false, [1], [1, 2, 14, 0, 11, 14, 8, 2, 6, 13, 6, 9, 5], -30⟩

def decCenterHex : Fin 12 → HexFloat :=
  ![
    ⟨false, [1], [7, 12, 14, 15, 13, 3, 14, 2, 9, 4, 7, 15, 15], -2⟩,
    ⟨false, [1], [5, 13, 0, 5, 15, 6, 14, 5, 11, 8, 5, 5, 5], -2⟩,
    ⟨false, [1], [1, 15, 8, 15, 12, 8, 2, 2, 7, 2, 12, 12, 5], -2⟩,
    ⟨false, [1], [8, 8, 3, 4, 4, 13, 10, 9, 6, 0, 6, 12, 11], -2⟩,
    ⟨false, [1], [1, 7, 8, 7, 6, 7, 10, 10, 0, 2, 10, 2, 1], -2⟩,
    ⟨true, [1], [3, 2, 0, 7, 9, 1, 9, 15, 13, 10, 6, 10, 14], -3⟩,
    ⟨false, [1], [8, 5, 1, 10, 7, 12, 11, 8, 10, 1, 8, 15, 11], -2⟩,
    ⟨true, [1], [13, 2, 4, 4, 0, 13, 1, 12, 15, 15, 12, 11, 4], -4⟩,
    ⟨true, [1], [10, 3, 12, 10, 13, 4, 13, 13, 15, 3, 12, 11, 9], -6⟩,
    ⟨true, [1], [11, 3, 8, 2, 10, 13, 3, 9, 9, 14, 4, 3, 13], -8⟩,
    ⟨true, [1], [4, 5, 3, 6, 8, 6, 5, 6, 5, 4, 1, 5, 2], -6⟩,
    ⟨true, [1], [11, 0, 11, 6, 6, 15, 6, 0, 11, 8, 9, 0, 13], -6⟩]

def decCenter6 : HexFloat := ⟨false, [1], [8, 5, 1, 10, 7, 12, 11, 8, 10, 1, 8, 15, 11], -2⟩

-- 向量索引可以被 rfl 归约
example : decCenterHex 6 = decCenter6 := rfl

-- 用 simp + norm_num 处理 hexNatVal
example : decRadiusHex.toQ = (4835703278458517 : ℚ) / 2 ^ 82 := by
  simp only [decRadiusHex, HexFloat.toQ, hexNatVal, List.length_cons, List.length_nil,
    pow_succ, pow_zero, Nat.cast_ofNat, Nat.cast_one, mul_one]
  norm_num

example : decCenter6.toQ = (6845180557269243 : ℚ) / 2 ^ 54 := by
  simp only [decCenter6, HexFloat.toQ, hexNatVal, List.length_cons, List.length_nil,
    pow_succ, pow_zero, Nat.cast_ofNat, Nat.cast_one, mul_one]
  norm_num
