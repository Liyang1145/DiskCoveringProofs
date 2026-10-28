import N11Formalization.HexFloat

open N11Formalization

example : HexFloat.parse "0x1.12e0be826d695p-30" =
    some (⟨false, [1], [1, 2, 14, 0, 11, 14, 8, 2, 6, 13, 6, 9, 5], -30⟩ : HexFloat) := by
  decide

example : (HexFloat.parse "0x1.7cefd3e2947ffp-2") =
    some (⟨false, [1], [7, 12, 14, 15, 13, 3, 14, 2, 9, 4, 7, 15, 15], -2⟩ : HexFloat) := by
  decide

example : (HexFloat.parse "-0x1.b0b66f60b890dp-6") =
    some (⟨true, [1], [11, 0, 11, 6, 6, 15, 6, 0, 11, 8, 9, 0, 13], -6⟩ : HexFloat) := by
  decide

-- ℚ 比较无法被 decide 归约 → 用 norm_num
example : (⟨false, [1], [1, 2, 14, 0, 11, 14, 8, 2, 6, 13, 6, 9, 5], -30⟩ : HexFloat).toQ
    = (4835703278458517 : ℚ) / 2 ^ 82 := by
  norm_num [HexFloat.toQ, hexNatVal]

-- 向量索引能否被 reduce？
def testVec : Fin 12 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

example : testVec 6 = 6 := by decide
example : testVec 11 = 11 := by decide
example : testVec 6 = 6 := rfl

def testHex : Fin 12 → HexFloat := ![
  ⟨false, [1], [7], -2⟩, ⟨false, [1], [5], -2⟩, ⟨false, [1], [1], -2⟩, ⟨false, [1], [8], -2⟩,
  ⟨false, [1], [1], -2⟩, ⟨true, [1], [3], -3⟩, ⟨false, [1], [8], -2⟩, ⟨true, [1], [13], -4⟩,
  ⟨true, [1], [10], -6⟩, ⟨true, [1], [11], -8⟩, ⟨true, [1], [4], -6⟩, ⟨true, [1], [11], -6⟩]

example : (testHex 6).exp = -2 := by decide
example : (testHex 6).neg = false := by decide
