import N11Formalization.Interval.Range

/-!
# fm-eval 探针 2：内核求值能力的边界（决定读数用哪条路线）

T1–T4：ℚ 的算术/比较在内核里到底能归约到什么程度（DEAD B1 只否证了「含除法归一化的大数比较」）。
T5：`Int.floor` 在 `inWindow` 守卫里的可解性（相位估计量路线）。
T6：`Int.emod` 在 `norm_num` 下的可解性（四态表 `k % 4` 路线）。
-/

namespace N11Formalization

namespace RatInterval

/-! ## T1 ℚ 比较/算术的内核归约（大数 + 除法归一化） -/

example : ((6701511529285631 / 18014398509481984 : ℚ) ≤ (3 / 4 : ℚ)) := by decide

example : ((6701511529285631 / 18014398509481984 : ℚ) ≤ (3 / 4 : ℚ)) := by norm_num

example : (((1 / 3 : ℚ) + 1 / 6) = 1 / 2) := by decide

example : ((((1 / 3 : ℚ)) * (3 / 2)) ≤ 1) := by decide

example : Rat.mul (1 / 3) (3 / 2) = 1 / 2 := by decide

example : (((6701511529285631 / 18014398509481984 : ℚ) + 1 / 7) ≤ 1) := by decide

/-! ## T2 `Nat.sqrt` 的 `norm_num` 路线（B1 已知：`decide` 不行） -/

example : Nat.sqrt 16 = 4 := by norm_num

example : Nat.sqrt (6701511529285631 * 18014398509481984) ≤
    6701511529285631 * 18014398509481984 := by norm_num

/-! ## T3 `Int.floor` / `Int.emod` 的 `norm_num` 路线 -/

example : ⌊(6701511529285631 / 18014398509481984 : ℚ) + 1 / 2⌋ = 0 := by norm_num

example : ⌊(-3 : ℚ) / 2⌋ = -2 := by norm_num

example : ((-3 : ℤ) % 4 = 1) := by norm_num

example : (if (-3 : ℤ) % 4 = 0 then (5 : ℚ) else 7) = 7 := by norm_num

example : (if (-3 : ℤ) % 4 = 1 then (5 : ℚ) else 7) = 5 := by norm_num

/-! ## T4 `inWindow` 守卫（含 `halfPiLo/halfPiHi/piLo/piHi` 展开） -/

example : inWindow (intv (1 / 4) (1 / 2)) 0 := by
  simp only [inWindow, intv]
  norm_num [halfPiLo, halfPiHi, piLo, piHi]

example : ¬ inWindow (intv 3 4) 0 := by
  simp only [inWindow, intv]
  norm_num [halfPiLo, halfPiHi, piLo, piHi]

example : ¬ inWindow (intv (1 / 4) (1 / 2)) 1 := by
  simp only [inWindow, intv]
  norm_num [halfPiLo, halfPiHi, piLo, piHi]

-- 负 k 分支
example : ¬ inWindow (intv (-5) (-9 / 2)) (-3) := by
  simp only [inWindow, intv]
  norm_num [halfPiLo, halfPiHi, piLo, piHi]

/-! ## T5 相位估计量路线：`phaseOf A := ⌊mid(A)/halfPiLo + 1/2⌋` 的守卫 -/

/-- 相位估计量（中点除以 `π/2` 的下界后四舍五入）。 -/
def phaseOf (A : RatInterval) : ℤ := ⌊(A.lo + A.hi) / 2 / halfPiLo + 1 / 2⌋

example : phaseOf (intv (1 / 4) (1 / 2)) = 0 := by
  simp only [phaseOf, intv]
  norm_num [halfPiLo, piLo]

example : phaseOf (intv (-5) (-9 / 2)) = -3 := by
  simp only [phaseOf, intv]
  norm_num [halfPiLo, piLo]

example : inWindow (intv (-5) (-9 / 2)) (phaseOf (intv (-5) (-9 / 2))) := by
  simp only [phaseOf, inWindow, intv]
  norm_num [halfPiLo, halfPiHi, piLo, piHi]

example : ¬ inWindow (intv (-5) (-9 / 2)) (phaseOf (intv (-5) (-9 / 2))) := by
  simp only [phaseOf, inWindow, intv]
  norm_num [halfPiLo, halfPiHi, piLo, piHi]

/-! ## T6 `reducedBox` 的端点求值 -/

example : (reducedBox (intv (-5) (-9 / 2)) (-3)).lo =
    (-5 : ℚ) - (-3 : ℤ) * halfPiHi := by
  simp only [reducedBox, intv]

example : (reducedBox (intv (-5) (-9 / 2)) (-3)).lo ≤
    ((-5 : ℚ) + 3 * halfPiHi) - 1 / 1000000000 := by
  simp only [reducedBox, intv]
  norm_num [halfPiLo, halfPiHi, piLo, piHi]

end RatInterval

end N11Formalization
