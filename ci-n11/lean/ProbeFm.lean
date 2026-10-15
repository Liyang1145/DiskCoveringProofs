import N11Formalization.Interval.Range

/-!
# fm-eval 探针：区间求值到显式有理数所需的自动化能力

目的：确定 `residualInterval cCert k` 的**读数**（端点为显式有理数的 kernel 等式）
用哪条自动化路线可行。每一条 `example` 是一个独立实验；失败的实验直接暴露能力边界。
本文件不是交付物（草稿探针），交付物是 `N11Formalization/ResidualInterval.lean`。
-/

namespace N11Formalization

namespace RatInterval

/-! ## T1 内核 `decide` 对 ℚ / ℤ / Nat.sqrt -/

-- 预期失败（DEAD B1）
example : ((-1 : ℚ) ≤ 3) := by decide

example : ((3 : ℤ) < 5) := by decide

example : Nat.sqrt 16 = 4 := by decide

example : ((-3 : ℤ) % 4 = 1) := by decide

/-! ## T2 `norm_num` / `simp` 对 `dite` 的解析（条件为具体有理不等式） -/

example : (if h : ((-1 : ℚ) ≤ -4) ∧ ((2 : ℚ) ≤ 1) then (5 : ℚ) else 7) = 7 := by norm_num

example : (if h : ((-1 : ℚ) ≤ -4) then (5 : ℚ) else 7) = 7 := by norm_num

example : (if ((-1 : ℚ) ≤ -4) then (5 : ℚ) else 7) = 7 := by norm_num

example : (if h : ((-1 : ℚ) ≤ 3) ∧ ((2 : ℚ) ≤ 1) then (5 : ℚ) else 7) = 7 := by norm_num

-- ℤ 条件（`if 0 ≤ k` 型）
example : (if (0 : ℤ) ≤ -3 then (5 : ℚ) else 7) = 7 := by norm_num

example : (if (0 : ℤ) ≤ 3 then (5 : ℚ) else 7) = 5 := by norm_num

/-! ## T3 `Int.floor` 的求值 -/

example : ⌊(-3 : ℚ) / 2 + 1 / 2⌋ = -1 := by norm_num

example : ⌊(7 : ℚ) / 2⌋ = 3 := by norm_num

/-! ## T4 具体区间上的 `inWindow`（在/不在窗口）判定 -/

example : inWindow (intv (1 / 4) (1 / 2)) 0 := by
  simp only [inWindow, intv]
  norm_num

example : ¬ inWindow (intv (1 / 4) (1 / 2)) 1 := by
  simp only [inWindow, intv]
  norm_num

example : ¬ inWindow (intv 3 4) 0 := by
  simp only [inWindow, intv]
  norm_num

-- 负 k（走 `if_neg` 分支）
example : inWindow (intv (-1 / 2) (-1 / 4)) 0 := by
  simp only [inWindow, intv]
  norm_num

example : ¬ inWindow (intv (-5) (-9 / 2)) (-3) := by
  simp only [inWindow, intv]
  norm_num

/-! ## T5 嵌套区间表达式的端点求值（`add`/`mul`/`sqrt` 链） -/

example : ((intv (1 / 4) (1 / 2)).add (intv (1 / 3) (1 / 3))).lo = 7 / 12 := by
  simp only [intv, RatInterval.add]
  norm_num

example : ((intv (1 / 4) (1 / 2)).mul (intv (1 / 3) (1 / 3))).hi = 1 / 6 := by
  simp only [intv, RatInterval.mul]
  norm_num

example : (((intv (1 / 2) (1 / 2)).mul (intv (1 / 2) (1 / 2))).sub
    (intv (1 / 4) (1 / 4))).lo = 1 / 4 - 1 / 4 := by
  simp only [intv, RatInterval.mul, RatInterval.sub]
  norm_num

-- `sqrt` on a concrete interval (Nat.sqrt 路线)
example : (sqrt (intv (1 / 4) (1 / 4))).hi = 3 / 4 := by
  simp only [sqrt, sqrtHi, sqrtLo, intv]
  norm_num

/-! ## T6 大数 / 高精度：证书盒量级的 ℚ 端点 -/

example : (sqrt (intv (6701511529285631 / 18014398509481984)
    (6701511529285631 / 18014398509481984))).hi =
  sqrtHi (6701511529285631 / 18014398509481984) := rfl

example : sqrtHi (6701511529285631 / 18014398509481984) ≤
    sqrtLo (6701511529285631 / 18014398509481984) + 1 / 1000000000000 := by
  simp only [sqrtHi, sqrtLo]
  norm_num

/-! ## T7 `sinI` / `cosI` 在具体区间上的端点（窗口支） -/

example : (sinI (intv (1 / 4) (1 / 4))).hi = sinHi (1 / 4) := by
  have h : -1 ≤ (intv (1 / 4) (1 / 4)).lo ∧ (intv (1 / 4) (1 / 4)).hi ≤ 1 := by
    simp only [intv]; norm_num
  simp only [sinI, dif_pos h, intv]

example : (cosI (intv (1 / 4) (1 / 4))).hi = 1 := by
  have h : -1 ≤ (intv (1 / 4) (1 / 4)).lo ∧ (intv (1 / 4) (1 / 4)).hi ≤ 1 := by
    simp only [intv]; norm_num
  simp only [cosI, dif_pos h, cosHi, cosHi_zero, intv]
  norm_num

end RatInterval

end N11Formalization
