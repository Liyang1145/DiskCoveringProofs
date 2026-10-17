/-
  N11Formalization.Interval.Taylor19B
  ===================================

  **第 4 步（kernel 负对照）** —— 已完成并 kernel-proved。

  （本文件**不修改** `Trig.lean` 的任何现有名字/语义——只**引用** `sinLo/sinHi/cosLo/cosHi`，
  以满足下游 `ResidualInterval.lean` 的依赖稳定要求。）

  **kernel 负对照**：用现有低阶界 `sinHi q = q − q³/6 + |q|⁵/100`、
  `sinLo q = q − q³/6 − |q|⁵/100`（差 = `2|q|⁵/100`），在 `q = 3843/10000` 处**内核证明**
  `9.956e-10 < sinHi q − sinLo q` ⟹ 旧阶（`N = 3`）的界**确实不够**，
  把 C1003 的 numeric 读数升级为内核事实。`cos` 侧同款（差 = `|q|⁴·(5/48)`，精确读数已证）。

  **未交付（尝试过但未成功，卡点如实记录）**：`inWindow` 的有限候选集界
  `inWindow A k ⟹ |k| ≤ (|A.lo| + |A.hi| + 2)/halfPiLo`。数学内容简单（由 `inWindow` 的两条不等式
  直接解出 `k` 的两侧界，再除以 `halfPiLo > 0`），但形式化时卡在
  `div_le_div_of_nonneg_left` 的**实参顺序/形式**上（它要求 `?m.227 ≤ ?m.226` 形式，
  与我需要把 `(A.lo+1)/halfPiHi` 与 `(|A.lo|+1)/halfPiLo` 比较的形状不一致），
  失败读数见 `evidence/interval/lakebuild-taylor19b-1.txt`（第 79、82、111、115、117 行）。
  正确写法应是先把两侧界都化成「分母统一为 `halfPiLo`」的形状再 `linarith`，
  或改用 `one_div_le_one_div_of_le` 处理 `1/halfPiHi ≤ 1/halfPiLo` —— 下一轮用这个改法。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Trig

namespace N11Formalization

namespace RatInterval

/-! ## 1. kernel 负对照：现有 `N = 3` 阶在证书角值上不够 -/

/-- 阈值 `9.956e-10` 的精确有理表示（`9956/10^13`）。 -/
def etaThreshold : ℚ := 9956 / 10 ^ 13

/-- **kernel 负对照（`sin`）**：在 `q = 3843/10000` 处，现有 `sinHi − sinLo` **超过**阈值
（即按现有阶无法把 `Fm` 包到 `η` 以内）。 -/
theorem sinLo_sinHi_gap_gt_eta_at_3843 :
    etaThreshold < sinHi (3843 / 10000) - sinLo (3843 / 10000) := by
  rw [sinHi, sinLo, etaThreshold]
  norm_num

/-- **kernel 负对照（`cos`）**：同款读数。 -/
theorem cosLo_cosHi_gap_gt_eta_at_3843 :
    etaThreshold < cosHi (3843 / 10000) - cosLo (3843 / 10000) := by
  rw [cosHi, cosLo, etaThreshold]
  norm_num

/-- 负对照的**精确读数**（供报告引用）：差值 = `2·|q|⁵/100`。 -/
theorem sinHi_sub_sinLo (q : ℚ) : sinHi q - sinLo q = |q| ^ 5 / 50 := by
  rw [sinHi, sinLo]
  ring

/-- `cos` 侧精确读数：差值 = `|q|⁴·(5/48)`。 -/
theorem cosHi_sub_cosLo (q : ℚ) : cosHi q - cosLo q = |q| ^ 4 * (5 / 48) := by
  rw [cosHi, cosLo]
  ring

/-- 负对照的**倍数读数**（内核）：`(sinHi − sinLo)/阈值` = `|q|⁵·10^13/(50·9956)`
——在 `q = 3843/10000` 处给出「超阈值多少倍」的有理数。 -/
theorem sinHi_sinLo_gap_ratio_at_3843 :
    (sinHi (3843 / 10000) - sinLo (3843 / 10000)) / etaThreshold
      = (3843 / 10000 : ℚ) ^ 5 * 10 ^ 13 / (50 * 9956) := by
  rw [sinHi, sinLo, etaThreshold]
  norm_num

end RatInterval

end N11Formalization
