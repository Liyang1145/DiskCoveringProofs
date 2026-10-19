import N11Formalization.IntervalsHighLag

/-!
# `arcsin(19/50)` 界的**独立控制件**（只算这个 q，不改任何阈值）

Lead 指定：先用**独立小文件**验证"算得动 + 方向对"，正控 / 负控都要。

* `q := 3897962964742606 / 10^16`（= 0.3897962964742606，数据盒上端）；
* **正控** `pos_control`：`19/50 < sinLoNLag q`（若成立 ⇒ `19/50 < Real.sin q`，再用
  `Real.arcsin_le_iff_le_sin` / `Real.strictMonoOn_sin` 反推 `arcsin(19/50) < q`）；
* **负控** `neg_control`：`q − 10^{-15}` 处**不该**成立（真余量只有 ≈3.37e-17），
  即 `¬ (19/50 < sinLoNLag (q − 10^{-15}))` 可证 —— 证明器械在真边界附近确实会翻面。

算术策略（按 Lead）：**纯有理比较优先 `by decide +kernel`**（不许 `native_decide`）；
若 `decide +kernel` 不可用，再退回 `norm_num [sinLoNLag, sinTQ, Finset.sum_range_succ]`
（项目 `Interval/ArcsinBracket.lean` 用的就是后者，能过 ⇒ 规模本身不爆炸，是展开方式问题）。
-/

namespace N11Formalization

set_option maxHeartbeats 4000000

/-- 数据盒上端（源用的有理数）。 -/
def qBox : ℚ := 3897962964742606 / 10 ^ 16

/-- 负控点：`qBox − 10^{-15}`。 -/
def qBoxNeg : ℚ := 3897962964742606 / 10 ^ 16 - 1 / 10 ^ 15

/-- **正控**：核在此 q 处给出 `> 19/50` 的 sin 下界。 -/
theorem pos_control : (19 : ℚ) / 50 < sinLoNLag qBox := by
  decide +kernel

/-- **负控**：把 q 往下挪 `10^{-15}`（超过真余量 ≈3.37e-17）后，同一核**不再**给出下界。 -/
theorem neg_control : ¬ ((19 : ℚ) / 50 < sinLoNLag qBoxNeg) := by
  decide +kernel

/-- 正控的实数读法（供上层直接接 `Real.arcsin_le_iff_le_sin`）。 -/
theorem pos_control_real :
    (19 : ℝ) / 50 < Real.sin ((qBox : ℚ) : ℝ) := by
  have h := sinLoNLag_le_sin qBox
  have h' : ((19 : ℚ) / 50 : ℝ) < ((sinLoNLag qBox : ℚ) : ℝ) := by
    exact_mod_cast pos_control
  linarith

end N11Formalization
