import N11Formalization.FlashTenBoundarySinCtl

/-!
# `arcsin(19/50) ≤ 0.3897962964742606`（**不留作前提**）

路线 = Lead 指定的那条，但复用**已绿的区间核**，不复制：

1. `FlashTenBoundarySinCtl.pos_control`（`by decide +kernel`，纯有理）：
   `19/50 < sinLoNLag qBox`，其中 `qBox = 3897962964742606/10^16`；
   经 `sinLoNLag_le_sin` 得实数形 `pos_control_real : 19/50 < Real.sin qBox`；
   **负控** `neg_control`：把 q 降到 `qBox − 10^{-15}`（超过真余量 ≈3.37e-17）后下界不成立
   ⇒ 器械在真边界附近确实翻面（不是盲目通过）。
2. `Real.arcsin_le_iff_le_sin`（项目 `Interval/ArcsinBracket.lean` 同款用法）：
   `arcsin s ≤ y ↔ s ≤ sin y`（`s ∈ [-1,1]`、`y ∈ [-π/2,π/2]`），取 `s = 19/50`、`y = qBox`。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

section

theorem arcsin_R_le_bound : Real.arcsin (19 / 50) ≤ (0.3897962964742606 : ℝ) := by
  have hq : ((qBox : ℚ) : ℝ) = (0.3897962964742606 : ℝ) := by norm_num [qBox]
  have hsR : (19 / 50 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hqmem : ((qBox : ℚ) : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have hq0 : (0 : ℝ) ≤ ((qBox : ℚ) : ℝ) := by norm_num [qBox]
    have hq2 : ((qBox : ℚ) : ℝ) < 2 := by norm_num [qBox]
    exact ⟨by linarith [Real.pi_pos, hq0], by linarith [Real.pi_gt_three]⟩
  have hmain : Real.arcsin (19 / 50) ≤ ((qBox : ℚ) : ℝ) :=
    (Real.arcsin_le_iff_le_sin hsR hqmem).mpr (le_of_lt pos_control_real)
  rwa [hq] at hmain

end

end N11Formalization
