import N11Formalization.FlashTenBoundaryAnalytic

/-!
# C450 解析 consumer（第六层）：**两圆装配**（L1 用于真正的两个测试圆）

源文 §2 的容量不等式需要**两个**测试圆：
* 外圆 `∂D`（圆心 `0`、半径 `1`）——由十个环盘覆盖（前提）；
* 内圆 `S(h,R)`（圆心 `h = c hub`、半径 `R`）——整圈被十个环盘覆盖（由
  `circle_covered_by_others` 的 q↓R 闭集极限给出，**不需要**积分极限交换）。

本件把 L1（`circle_integral_le_sum_arc_integrals`）**分别**作用在这两个圆上并相加，得到
`2πa₀₀ + 2πa₁₀ ≤ Σ_i (外弧积分_i + 内弧积分_i)`，即源文的
`B = π(a₀₀+a₁₀) ≤ Σ_i Q_i`（`Q_i = ½(外弧积分_i + 内弧积分_i)`）。

**前提口径**：
* `hcovD`：单位闭盘被 `n` 个半径 `R` 的环盘 **或** hub 盘覆盖（= 源文十一盘覆盖 `D`）；
* `harcD`：单位**圆**被那 `n` 个环盘覆盖（= 源文"十个指定盘共同覆盖 `∂D`"）；
* `hR : 0 < R`、`hmargin : ‖h‖ + R < 1`（源文 `R = 19/50`、`‖h‖ ≤ 7/50` 给 `0.48 > 0`）。

**注意**：本件**不**用单位圆的界冒充 `q ≠ 1` 的内圆 —— 内圆直接用 L1 的圆版
（测试圆 = `h + R • angPt θ`），标度（`arc_scale`）只在下一步把每个 `Q_i` 认成证书数据时用。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-- **两圆装配**：L1 分别用于 `∂D` 与 `S(h,R)` 并相加。

结论的右端按盘分组（`Σ_i (外_i + 内_i)`），正是源文"每盘贡献相加"的形状。 -/
theorem two_circle_capacity (W0 W1 : TrigDensity) {n : ℕ} {c : Fin n → Point} {h : Point}
    {R : ℝ} (hR : 0 < R) (hmargin : ‖h‖ + R < 1)
    (hcovD : ∀ x : Point, ‖x‖ ≤ 1 → (∃ i : Fin n, dist x (c i) ≤ R) ∨ dist x h ≤ R)
    (harcD : ∀ θ : ℝ, ∃ i : Fin n, dist (angPt θ) (c i) ≤ R) :
    2 * Real.pi * W0.a0 + 2 * Real.pi * W1.a0
      ≤ ∑ i : Fin n,
          ((∫ θ in (0)..(2 * Real.pi),
              (if dist (angPt θ) (c i) ≤ R then W0.toFun θ else 0))
            + (∫ θ in (0)..(2 * Real.pi),
              (if dist (h + R • angPt θ) (c i) ≤ R then W1.toFun θ else 0))) := by
  -- 外圆：L1（γ = angPt）
  have h1 := circle_integral_le_sum_arc_integrals (γ := angPt) continuous_angPt
    W0.continuous_toFun W0.nonneg_toFun harcD
  -- 内圆：L1（γ = h + R • angPt）+ 排 hub 极限给覆盖
  have h2 := circle_integral_le_sum_arc_integrals
    (γ := fun θ : ℝ => h + R • angPt θ)
    (continuous_const.add (continuous_angPt.const_smul R))
    W1.continuous_toFun W1.nonneg_toFun (circle_covered_by_others hR hmargin hcovD)
  rw [W0.integral_toFun] at h1
  rw [W1.integral_toFun] at h2
  have hsum : (∑ i : Fin n, (∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) (c i) ≤ R then W0.toFun θ else 0)))
      + (∑ i : Fin n, (∫ θ in (0)..(2 * Real.pi),
        (if dist (h + R • angPt θ) (c i) ≤ R then W1.toFun θ else 0)))
      = ∑ i : Fin n,
          ((∫ θ in (0)..(2 * Real.pi),
              (if dist (angPt θ) (c i) ≤ R then W0.toFun θ else 0))
            + (∫ θ in (0)..(2 * Real.pi),
              (if dist (h + R • angPt θ) (c i) ≤ R then W1.toFun θ else 0))) :=
    Finset.sum_add_distrib.symm
  linarith [h1, h2, hsum]

/-- **真实的 capacity → 积分矛盾 consumer**（灌 36 段数据前的最小端到端件）：
两圆容量不等式（`two_circle_capacity`）+ **逐盘界**（证书数据的形状：
每盘"外弧积分 + 内弧积分" < 总需求/n）⇒ `False`。

这就是源文 §2–§4 的矛盾骨架：容量要求**总和不小于** `2B`，而逐盘界给出**总和严格小于** `2B`。
逐盘界的来源（下一步）：对每个环盘用 `arc_scale` 归约到单位圆、再用 clamp 闭式
`arc_integral_scale_clamp` 认成 `2Q_i`，而 `2Q_i < 2B/n` 正是 36 段证书数据给出的事。 -/
theorem c450_capacity_contradiction (W0 W1 : TrigDensity) {n : ℕ} (hn : 0 < n)
    {c : Fin n → Point} {h : Point} {R : ℝ} (hR : 0 < R) (hmargin : ‖h‖ + R < 1)
    (hcovD : ∀ x : Point, ‖x‖ ≤ 1 → (∃ i : Fin n, dist x (c i) ≤ R) ∨ dist x h ≤ R)
    (harcD : ∀ θ : ℝ, ∃ i : Fin n, dist (angPt θ) (c i) ≤ R)
    (hper : ∀ i : Fin n,
        (∫ θ in (0)..(2 * Real.pi),
            (if dist (angPt θ) (c i) ≤ R then W0.toFun θ else 0))
          + (∫ θ in (0)..(2 * Real.pi),
              (if dist (h + R • angPt θ) (c i) ≤ R then W1.toFun θ else 0))
        < (2 * Real.pi * W0.a0 + 2 * Real.pi * W1.a0) / n) :
    False := by
  have hcap := two_circle_capacity W0 W1 hR hmargin hcovD harcD
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have hlt : (∑ i : Fin n,
        ((∫ θ in (0)..(2 * Real.pi),
            (if dist (angPt θ) (c i) ≤ R then W0.toFun θ else 0))
          + (∫ θ in (0)..(2 * Real.pi),
              (if dist (h + R • angPt θ) (c i) ≤ R then W1.toFun θ else 0))))
      < ∑ _i : Fin n, (2 * Real.pi * W0.a0 + 2 * Real.pi * W1.a0) / n := by
    refine Finset.sum_lt_sum_of_nonempty hne ?_
    intro i _
    exact hper i
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hconst : (∑ _i : Fin n, (2 * Real.pi * W0.a0 + 2 * Real.pi * W1.a0) / n)
      = 2 * Real.pi * W0.a0 + 2 * Real.pi * W1.a0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ hn']
  linarith [hcap, hlt, hconst]

end

end N11Formalization
