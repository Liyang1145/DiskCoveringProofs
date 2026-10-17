/-
n11-formalization —— **G2 的统一形式**：把覆盖结论挂到「残差为零的 `u`」这个对象上

写域：本文件 + `evidence/g2-unify/`（不触碰其它成员文件）。

## 0. 目标对象（逐条读源码 + `#check` 确认，非凭印象）

* `Point := EuclideanSpace ℝ (Fin 2)`（`Definitions.lean`），`unitDisk = {x | ‖x‖ ≤ 1}`；
* `Covers (c : Fin 11 → Point) (r : ℝ) : Prop := ∀ x, x ∈ unitDisk → ∃ i, dist x (c i) ≤ r`；
* `centersOfRoot u : Fin 11 → Point`：`0..8` = `ringCenter u k`，`9` = `hub0 u = (u 4, 0)`，
  `10` = `hub1 u = (u 5, 0)`（`TCSystem.lean`）；
* **半径的来源**：源文的 `R` 就是 **`u 6`**（几何只读 `u` 的前 7 槽）；`uCert` 处 `uCert 6 = ↑qR`。
  `ArcCover.covers_cert_of_outer` 挂的是固定常数 `uCert`/`↑qR`，本文件换成 `u`/`u 6`；
* `residual u : Fin 5 → ℝ = ![|U_1−H1|−u6, |U_2−H0|−u6, |U_3−H0|−u6, |U_8−H1|−u6, |W−C_6|−u6]`
  （`TCSystem.lean`）；`TCSystem u` 的前 5 个分量就是 `residual u`（`TCSystem_first`）。

本文件把统一目标写成

```
G2Unified : ∀ u, RootRange u → residual u = 0 → u 5 ≤ 0 → 0 ≤ u 6 + u 5 →
            Covers (centersOfRoot u) (u 6)
```

并给出**归约**：`G2Unified` 由具名义务 `G2RemainingObligation`（`rIn ≤ ‖x‖ < 1` 且非负 x 轴点）承担，
内球 / 圆周 / pinch 段三类配置在本文件**无条件或精确**闭合。

## 1. 本文件证成的部分（kernel-proved；零 `sorry`、零自定义 `axiom`、零 `native_decide`）

| # | 内容 | 等级 |
|---|---|---|
| A | **一般弧链**（任意 `u`）：`arcLo₀ = −π`、`arcHi₈ = π`、`arcHi_k = arcLo_{k+1}`、`arcLo_k ≤ arcHi_k`，故 `[−π,π]` 被九个弧覆盖 | proved |
| B | **一般圆周层**（任意 `u`，仅需 `RootRange`）：`S¹` 被 9 个环盘覆盖 —— `ArcCover.circle_covered`（固定 `uCert` + 显式有理角）的推广，**不含任何数值余量** | proved |
| C | **一般共点（紧性）**：`dist (Uvec u k) (ringCenter u k) = u 6`、`dist (Uvec u k) (ringCenter u (k+1)) = u 6`（任意 `u`）——即 `U_k` 是两环盘边界的第二交点 | proved |
| D | **统一形式归约**：内球（`hub1_covers_ball`，无条件）+ 圆周（B）+ pinch 段（`neg_axis_covered_of_residual`，用 `residual u 3 = 0`）⟹ `G2Unified`，唯一剩余义务 = `G2RemainingObligation` | proved（归约） |
| E | **负对照（有判别力）**：9 个环盘在半径 `↑qR` 下**不覆盖原点**（`ρ_k ≥ 1/2 > qR`），而 11 盘覆盖原点（`covers_inner_lower 0`） | proved |

## 2. 本文件**未**证成的部分（如实标注；读数见 `evidence/g2-unify/RAY-STRUCTURE.md`）

`G2RemainingObligation`（`rIn ≤ ‖x‖ < 1` 且 `x` 不在负 x 轴上）。它**不是**「正余量」问题：
`residual u = 0` 时覆盖在 **8 个内点**精确紧（`U_1,U_2,U_3,U_4,U_5,U_6,U_8` 与 `W`：三个盘同时过该点，
余量恰 0），其中只有 `U_8` 所在的负 x 轴射线被本文件用 `residual 3 = 0` 精确闭合。
其余 4 条紧射线（`U_1/U_6`、`U_2/U_5`、`U_3/U_4`、`W`）需要同一技术，但还缺一个**角度条件**
（紧点方向的单位点落在相邻环盘的弧内），见 §7 注释。
-/

import Mathlib
import N11Formalization.Definitions
import N11Formalization.TCSystem
import N11Formalization.Geometry.CapArc
import N11Formalization.Geometry.ArcCovering
import N11Formalization.Geometry.InnerRoot
import N11Formalization.Assembly.ArcCover

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace N11Formalization

/-! ## §1 统一目标的精确陈述（定义层） -/

/-- 内区半径：`hub1` 盘所覆盖的球半径 `r_in = u 6 − |u 5|`（**无条件**可得，见 `hub1_covers_ball`）。 -/
def innerRadius (u : Fin 12 → ℝ) : ℝ := u 6 - |u 5|

/-- **根的范围条件**（与 `residual u = 0` 无关的几何前提；本文件只在圆周层与共点引理用到）。 -/
structure RootRange (u : Fin 12 → ℝ) : Prop where
  /-- 半径非负。 -/
  hR : 0 ≤ u 6
  /-- 九个角非负。 -/
  ha : ∀ k : Fin 9, 0 ≤ angleVec u k
  /-- 九个角 `≤ π`。 -/
  hapi : ∀ k : Fin 9, angleVec u k ≤ Real.pi
  /-- 径向根有定义：`sin²a_k ≤ R²`。 -/
  hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2
  /-- 环盘中心与原点同侧（`ρ_k ≥ 0`）。 -/
  hrho : ∀ k : Fin 9, 0 ≤ rhoK u k

/-- 负 x 轴段上的点（`0 ≤ r ≤ 1`；含 pinch 点 `U_8 = (−(ρ_0²−R²), 0)`）。 -/
def NegAxisPoint (x : Point) : Prop := ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ x = (!₂[(-r), 0] : Point)

/-- **G2 的统一形式（全称版目标命题）**。 -/
def G2Unified : Prop :=
  ∀ u : Fin 12 → ℝ, RootRange u → residual u = 0 → u 5 ≤ 0 → 0 ≤ u 6 + u 5 →
    Covers (centersOfRoot u) (u 6)

/-- **收口后的唯一剩余义务（具名）**：`rIn ≤ ‖x‖ < 1` 且 `x` 不在负 x 轴时，覆盖仍成立。

被排除的三类配置（本文件均已证）：
* `‖x‖ ≤ rIn`：内球 —— `hub1_covers_ball`（**无条件**，任意 `u`）；
* `‖x‖ = 1`：圆周层 —— `circle_covered_of_range`（一般 `u`，仅需 `RootRange`，无余量损失）；
* `x ∈ 负 x 轴`：pinch 段 —— `neg_axis_covered_of_residual`（用 `residual u 3 = 0`，**精确**）。 -/
def G2RemainingObligation : Prop :=
  ∀ u : Fin 12 → ℝ, RootRange u → residual u = 0 → u 5 ≤ 0 → 0 ≤ u 6 + u 5 →
    ∀ x : Point, ¬ NegAxisPoint x → innerRadius u ≤ ‖x‖ → ‖x‖ < 1 →
      ∃ i : Fin 11, dist x (centersOfRoot u i) ≤ u 6

/-! ## §2 一般弧链：九个弧无缝隙（任意 `u`，纯代数）

与 `ArcCover.arc_chain_cover`（固定 `uCert`、显式有理端点、九次二分）不同，这里对**任意 `u`**
只用：`θ_0 − a_0 = −π`、`θ_8 + a_8 = π`、弧首尾相接 `θ_{k+1} − a_{k+1} = θ_k + a_k`，
以及 `a_k ≥ 0`（弧非退化）。全部是 `thetaOf`/`angleVec` 显式向量上的 `ring` 恒等式。 -/

/-- 弧的右端点 `θ_k + a_k`。 -/
def arcHiG (u : Fin 12 → ℝ) (k : Fin 9) : ℝ := thetaOf (angleVec u) k + angleVec u k

/-- 弧的左端点 `θ_k − a_k`。 -/
def arcLoG (u : Fin 12 → ℝ) (k : Fin 9) : ℝ := thetaOf (angleVec u) k - angleVec u k

/-- `θ_0 − a_0 = −π`（`a_4 = π − 2(a_0+a_1+a_2+a_3)` 的直接推论，**任意 `u`**）。 -/
theorem arcLoG_zero (u : Fin 12 → ℝ) : arcLoG u 0 = -Real.pi := by
  rw [arcLoG, thetaOf_zero]
  ring

/-- `θ_8 + a_8 = π`（回文 `a_8 = a_0` 与 `thetaOf_eight`，**任意 `u`**）。 -/
theorem arcHiG_eight (u : Fin 12 → ℝ) : arcHiG u 8 = Real.pi := by
  rw [arcHiG, thetaOf_eight, angleVec_eight_eq_zero]
  ring

/-- **弧首尾相接**（`k < 8`；后继写作 `⟨k+1, _⟩`）：`θ_{k+1} − a_{k+1} = θ_k + a_k`。 -/
theorem arcLoG_succ_eq_arcHiG (u : Fin 12 → ℝ) (k : Fin 8) :
    arcLoG u ⟨(k : ℕ) + 1, by omega⟩ = arcHiG u ⟨(k : ℕ), by omega⟩ := by
  have h := thetaOf_rec (angleVec u) k
  simp only [arcLoG, arcHiG]
  linarith

/-- **弧首尾相接（`Fin 8` 形式的另一侧）**：`θ_k + a_k = θ_{k+1} − a_{k+1}`。 -/
theorem arcHiG_eq_arcLoG_add_one (u : Fin 12 → ℝ) (k : Fin 8) :
    arcHiG u ⟨(k : ℕ), by omega⟩ = arcLoG u ⟨(k : ℕ) + 1, by omega⟩ :=
  (arcLoG_succ_eq_arcHiG u k).symm

/-- **弧首尾相接（环状形式，任意 `k`）**：`θ_{k+1} − a_{k+1} = θ_k + a_k`，`k = 8` 时差 `2π`。 -/
theorem arcLoG_succ_eq_arcHiG_or_sub (u : Fin 12 → ℝ) (k : Fin 9) :
    thetaOf (angleVec u) (k + 1) - angleVec u (k + 1) = thetaOf (angleVec u) k + angleVec u k ∨
      thetaOf (angleVec u) (k + 1) - angleVec u (k + 1)
        = thetaOf (angleVec u) k + angleVec u k - 2 * Real.pi := by
  by_cases hk : (k : ℕ) + 1 < 9
  · left
    have h1 : (k + 1 : Fin 9) = (⟨(k : ℕ) + 1, hk⟩ : Fin 9) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt hk]
    have h' : arcHiG u k = arcLoG u (⟨(k : ℕ) + 1, hk⟩ : Fin 9) := by
      have h := arcHiG_eq_arcLoG_add_one u ⟨(k : ℕ), by omega⟩
      simpa using h
    rw [h1]
    exact h'.symm
  · right
    have hk8 : k = 8 := by apply Fin.ext; omega
    rw [hk8, fin_eight_add_one, thetaOf_zero, thetaOf_eight, angleVec_eight_eq_zero]
    ring

/-- 单个弧非退化（`0 ≤ a_k` ⟹ 左端点 ≤ 右端点）。 -/
theorem arcLoG_le_arcHiG (u : Fin 12 → ℝ) (ha : ∀ k : Fin 9, 0 ≤ angleVec u k) (k : Fin 9) :
    arcLoG u k ≤ arcHiG u k := by
  simp only [arcLoG, arcHiG]
  linarith [ha k]

/-- **一般弧链覆盖（任意 `u`）**：`φ ∈ [−π,π]` 落在某个弧 `[θ_k−a_k, θ_k+a_k]` 内。

（九次二分；每一档的「首尾相接」用**具体指标**的局部 `ring` 计算，避免指标证明项不匹配。） -/
theorem arc_chain_cover_general (u : Fin 12 → ℝ) (ha : ∀ k : Fin 9, 0 ≤ angleVec u k)
    {φ : ℝ} (hlo : -Real.pi ≤ φ) (hhi : φ ≤ Real.pi) :
    ∃ k : Fin 9, arcLoG u k ≤ φ ∧ φ ≤ arcHiG u k := by
  by_cases h0 : φ ≤ arcHiG u 0
  · exact ⟨0, by rw [arcLoG_zero]; exact hlo, h0⟩
  · rw [not_le] at h0
    by_cases h1 : φ ≤ arcHiG u 1
    · refine ⟨1, ?_, h1⟩
      have e : arcHiG u 0 = arcLoG u 1 := by
        have h := arcHiG_eq_arcLoG_add_one u (0 : Fin 8)
        simpa using h
      linarith
    · rw [not_le] at h1
      by_cases h2 : φ ≤ arcHiG u 2
      · refine ⟨2, ?_, h2⟩
        have e : arcHiG u 1 = arcLoG u 2 := by
          have h := arcHiG_eq_arcLoG_add_one u (1 : Fin 8)
          simpa using h
        linarith
      · rw [not_le] at h2
        by_cases h3 : φ ≤ arcHiG u 3
        · refine ⟨3, ?_, h3⟩
          have e : arcHiG u 2 = arcLoG u 3 := by
            have h := arcHiG_eq_arcLoG_add_one u (2 : Fin 8)
            simpa using h
          linarith
        · rw [not_le] at h3
          by_cases h4 : φ ≤ arcHiG u 4
          · refine ⟨4, ?_, h4⟩
            have e : arcHiG u 3 = arcLoG u 4 := by
              have h := arcHiG_eq_arcLoG_add_one u (3 : Fin 8)
              simpa using h
            linarith
          · rw [not_le] at h4
            by_cases h5 : φ ≤ arcHiG u 5
            · refine ⟨5, ?_, h5⟩
              have e : arcHiG u 4 = arcLoG u 5 := by
                have h := arcHiG_eq_arcLoG_add_one u (4 : Fin 8)
                simpa using h
              linarith
            · rw [not_le] at h5
              by_cases h6 : φ ≤ arcHiG u 6
              · refine ⟨6, ?_, h6⟩
                have e : arcHiG u 5 = arcLoG u 6 := by
                  have h := arcHiG_eq_arcLoG_add_one u (5 : Fin 8)
                  simpa using h
                linarith
              · rw [not_le] at h6
                by_cases h7 : φ ≤ arcHiG u 7
                · refine ⟨7, ?_, h7⟩
                  have e : arcHiG u 6 = arcLoG u 7 := by
                    have h := arcHiG_eq_arcLoG_add_one u (6 : Fin 8)
                    simpa using h
                  linarith
                · rw [not_le] at h7
                  refine ⟨8, ?_, by rw [arcHiG_eight]; exact hhi⟩
                  have e : arcHiG u 7 = arcLoG u 8 := by
                    have h := arcHiG_eq_arcLoG_add_one u (7 : Fin 8)
                    simpa using h
                  linarith

/-! ## §3 一般圆周层（任意 `u`；`ArcCover.circle_covered` 的推广） -/

/-- **一般圆周层**：`RootRange u` ⟹ 单位圆周每点被 9 个环盘（半径 `u 6`）覆盖。

与固定数据的 `ArcCover.circle_covered` 不同：这里只用一般弧链（§2）与已是一般形式的
`dist_le_radius_of_inner`，弧端点处 `cos a_k ≤ cos a_k` 取等号，**不含任何数值余量**。 -/
theorem circle_covered_of_range (u : Fin 12 → ℝ) (H : RootRange u) (x : Point)
    (hx : ‖x‖ = 1) : ∃ k : Fin 9, dist x (ringCenter u k) ≤ u 6 := by
  have hmem := circleAngle_mem_Ioc x
  obtain ⟨k, hklo, hkhi⟩ := arc_chain_cover_general u H.ha (le_of_lt hmem.1) hmem.2
  refine ⟨k, dist_le_radius_of_inner u k x hx (H.hsin k) H.hR (H.hrho k) ?_⟩
  rw [← circleMap_circleAngle x hx, inner_circleMap]
  have habs : |circleAngle x - thetaOf (angleVec u) k| ≤ angleVec u k := by
    rw [abs_le]
    constructor
    · simp only [arcLoG] at hklo; linarith
    · simp only [arcHiG] at hkhi; linarith
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (H.hapi k) habs
  rwa [Real.cos_abs] at h

/-! ## §4 一般共点（紧性）：`U_k` 到相邻两个环盘中心的距离恰为 `u 6`

`U_k = C_k + C_{k+1} − B_k` 是 `∂B(C_k,R)` 与 `∂B(C_{k+1},R)` 的**第二个交点**
（第一个是弧交接点 `B_k ∈ S¹`）。这正是残差各分量在紧点处取到 `u 6` 的几何原因。 -/

/-- `B_k` 的圆参数等于下一个弧的左端点（下标按模 9；`k = 8` 处用 `circleMap` 的 `2π` 周期性）。 -/
theorem arcEnd_eq_circleMap_arcLo_succ (u : Fin 12 → ℝ) (k : Fin 9) :
    arcEnd u k = circleMap (thetaOf (angleVec u) (k + 1) - angleVec u (k + 1)) := by
  rw [arcEnd_eq_circleMap]
  by_cases hk : (k : ℕ) + 1 < 9
  · have h1 : (k + 1 : Fin 9) = (⟨(k : ℕ) + 1, hk⟩ : Fin 9) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt hk]
    have h' : arcHiG u k = arcLoG u (⟨(k : ℕ) + 1, hk⟩ : Fin 9) := by
      have h := arcHiG_eq_arcLoG_add_one u ⟨(k : ℕ), by omega⟩
      simpa using h
    rw [h1]
    show circleMap (arcHiG u k) = circleMap (arcLoG u (⟨(k : ℕ) + 1, hk⟩ : Fin 9))
    rw [h']
  · have hk8 : k = 8 := by apply Fin.ext; omega
    rw [hk8, fin_eight_add_one, thetaOf_eight, angleVec_eight_eq_zero,
      show thetaOf (angleVec u) 0 - angleVec u 0 = -Real.pi from by rw [thetaOf_zero]; ring,
      show Real.pi - angleVec u 0 + angleVec u 0 = Real.pi from by ring,
      circleMap_pi, circleMap_neg_pi]

/-- **弧交接处到下一个环盘的球心距离恰为 `u 6`**（一般 `u`，含 `k = 8` 的环状情形）。 -/
theorem dist_arcEnd_ringCenter_succ (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (k : Fin 9) : dist (arcEnd u k) (ringCenter u (k + 1)) = u 6 := by
  rw [arcEnd_eq_circleMap_arcLo_succ u k]
  exact dist_arcLo_ringCenter u (k + 1) (hsin (k + 1)) hR

/-- **共点引理（自身侧）**：`dist (Uvec u k) (ringCenter u k) = u 6`（一般 `u`；`U_k` 在两环盘边界上）。 -/
theorem dist_Uvec_ringCenter_self (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (k : Fin 9) : dist (Uvec u k) (ringCenter u k) = u 6 := by
  have h : Uvec u k - ringCenter u k = ringCenter u (k + 1) - arcEnd u k := by
    simp only [Uvec]
    abel
  rw [dist_eq_norm, h, ← dist_eq_norm, dist_comm]
  exact dist_arcEnd_ringCenter_succ u hsin hR k

/-- **共点引理（后继侧）**：`dist (Uvec u k) (ringCenter u (k+1)) = u 6`（一般 `u`）。 -/
theorem dist_Uvec_ringCenter_succ (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6)
    (k : Fin 9) : dist (Uvec u k) (ringCenter u (k + 1)) = u 6 := by
  have h : Uvec u k - ringCenter u (k + 1) = ringCenter u k - arcEnd u k := by
    simp only [Uvec]
    abel
  rw [dist_eq_norm, h, ← dist_eq_norm, dist_comm]
  exact dist_arcEnd_ringCenter u k (hsin k) hR

/-! ## §5 装配：把已有件接到统一目标上 -/

/-- **pinch 段（负 x 轴）的 `∃` 形式**（一般 `u`；由 `residual u 3 = 0` 精确闭合）。 -/
theorem neg_axis_covered_all_of_residual (u : Fin 12 → ℝ)
    (hs : Real.sin (angleVec u 0) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) (hy1 : u 5 ≤ 0)
    (hRy : 0 ≤ u 6 + u 5) (h3 : residual u 3 = 0) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ i : Fin 11, dist (!₂[(-r), 0] : Point) (centersOfRoot u i) ≤ u 6 := by
  rcases neg_axis_covered_of_residual u hs hR hy1 hRy h3 hr0 hr1 with h | h
  · exact ⟨10, by rw [centersOfRoot_ten]; exact h⟩
  · exact ⟨⟨8, by omega⟩, by simpa [centersOfRoot] using h⟩

/-- **统一形式的归约（主定理）**：唯一剩余义务 `G2RemainingObligation` ⟹ `G2Unified`。

三类配置在此**不再需要任何新输入**：内球（无条件）、圆周（§3，一般 `u`）、
负 x 轴 pinch 段（`neg_axis_covered_all_of_residual`，用 `residual u 3 = 0`）。 -/
theorem covers_of_remaining_obligation (hrem : G2RemainingObligation) : G2Unified := by
  intro u H hres hy1 hRy x hx
  by_cases h1 : ‖x‖ ≤ innerRadius u
  · exact ⟨10, by rw [centersOfRoot_ten]; exact hub1_covers_ball u h1⟩
  · have h2 : innerRadius u ≤ ‖x‖ := le_of_lt (not_le.mp h1)
    have hx1 : ‖x‖ ≤ 1 := mem_unitDisk.mp hx
    by_cases h3 : ‖x‖ = 1
    · obtain ⟨k, hk⟩ := circle_covered_of_range u H x h3
      exact ⟨⟨(k : ℕ), by omega⟩, by rwa [centersOfRoot_ring]⟩
    · have h4 : ‖x‖ < 1 := lt_of_le_of_ne hx1 h3
      by_cases hp : NegAxisPoint x
      · obtain ⟨r, hr0, hr1, rfl⟩ := hp
        exact neg_axis_covered_all_of_residual u (H.hsin 0) H.hR hy1 hRy
          (by simp [hres]) hr0 hr1
      · exact hrem u H hres hy1 hRy x hp h2 h4

/-! ## §6 负对照（有判别力，kernel-proved）

`Covers` 的否定需要**下界**：对**原点**这类点，11 个中心到它的距离有闭式（环盘 = `ρ_k`，
hub = `|y|`），可精确/有理控制 —— 这是本工程唯一能做无余量核验的负对照位置。
「9 个环盘不覆盖原点（半径 `↑qR`）」与「11 盘覆盖原点（`covers_inner_lower`）」构成
**同一半径、同一对象**的判别对，说明两个 hub 盘在 `qR` 处是**承重**的。 -/

/-- 具体数据：每个证书角 `≤ 2/5`（`a_4 = π − 2S` 处用 `π` 的 6 位小数夹）。 -/
theorem angleVec_uCert_le_two_fifths (k : Fin 9) : angleVec uCert k ≤ (2 : ℝ) / 5 := by
  rw [angleVec_uCert_eq]
  fin_cases k <;>
    · norm_num [qA0, qA1, qA2, qA3, qS] <;>
      linarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos]

/-- 具体数据：每个环盘中心到原点的距离 `ρ_k ≥ 1/2`。 -/
theorem rhoK_cert_ge_half (k : Fin 9) : (1 : ℝ) / 2 ≤ rhoK uCert k := by
  have ha0 : 0 ≤ angleVec uCert k := (angleVec_uCert_mem01 k).1
  have ha : angleVec uCert k ≤ (2 : ℝ) / 5 := angleVec_uCert_le_two_fifths k
  have hsq : angleVec uCert k ^ 2 ≤ ((2 : ℝ) / 5) ^ 2 := by nlinarith
  have hcos : (23 : ℝ) / 25 ≤ Real.cos (angleVec uCert k) := by
    have := Real.one_sub_sq_div_two_le_cos (x := angleVec uCert k)
    nlinarith
  have hsqrt : Real.sqrt ((uCert 6) ^ 2 - Real.sin (angleVec uCert k) ^ 2) ≤ (qR : ℝ) := by
    calc Real.sqrt ((uCert 6) ^ 2 - Real.sin (angleVec uCert k) ^ 2)
        ≤ Real.sqrt ((uCert 6) ^ 2) :=
          Real.sqrt_le_sqrt (sub_le_self _ (sq_nonneg _))
      _ = uCert 6 := Real.sqrt_sq (by rw [uCert_six]; exact_mod_cast qR_pos.le)
      _ = (qR : ℝ) := uCert_six
  have hqR_le : (qR : ℝ) ≤ (21 : ℝ) / 50 := by norm_num [qR]
  rw [rhoK]
  linarith

/-- **负对照（判别性，kernel-proved）**：9 个环盘在半径 `↑qR` 下**不覆盖原点**。

对照正面事实：11 盘在**同一半径**下覆盖原点（`covers_inner_lower 0`，无条件）。
即：`hub0`/`hub1` 盘在 `qR` 处对内区是**承重**的，不能删。 -/
theorem ringOnly_not_covers_origin_at_qR :
    ¬ ∃ k : Fin 9, dist (0 : Point) (ringCenter uCert k) ≤ (qR : ℝ) := by
  rintro ⟨k, hk⟩
  have hnorm : dist (0 : Point) (ringCenter uCert k) = rhoK uCert k := by
    rw [dist_eq_norm, zero_sub, norm_neg, ringCenter_eq_smul, norm_smul, circleMap_norm, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (rhoK_nonneg_cert k)]
  rw [hnorm] at hk
  have hqR_lt : (qR : ℝ) < (1 : ℝ) / 2 := by norm_num [qR]
  linarith [rhoK_cert_ge_half k]

/-- 正面对照（同一半径、同一对象）：11 盘覆盖原点。 -/
theorem eleven_covers_origin_at_qR :
    ∃ i : Fin 11, dist (0 : Point) (centersOfRoot uCert i) ≤ (qR : ℝ) :=
  covers_inner_lower 0 (by norm_num [rIn])

/-- 具体数据：原点到**每个**中心的距离都 `> 1/7`（环盘 `ρ_k ≥ 1/2`；hub 距 `|qY0|,|qY1|`）。 -/
theorem dist_zero_centers_gt_seventh (i : Fin 11) :
    (1 : ℝ) / 7 < dist (0 : Point) (centersOfRoot uCert i) := by
  have hqY0 : hub0 uCert = (qY0 : ℝ) • (!₂[(1 : ℝ), 0] : Point) := by
    rw [hub0, uCert_four, smul_cons_zero, mul_one]
  have hqY1 : hub1 uCert = (qY1 : ℝ) • (!₂[(1 : ℝ), 0] : Point) := by
    rw [hub1, uCert_five, smul_cons_zero, mul_one]
  by_cases h9 : (i : ℕ) = 9
  · have hi : i = 9 := Fin.ext h9
    subst hi
    rw [centersOfRoot_nine, hqY0, dist_eq_norm, zero_sub, norm_neg, norm_smul, cons_norm_eq_abs,
      Real.norm_eq_abs, abs_one, mul_one]
    rw [abs_of_pos (by exact_mod_cast qY0_pos : (0 : ℝ) < (qY0 : ℝ))]
    norm_num [qY0]
  · by_cases h10 : (i : ℕ) = 10
    · have hi : i = 10 := Fin.ext h10
      subst hi
      rw [centersOfRoot_ten, hqY1, dist_eq_norm, zero_sub, norm_neg, norm_smul, cons_norm_eq_abs,
        Real.norm_eq_abs, abs_one, mul_one]
      have hneg : (qY1 : ℝ) < 0 := by exact_mod_cast qY1_neg
      rw [abs_of_neg hneg]
      norm_num [qY1]
    · have hi9 : (i : ℕ) < 9 := by
        have := i.isLt; omega
      have hci : centersOfRoot uCert i = ringCenter uCert ⟨(i : ℕ), hi9⟩ := by
        simp only [centersOfRoot, dif_pos hi9]
      rw [hci, dist_eq_norm, zero_sub, norm_neg, ringCenter_eq_smul, norm_smul, circleMap_norm,
        mul_one, Real.norm_eq_abs, abs_of_nonneg (rhoK_nonneg_cert _)]
      linarith [rhoK_cert_ge_half ⟨(i : ℕ), hi9⟩]

/-- **负对照 2（有判别力，kernel-proved）**：半径取 `1/7` 时，**整个 11 盘族**都不覆盖原点
（原点最近的盘是 `hub1`，距离 `|qY1| ≈ 0.14943 > 1/7`）。对照：半径 `↑qR ≈ 0.379984` 时原点被覆盖
（`covers_inner_lower 0`）。⇒ 覆盖半径**不可降到 `|Y1|` 以下**，且 `Covers` 对半径确有判别力。 -/
theorem not_covers_centers_seventh : ¬ Covers (centersOfRoot uCert) ((1 : ℝ) / 7) := by
  intro h
  obtain ⟨i, hi⟩ := h 0 zero_mem_unitDisk
  linarith [dist_zero_centers_gt_seventh i, hi]

/-! ## §6ter 角度界 `|θ_k| ≤ 2π/3`（具体数据）与更锐的负对照

这一节的两类工具正是 §2ter 记录的那 4 条紧射线所缺的**角度条件**的同款工具：
`θ_k` 是 `a_0..a_3, π` 的显式线性式，故其界是**有理不等式**（`norm_num` + `π` 的 6 位小数夹）。
下面先用它把负对照从「原点 + 半径 `1/7`」抬到「`(−1,0)` + 半径 `3/8 < qR`」。 -/

/-- `|θ_1| ≤ 2π/3`（= `π − 2a_0 − a_1 ≤ 2π/3` ⟺ `π/3 ≤ 2a_0 + a_1`，余量 3.8e-2）。 -/
theorem abs_theta_uCert_one : |thetaOf (angleVec uCert) 1| ≤ 2 * Real.pi / 3 := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [abs_le]
  constructor <;> norm_num [qA0, qA1, qA2, qA3, qS] <;>
    linarith [Real.pi_gt_d6, Real.pi_lt_d6]

/-- `|θ_2| ≤ 2π/3`。 -/
theorem abs_theta_uCert_two : |thetaOf (angleVec uCert) 2| ≤ 2 * Real.pi / 3 := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [abs_le]
  constructor <;> norm_num [qA0, qA1, qA2, qA3, qS] <;>
    linarith [Real.pi_gt_d6, Real.pi_lt_d6]

/-- `|θ_3| ≤ 2π/3`。 -/
theorem abs_theta_uCert_three : |thetaOf (angleVec uCert) 3| ≤ 2 * Real.pi / 3 := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [abs_le]
  constructor <;> norm_num [qA0, qA1, qA2, qA3, qS] <;>
    linarith [Real.pi_gt_d6, Real.pi_lt_d6]

/-- `|θ_4| ≤ 2π/3`（`θ_4 = 0`）。 -/
theorem abs_theta_uCert_four : |thetaOf (angleVec uCert) 4| ≤ 2 * Real.pi / 3 := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  positivity

/-- `|θ_5| ≤ 2π/3`。 -/
theorem abs_theta_uCert_five : |thetaOf (angleVec uCert) 5| ≤ 2 * Real.pi / 3 := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [abs_le]
  constructor <;> norm_num [qA0, qA1, qA2, qA3, qS] <;>
    linarith [Real.pi_gt_d6, Real.pi_lt_d6]

/-- `|θ_6| ≤ 2π/3`。 -/
theorem abs_theta_uCert_six : |thetaOf (angleVec uCert) 6| ≤ 2 * Real.pi / 3 := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [abs_le]
  constructor <;> norm_num [qA0, qA1, qA2, qA3, qS] <;>
    linarith [Real.pi_gt_d6, Real.pi_lt_d6]

/-- `|θ_7| ≤ 2π/3`（= `π − 2a_0 − a_1 ≤ 2π/3`，与 `θ_1` 同式）。 -/
theorem abs_theta_uCert_seven : |thetaOf (angleVec uCert) 7| ≤ 2 * Real.pi / 3 := by
  rw [angleVec_uCert_eq]
  simp only [thetaOf]
  simp
  rw [abs_le]
  constructor <;> norm_num [qA0, qA1, qA2, qA3, qS] <;>
    linarith [Real.pi_gt_d6, Real.pi_lt_d6]

/-- **`cos θ_k ≥ −1/2`**（`k ≠ 0, 8`）：由 `|θ_k| ≤ 2π/3` 与 `cos` 在 `[0,π]` 上单调。 -/
theorem cos_theta_uCert_ge (k : Fin 9) (h0 : (k : ℕ) ≠ 0) (h8 : (k : ℕ) ≠ 8) :
    -(1 / 2 : ℝ) ≤ Real.cos (thetaOf (angleVec uCert) k) := by
  have hθ : |thetaOf (angleVec uCert) k| ≤ 2 * Real.pi / 3 := by
    fin_cases k
    · exact absurd rfl h0
    · exact abs_theta_uCert_one
    · exact abs_theta_uCert_two
    · exact abs_theta_uCert_three
    · exact abs_theta_uCert_four
    · exact abs_theta_uCert_five
    · exact abs_theta_uCert_six
    · exact abs_theta_uCert_seven
    · exact absurd rfl h8
  have hπ2 : 2 * Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hπ2 hθ
  have hc23 : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  rwa [hc23, Real.cos_abs] at hmono

/-- **`(−1,0)` 到环盘中心的距离 > 3/8**（`k ≠ 0, 8`）：由 `cos θ_k ≥ −1/2` 与
`dist² = 1 + ρ² + 2ρcos θ ≥ 1 + ρ² − ρ = (ρ − 1/2)² + 3/4 ≥ 3/4`。 -/
theorem dist_neg_one_ringCenter_gt (k : Fin 9)
    (hcos : -(1 / 2 : ℝ) ≤ Real.cos (thetaOf (angleVec uCert) k)) :
    (3 : ℝ) / 8 < dist (!₂[(-1 : ℝ), 0] : Point) (ringCenter uCert k) := by
  have hsq : dist (!₂[(-1 : ℝ), 0] : Point) (ringCenter uCert k) ^ 2
      = 1 + rhoK uCert k ^ 2 + 2 * rhoK uCert k * Real.cos (thetaOf (angleVec uCert) k) := by
    rw [dist_point_eq_sqrt, neg_pair_coord0, neg_pair_coord1, ringCenter_coord0,
      ringCenter_coord1]
    have hnn : 0 ≤ ((-1 : ℝ) - rhoK uCert k * Real.cos (thetaOf (angleVec uCert) k)) ^ 2
        + ((0 : ℝ) - rhoK uCert k * Real.sin (thetaOf (angleVec uCert) k)) ^ 2 := by positivity
    rw [Real.sq_sqrt hnn]
    have h := Real.sin_sq_add_cos_sq (thetaOf (angleVec uCert) k)
    nlinarith [h]
  have hρ : 0 ≤ rhoK uCert k := rhoK_nonneg_cert k
  have hkey : (3 : ℝ) / 4 ≤ dist (!₂[(-1 : ℝ), 0] : Point) (ringCenter uCert k) ^ 2 := by
    rw [hsq]
    nlinarith [hcos, hρ, sq_nonneg (rhoK uCert k - 1 / 2),
      mul_nonneg hρ (by linarith : (0 : ℝ) ≤ Real.cos (thetaOf (angleVec uCert) k) + 1 / 2)]
  nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist (!₂[(-1 : ℝ), 0] : Point) (ringCenter uCert k)), hkey]

/-- **`(−1,0)` 到每个中心的距离都 > 3/8**（`k = 0, 8` 处用精确恒等式 `dist = ↑qR > 3/8`）。 -/
theorem dist_neg_one_centers_gt (i : Fin 11) :
    (3 : ℝ) / 8 < dist (!₂[(-1 : ℝ), 0] : Point) (centersOfRoot uCert i) := by
  have hqY0 : hub0 uCert = (qY0 : ℝ) • (!₂[(1 : ℝ), 0] : Point) := by
    rw [hub0, uCert_four, smul_cons_zero, mul_one]
  have hqY1 : hub1 uCert = (qY1 : ℝ) • (!₂[(1 : ℝ), 0] : Point) := by
    rw [hub1, uCert_five, smul_cons_zero, mul_one]
  by_cases h9 : (i : ℕ) = 9
  · have hi : i = 9 := Fin.ext h9
    subst hi
    rw [centersOfRoot_nine, hqY0, dist_cons_smul_cons]
    rw [abs_of_neg (by norm_num [qY0] : (-1 : ℝ) - (qY0 : ℝ) < 0)]
    norm_num [qY0]
  · by_cases h10 : (i : ℕ) = 10
    · have hi : i = 10 := Fin.ext h10
      subst hi
      rw [centersOfRoot_ten, hqY1, dist_cons_smul_cons]
      rw [abs_of_neg (by norm_num [qY1] : (-1 : ℝ) - (qY1 : ℝ) < 0)]
      norm_num [qY1]
    · have hi9 : (i : ℕ) < 9 := by
        have := i.isLt; omega
      have hci : centersOfRoot uCert i = ringCenter uCert ⟨(i : ℕ), hi9⟩ := by
        simp only [centersOfRoot, dif_pos hi9]
      rw [hci]
      by_cases h0 : (i : ℕ) = 0
      · have hidx : (⟨(i : ℕ), hi9⟩ : Fin 9) = 0 := Fin.ext h0
        rw [hidx, dist_neg_one_zero_ringCenter_zero]
        norm_num [qR]
      · by_cases h8 : (i : ℕ) = 8
        · have hidx : (⟨(i : ℕ), hi9⟩ : Fin 9) = 8 := Fin.ext h8
          rw [hidx, dist_neg_one_zero_ringCenter_eight]
          norm_num [qR]
        · exact dist_neg_one_ringCenter_gt ⟨(i : ℕ), hi9⟩
            (cos_theta_uCert_ge ⟨(i : ℕ), hi9⟩ h0 h8)

/-- **负对照 3（更锐，判别力最强的一条，kernel-proved）**：半径取 `3/8 = 0.375 < ↑qR ≈ 0.379984`
时 `Covers` 已为假 —— 见证点 `(−1,0) ∈ D`（到 `C_0`、`C_8` 恰 `↑qR > 3/8`，到其余 9 个中心 > 0.85）。
⇒ 该构型的覆盖半径在 `(−1,0)` 处**不能降 3/8 以下**（`qR − 3/8 ≈ 4.98e-3`）。 -/
theorem not_covers_three_eighths : ¬ Covers (centersOfRoot uCert) ((3 : ℝ) / 8) := by
  intro h
  obtain ⟨i, hi⟩ := h (!₂[(-1 : ℝ), 0] : Point)
    (by rw [mem_unitDisk, cons_norm_eq_abs]; norm_num)
  linarith [dist_neg_one_centers_gt i, hi]

/-! ## §7 可信基础 -/

#print axioms N11Formalization.arcLoG_succ_eq_arcHiG_or_sub
#print axioms N11Formalization.arc_chain_cover_general
#print axioms N11Formalization.circle_covered_of_range
#print axioms N11Formalization.arcEnd_eq_circleMap_arcLo_succ
#print axioms N11Formalization.dist_Uvec_ringCenter_self
#print axioms N11Formalization.dist_Uvec_ringCenter_succ
#print axioms N11Formalization.neg_axis_covered_all_of_residual
#print axioms N11Formalization.covers_of_remaining_obligation
#print axioms N11Formalization.angleVec_uCert_le_two_fifths
#print axioms N11Formalization.rhoK_cert_ge_half
#print axioms N11Formalization.ringOnly_not_covers_origin_at_qR
#print axioms N11Formalization.dist_zero_centers_gt_seventh
#print axioms N11Formalization.not_covers_centers_seventh
#print axioms N11Formalization.cos_theta_uCert_ge
#print axioms N11Formalization.dist_neg_one_ringCenter_gt
#print axioms N11Formalization.dist_neg_one_centers_gt
#print axioms N11Formalization.not_covers_three_eighths

end N11Formalization
