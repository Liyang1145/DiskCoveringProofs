/-
# `D` 的**两批具体正性**：16 条有限有理不等式（`hWk` 9 + `hrad` 5 + `hWp` 1）

## 为什么这条路线便宜（关键判断，已用探针确认）
* `WkIv j = R² − (sin a_j)²`：`sq`/`sub` 的展开**只用**叶子 `sa_j_*` 与 `cCert_6` ⇒ **不含 `Nat.sqrt`**。
* `radIv k = Δx² + Δy²`：只用 `uv_*`/`hub*_*`/`wp_*`/`ring_6_*` 的四角乘积 ⇒ **不含 `Nat.sqrt`**。
* **`inv` 侧需要的 `0 < (twoRadSqrtIv k).lo` / `0 < (twoSqrtWkIv j).lo` 不需要在这里重算** ——
  它们已由 `ResidualDerivD.lean` 的 `twoRadSqrtIv_pos` / `twoMulIv_pos` + `sqrtLo_pos`
  **从 `0 < (radIv k).lo` / `0 < (WkIv j).lo` 一般性地推出**（`inv` 侧无需端点字面量）。
* `WpIv` 只用 `cCert` 的字面量。

⇒ 16 条全部是**叶子表上的 `norm_num`**，代价与 `ResidualIntervalReadout.lean` 同量级。
**端点来源**：全部来自本工程自己的区间求值 + 叶子表；**未引用任何外部数值表**（`C1060`）。

**真实等级**：kernel-proved（`norm_num` 具体有理算术），无条件。
-/
import N11Formalization.ResidualDerivD
import N11Formalization.ResidualIntervalReadout
import N11Formalization.ResidualIntervalReadoutLag

noncomputable section

namespace N11Formalization

open RatInterval

/-! ## 1. `hWk`：9 条 `0 < (WkIv j).lo`（⇒ `Wk j ≠ 0` 与 `inv` 侧前提） -/

theorem WkIv_lo_pos_0 : 0 < (WkIv 0).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_0_lo, FmLagReadout.sa_0_hi, cCert_6]

theorem WkIv_lo_pos_1 : 0 < (WkIv 1).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_1_lo, FmLagReadout.sa_1_hi, cCert_6]

theorem WkIv_lo_pos_2 : 0 < (WkIv 2).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_2_lo, FmLagReadout.sa_2_hi, cCert_6]

theorem WkIv_lo_pos_3 : 0 < (WkIv 3).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_3_lo, FmLagReadout.sa_3_hi, cCert_6]

theorem WkIv_lo_pos_4 : 0 < (WkIv 4).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_4_lo, FmLagReadout.sa_4_hi, cCert_6]

theorem WkIv_lo_pos_5 : 0 < (WkIv 5).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_5_lo, FmLagReadout.sa_5_hi, cCert_6]

theorem WkIv_lo_pos_6 : 0 < (WkIv 6).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_6_lo, FmLagReadout.sa_6_hi, cCert_6]

theorem WkIv_lo_pos_7 : 0 < (WkIv 7).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_7_lo, FmLagReadout.sa_7_hi, cCert_6]

theorem WkIv_lo_pos_8 : 0 < (WkIv 8).lo := by
  norm_num [WkIv, sinAIv, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.sa_8_lo, FmLagReadout.sa_8_hi, cCert_6]

/-! ## 2. `hWp`：1 条 `0 < WpIv.lo`（只用 `cCert` 字面量） -/

theorem WpIv_lo_pos : 0 < WpIv.lo := by
  norm_num [WpIv, RatInterval.sub, RatInterval.sq, RatInterval.mul, ofRat, cCert_4, cCert_5,
    cCert_6]

/-! ## 3. `hrad`：5 条 `0 < (radIv k).lo`（Δx²+Δy²；探针盒心最小 `1.2159e-1`） -/

theorem radIv_lo_pos_0 : 0 < (radIv 0).lo := by
  norm_num [radIv, DxIv, DyIv, Aiv, Biv, RatInterval.add, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.uv_1_0_lo, FmLagReadout.uv_1_0_hi, FmLagReadout.uv_1_1_lo, FmLagReadout.uv_1_1_hi,
    hub1_0_lo, hub1_0_hi, hub1_1_lo, hub1_1_hi]

theorem radIv_lo_pos_1 : 0 < (radIv 1).lo := by
  norm_num [radIv, DxIv, DyIv, Aiv, Biv, RatInterval.add, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.uv_2_0_lo, FmLagReadout.uv_2_0_hi, FmLagReadout.uv_2_1_lo, FmLagReadout.uv_2_1_hi,
    hub0_0_lo, hub0_0_hi, hub0_1_lo, hub0_1_hi]

theorem radIv_lo_pos_2 : 0 < (radIv 2).lo := by
  norm_num [radIv, DxIv, DyIv, Aiv, Biv, RatInterval.add, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.uv_3_0_lo, FmLagReadout.uv_3_0_hi, FmLagReadout.uv_3_1_lo, FmLagReadout.uv_3_1_hi,
    hub0_0_lo, hub0_0_hi, hub0_1_lo, hub0_1_hi]

theorem radIv_lo_pos_3 : 0 < (radIv 3).lo := by
  norm_num [radIv, DxIv, DyIv, Aiv, Biv, RatInterval.add, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.uv_8_0_lo, FmLagReadout.uv_8_0_hi, FmLagReadout.uv_8_1_lo, FmLagReadout.uv_8_1_hi,
    hub1_0_lo, hub1_0_hi, hub1_1_lo, hub1_1_hi]

theorem radIv_lo_pos_4 : 0 < (radIv 4).lo := by
  norm_num [radIv, DxIv, DyIv, Aiv, Biv, RatInterval.add, RatInterval.sub, RatInterval.sq, ofRat,
    FmLagReadout.wp_0_lo, FmLagReadout.wp_0_hi, FmLagReadout.wp_1_lo, FmLagReadout.wp_1_hi,
    FmLagReadout.ring_6_0_lo, FmLagReadout.ring_6_0_hi, FmLagReadout.ring_6_1_lo,
    FmLagReadout.ring_6_1_hi]

/-! ## 4. 两族前提的 `∀` 形式（紧凑的 pattern-matching 定义） -/

theorem WkIv_lo_pos : ∀ j : Fin 9, 0 < (WkIv j).lo
  | 0 => WkIv_lo_pos_0
  | 1 => WkIv_lo_pos_1
  | 2 => WkIv_lo_pos_2
  | 3 => WkIv_lo_pos_3
  | 4 => WkIv_lo_pos_4
  | 5 => WkIv_lo_pos_5
  | 6 => WkIv_lo_pos_6
  | 7 => WkIv_lo_pos_7
  | 8 => WkIv_lo_pos_8

theorem radIv_lo_pos : ∀ k : Fin 5, 0 < (radIv k).lo
  | 0 => radIv_lo_pos_0
  | 1 => radIv_lo_pos_1
  | 2 => radIv_lo_pos_2
  | 3 => radIv_lo_pos_3
  | 4 => radIv_lo_pos_4

/-! ## 5. `hD` 的前提清单压到**单条**（`hWk`/`hWp`/`hrad` 全部已消） -/

/-- 两点分离：`Δx²+Δy² ≠ 0 ⟹ 两点不同`（`Point` 坐标读法）。 -/
theorem point_ne_of_sq_sum_ne {a b : Point}
    (h : (a.ofLp 0 - b.ofLp 0) ^ 2 + (a.ofLp 1 - b.ofLp 1) ^ 2 ≠ 0) : a ≠ b := by
  intro hab
  apply h
  rw [hab]
  ring

/-- **`hD`（只剩 `DifferentiableAt` 一条前提）**：16 条有理不等式全部由本文件 §1–§3 付清。 -/
theorem hD_of_diff (hd : DifferentiableAt ℝ residualFun u0) :
    ∀ (k : Fin 5) (i : Fin 7),
      (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k) := by
  intro k i
  fin_cases k
  · exact hD_0 hd WkIv_lo_pos radIv_lo_pos i
  · exact hD_1 hd WkIv_lo_pos radIv_lo_pos i
  · exact hD_2 hd WkIv_lo_pos radIv_lo_pos i
  · exact hD_3 hd WkIv_lo_pos radIv_lo_pos i
  · exact hD_4 hd WkIv_lo_pos WpIv_lo_pos radIv_lo_pos i

/-! ## 6. 消掉最后一条：`DifferentiableAt ℝ residualFun u0`

用 `Transport.contDiffAt_residualFun_first7 cCertR`（其 7 条条件的确切形状已按源码核过，
**非凭印象**）逐条由 §1–§3 的正性 + `point_ne_of_sq_sum_ne` 给出。 -/

theorem differentiableAt_residualFun_cCertR : DifferentiableAt ℝ residualFun u0 := by
  rw [show u0 = first7 cCertR from rfl]
  refine differentiableAt_pi.mpr (fun i => ?_)
  have h1 : ∀ j : Fin 9, (cCertR 6) ^ 2 - (Real.sin (angleVec cCertR j)) ^ 2 ≠ 0 := by
    intro j
    rw [← u0_six, ← angleVec_u0_eq j]
    exact Wk_ne_zero j (WkIv_lo_pos j)
  have h2 : (cCertR 6) ^ 2 - ((cCertR 5 - cCertR 4) / 2) ^ 2 ≠ 0 := by
    rw [← u0_six, ← u0_five, ← u0_four]
    exact Wp_ne_zero WpIv_lo_pos
  have h3 : Uvec cCertR 1 ≠ hub1 cCertR := by
    rw [← Uvec_u0_eq 1, ← hub1_u0]
    exact point_ne_of_sq_sum_ne (sq_sum_ne_of_rad 0 (radIv_lo_pos 0))
  have h4 : Uvec cCertR 2 ≠ hub0 cCertR := by
    rw [← Uvec_u0_eq 2, ← hub0_u0]
    exact point_ne_of_sq_sum_ne (sq_sum_ne_of_rad 1 (radIv_lo_pos 1))
  have h5 : Uvec cCertR 3 ≠ hub0 cCertR := by
    rw [← Uvec_u0_eq 3, ← hub0_u0]
    exact point_ne_of_sq_sum_ne (sq_sum_ne_of_rad 2 (radIv_lo_pos 2))
  have h6 : Uvec cCertR 8 ≠ hub1 cCertR := by
    rw [← Uvec_u0_eq 8, ← hub1_u0]
    exact point_ne_of_sq_sum_ne (sq_sum_ne_of_rad 3 (radIv_lo_pos 3))
  have h7 : wPoint cCertR ≠ ringCenter cCertR 6 := by
    rw [← wPoint_u0, ← ringCenter_u0 6]
    exact point_ne_of_sq_sum_ne (sq_sum_ne_of_rad 4 (radIv_lo_pos 4))
  exact (contDiffAt_residualFun_first7 (n := (1 : WithTop ℕ∞)) cCertR h1 h2 h3 h4 h5 h6 h7 i)
    |>.differentiableAt (by norm_num)

/-- **`hD`（无条件，35 格）**：`D` 包含证书盒心处的残差 Jacobian，**零未消前提**。 -/
theorem hD : ∀ (k : Fin 5) (i : Fin 7),
    (D k i).Mem ((fderiv ℝ residualFun (first7 cCertR) (Pi.single i 1)) k) :=
  hD_of_diff differentiableAt_residualFun_cCertR

end N11Formalization
