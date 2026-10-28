import N11Formalization.FlashTenBoundaryScale

/-!
# C450 证书数据（第 1 段标定）：源逻辑形式 + 一段精确数据 + 全分支 consumer 骨架

## 0. 源证书的逻辑形式（读源脚本确认，非猜测）

`research-2026/solo-20260922/certify_directional_dual_t.py`：

* `target = iv.pi * (c['boundary'][0] + c['hub'][0]) / 10`（**每段**用自己的权重算阈值）；
* 对每个叶盒 `if val.b < target.a: leaves+=1`（即对盒内**所有** `(t, cos φ, e, 根符号)`
  验证 `upper(Q) < lower(target)`）。

⇒ **逻辑形式 = "按 e 分段（36 段），每段一组权重 + 一个阈值；段内对所有单盘同一阈值"**，
**不是**"每盘各自阈值"，也**不是**"按半径分箱"。故容量侧（`two_circle_capacity`）与逐盘侧
必须用**同一段**的权重 ✓（装配件正是固定 (W0,W1) ✓）。

## 1. 本件做什么

* 用**源的变量** `(t, cos φ, e, 根符号)` 写出源证书的量 `Q`（定义 `c450Q`、`c450QAngle`）；
* 给 `cos(kφ) ↔ v = cos φ` 的 Chebyshev 桥（源以 `v` 为自由变量）；
* 用源 JSON **第 1 段**（`e ∈ [0, 1/250]`，源文件 `directional_low_cover.json` 第一段）的
  **精确有理权重**写出该段数据 `C450Seg1Data`（含非负条件与域上界）。

## 2. 剩余义务（下一步，逐盘界）

把 `C450Seg1Data` 套到**真实环盘**上得 `外_i + 内_i < 2·target`：需
(i) 极坐标分解 `c i = !₂[ρ_i cos φ_i, ρ_i sin φ_i]` 与内圆相对中心 `c i − h = R • !₂[…]`；
(ii) 用 `arc_integral_scale_clamp`（full/empty/clamp 三支都在内）把两个弧积分认成闭式；
(iii) 用 Chebyshev 桥把闭式换到 `v`-形再套数据。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-! ## 1. Chebyshev 桥：`cos(kφ)` 只用 `v = cos φ` 表达 -/

theorem cos_two_mul_of_cos {v φ : ℝ} (hv : Real.cos φ = v) :
    Real.cos (2 * φ) = 2 * v ^ 2 - 1 := by
  rw [Real.cos_two_mul, hv]

theorem cos_three_mul_of_cos {v φ : ℝ} (hv : Real.cos φ = v) :
    Real.cos (3 * φ) = 4 * v ^ 3 - 3 * v := by
  rw [Real.cos_three_mul, hv]

/-! ## 2. 源证书的量 `Q`（源变量 `t, v = cos φ, e, 根符号`）

`ρ = cos t ± √(R² - sin²t)`（`R = 19/50`，两符号都枚举）；
规范框里 hub 在 `(e,0)`，`ℓ = |c - hub| = √((ρv - e)² + (ρ sinφ)²)`，`sinφ = √(1-v²)`；
`b = arccos(ℓ/(2R))` 若 `ℓ < 2R` 否则 `0`；`cq = cos ψ = (ρv - e)/ℓ`（不需要角度）。
则 `Q = [a₀₀t + Σ_k a_{0k} sin(kt)cos(kφ)/k] + [a₁₀b + Σ_k a_{1k} sin(kb)cos(kψ)/k]`
（= 源文"弧积分除以 2"的总和）；证书断言 `Q < π(a₀₀+a₁₀)/10`。 -/

noncomputable def c450Q (a00 a01 a02 a03 a10 a11 a12 a13 : ℚ) (t v e : ℝ) (sign : Bool) : ℝ :=
  let R : ℝ := 19 / 50
  let rho : ℝ := Real.cos t + (if sign then 1 else -1) * Real.sqrt (R ^ 2 - (Real.sin t) ^ 2)
  let sφ : ℝ := Real.sqrt (1 - v ^ 2)
  let ell : ℝ := Real.sqrt ((rho * v - e) ^ 2 + (rho * sφ) ^ 2)
  let b : ℝ := if ell < 2 * R then Real.arccos (ell / (2 * R)) else 0
  let cq : ℝ := if ell = 0 then 1 else (rho * v - e) / ell
  ((a00 : ℝ) * t + (a01 : ℝ) * Real.sin t * v
      + (a02 : ℝ) * Real.sin (2 * t) * (2 * v ^ 2 - 1) / 2
      + (a03 : ℝ) * Real.sin (3 * t) * (4 * v ^ 3 - 3 * v) / 3)
    + ((a10 : ℝ) * b + (a11 : ℝ) * Real.sin b * cq
      + (a12 : ℝ) * Real.sin (2 * b) * (2 * cq ^ 2 - 1) / 2
      + (a13 : ℝ) * Real.sin (3 * b) * (4 * cq ^ 3 - 3 * cq) / 3)

/-! ## 3. 第 1 段的精确数据（权重取自源 JSON 第 1 段）

源 `directional_low_cover.json` 第一段：`e_interval = ["0", "0.004"] = [0, 1/250]`，
权重 `boundary = [641363/250000, 0, 0, 0]`、`hub = [338103/500000, -17317/1000000, 31/100000, -27/1000000]`，
`target = π(a₀₀+a₁₀)/10 ≈ 1.0183968958250582`（与 `c450Q` 的阈值一致，已数值核对）。
真实半宽上界是 `arcsin(19/50)`；源用稍大的有理数 `0.3897962964742606`（只扩张验证域）。 -/

/-- 第 1 段数据（**源证书的断言形状**；本件只把它固定成 Lean `Prop`，**不证它**）。 -/
def C450Seg1Data : Prop :=
  (|(0 : ℚ)| + |(0 : ℚ)| + |(0 : ℚ)| ≤ (641363 : ℚ) / 250000)
    ∧ (|(-17317 : ℚ) / 1000000| + |(31 : ℚ) / 100000| + |(-27 : ℚ) / 1000000|
        ≤ (338103 : ℚ) / 500000)
    ∧ (∀ (t v e : ℝ) (sign : Bool),
        0 ≤ t → t ≤ (0.3897962964742606 : ℝ) → -1 ≤ v → v ≤ 1 →
        0 ≤ e → e ≤ 1 / 250 →
        c450Q (641363 / 250000) 0 0 0 (338103 / 500000) (-17317 / 1000000) (31 / 100000)
            (-27 / 1000000) t v e sign
          < Real.pi * ((641363 : ℝ) / 250000 + (338103 : ℝ) / 500000) / 10)

end

end N11Formalization
