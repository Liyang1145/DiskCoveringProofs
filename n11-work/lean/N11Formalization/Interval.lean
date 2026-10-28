/-
  N11Formalization.Interval
  =========================

  可信区间算术内核（伞模块）。子模块：

  * `N11Formalization.Interval.Core` —— `RatInterval` + **ℝ 侧语义**（`toSet`/`Mem`）
    + 四则运算（`add`/`neg`/`sub`/`mul`/`inv`/`div`/`pow`）的**包含性**与 `Valid` 保持性
    + 具体端点读数（含 min/max 方向的等式检验）。
  * `N11Formalization.Interval.Sqrt` —— `Real.sqrt` 的精确有理外向端点
    （`Nat.sqrt` 造的 `sqrtLo`/`sqrtHi`）与包含性。
  * `N11Formalization.Interval.Eval` —— 表达式语言的反射求值（含通用一元挂点 `app1`
    与保守回退 `none`）及其**声音性** `IExpr.eval_sound`。
  * `N11Formalization.Interval.Vector` —— M1–M4：`abs`（区间绝对值）、`dot`（有限点积）、
    `supNorm`（上确界范数）、`BoxIncl`（盒包含），以及 Krawczyk 算子的**仿射骨架**
    `krawczykAffine` 及其包含性 `krawczykAffine_mem`（Fm 与矩阵 M 作为输入数据）。
  * `N11Formalization.Interval.Trig` —— M5（部分）：π/π/2 的 20 位有理夹逼、
    `sin`/`cos` 的**点级有理外向界**（`sinLo/sinHi/cosLo/cosHi`，基于
    `Real.sin_bound`/`cos_bound` 的显式有理余项）、区间算子 `sinI`/`cosI`
    （窗口 `[-1,1]` 内给界、窗口外保守回退 `[-1,1]`）及其无条件包含性
    `sinI_mem`/`cosI_mem`。
  * `N11Formalization.Interval.Shift` —— **M5b/R2：移位选择引理**
    `exists_shift_halfPi : ∀ q : ℚ, |q| ≤ 10 → ∃ k : ℤ, |q − k·(π/2)| ≤ 1`
    （单独成件、可独立复用与复核；构造用 20 位 π 下界 + ℚ 上的 `Int.floor`）。
    **R3 核心已证**（Interval/Phase.lean：四态表 + 两个 ±π/2 转移 + 沿两侧的 ℕ 归纳 + int_split_nat），\n    但 k : ℤ 的直接封装遇 cast 归一化障碍（实现层面，已在文件内如实记录）；**R4 未做**；
    精确待办见 `evidence/interval/INTERVAL-GAPS.md` §3.1。

  本模块只依赖 `Mathlib`，不含 `sorry`/自定义 `axiom`/`native_decide`。
  尚未覆盖的算子（`exp`/`log`/`atan2`、以及 `sin/cos` 的一般范围约化）与精确缺口陈述见
  `evidence/interval/INTERVAL-GAPS.md`。
-/
import N11Formalization.Interval.Core
import N11Formalization.Interval.Sqrt
import N11Formalization.Interval.Eval
import N11Formalization.Interval.Vector
import N11Formalization.Interval.Trig
import N11Formalization.Interval.Shift
import N11Formalization.Interval.Phase
import N11Formalization.Interval.Range
import N11Formalization.Interval.Taylor19
import N11Formalization.Interval.Taylor19B
import N11Formalization.Interval.Taylor19C
import N11Formalization.Interval.IndexIf






