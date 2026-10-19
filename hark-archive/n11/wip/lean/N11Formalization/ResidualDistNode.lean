/-
# `dist` 节点：把 5 个残差分量**化归为同一形状**（Lead，R55）

**动机**：`TCSystem.lean` 的 `residual` 五个分量**全是** `dist (A_k z) (B_k z) − z 6`：

| k | `A_k` | `B_k` |
|---|---|---|
| 0 | `Uvec (pad12 z) 1` | `hub1 (pad12 z) = !₂[z 5, 0]` |
| 1 | `Uvec (pad12 z) 2` | `hub0 (pad12 z) = !₂[z 4, 0]` |
| 2 | `Uvec (pad12 z) 3` | `hub0 (pad12 z)` |
| 3 | `Uvec (pad12 z) 8` | `hub1 (pad12 z)` |
| 4 | `wPoint (pad12 z) = !₂[(z4+z5)/2, √(z6² − ((z5−z4)/2)²)]` | `ringCenter (pad12 z) 6` |

⇒ **只需一条通用的 `dist` 节点引理**（对任意 `A, B` 及其 `HasFDerivAt`），5 个分量是其**实例**
（工作量从 5× 压到 1× + 5 次实例化）。

**本文件提供的是那条化归的"接线"部分**：定义 `resA`/`resB` 并证明 `residualFun_eq_dist`
（`rfl` 级，逐 `k` 由 `fin_cases` 展开）。**真正需要分析的是"通用 `dist` 引理"**，
它需要 `A z ≠ B z`（因为 `dist = ‖A − B‖` 的导数含 `1/‖A−B‖`）—— 这一步的正性前提
属"两批正性"那批（探针已给判决：盒上 `Δx²+Δy²` 的下界最小 `1.2159e-1`，安全非刀锋）。

**注意 `− (pad12 z) 6` 的写法**：`pad12 z` 的第 6 坐标是 `if (6:ℕ) < 7 then z ⟨6,⋯⟩ else 0`，
**不是**语法的 `z 6`（`(6 : Fin 7)` 与 `⟨6, ⋯⟩` 的 `OfNat` 证明项不同 ⇒ 不等价，本工程已多次踩到）。
故本文件用 `(pad12 z) 6` 保持 `rfl` 干净；需要 `z 6` 时另证一条 `pad12_six`。
-/
import N11Formalization.SmoothnessC2
import N11Formalization.ResidualDerivNode2

namespace N11Formalization

/-- `residual` 第 `k` 分量的"被减点" `A_k`（**随 `z`**）。 -/
noncomputable def resA : Fin 5 → (Fin 7 → ℝ) → Point
  | 0, z => Uvec (pad12 z) 1
  | 1, z => Uvec (pad12 z) 2
  | 2, z => Uvec (pad12 z) 3
  | 3, z => Uvec (pad12 z) 8
  | 4, z => wPoint (pad12 z)

/-- `residual` 第 `k` 分量的"减点" `B_k`（**也随 `z`** —— `hub0 = !₂[z4,0]`、`hub1 = !₂[z5,0]`、
`ringCenter (·) 6` 亦然；这条依赖**极易漏**，漏则 `∂Δx/∂z_i` 缺 `−δ_{i,4}`/`−δ_{i,5}`）。 -/
noncomputable def resB : Fin 5 → (Fin 7 → ℝ) → Point
  | 0, z => hub1 (pad12 z)
  | 1, z => hub0 (pad12 z)
  | 2, z => hub0 (pad12 z)
  | 3, z => hub1 (pad12 z)
  | 4, z => ringCenter (pad12 z) 6

/-- **5 个残差分量同形**：`residualFun z k = dist (A_k z) (B_k z) − (pad12 z) 6`。
（`rfl` 级：`residualFun z = residual (pad12 z)` 是定义等式，逐 `k` 展开 `![…]` 即得。） -/
theorem residualFun_eq_dist (k : Fin 5) (z : Fin 7 → ℝ) :
    residualFun z k = dist (resA k z) (resB k z) - (pad12 z) 6 := by
  fin_cases k <;> rfl

/-- **距离的坐标化**：`dist A B = √(‖A − B‖²)`（`dist = ‖·‖`，而 `‖v‖ = √(‖v‖²)`）。 -/
theorem dist_eq_sqrt_norm_sq (A B : Point) : dist A B = Real.sqrt (‖A - B‖ ^ 2) := by
  rw [dist_eq_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- **通用 `dist` 节点引理**（`dist` 沿两条可微曲线求导）。
利用 mathlib 的 **`HasFDerivAt.norm_sq`**（平方范数的导数，**不需非零前提**）
与 **`HasFDerivAt.sqrt`**（`√` 的链式，**非零前提显式在语句里**）。
由 `ResidualDistNode.residualFun_eq_dist`，`D` 的 5 个残差分量都是本引理的实例。 -/
theorem hasFDerivAt_dist_sqrt {A B : (Fin 7 → ℝ) → Point} {a b : (Fin 7 → ℝ) →L[ℝ] Point}
    {z : Fin 7 → ℝ} (hA : HasFDerivAt A a z) (hB : HasFDerivAt B b z)
    (hne : ‖(A - B) z‖ ^ 2 ≠ 0) :
    HasFDerivAt (fun w => Real.sqrt (‖(A - B) w‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖(A - B) z‖ ^ 2)))
        • ((2 : ℕ) • (innerSL ℝ) ((A - B) z) ∘SL (a - b))) z :=
  (hA.sub hB).norm_sq.sqrt hne

end N11Formalization
