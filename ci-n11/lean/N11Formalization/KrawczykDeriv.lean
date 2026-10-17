import N11Formalization.Krawczyk

/-!
# 从「导数算子界」到 Krawczyk 前提（G1 的解析桥；**不依赖区间库**）

`Krawczyk.lean` 已把根存在唯一归约到 `g = id − Y·F` 在球上的 Lipschitz 界与残差条件。
本文件补上**中间那一环**：区间侧能直接算出来的是导数算子界

  `‖I − Y · (∂F/∂x)(x)‖ ≤ K`（`x ∈ B(c,ρ)`），

而要喂给 `krawczyk_banach` 的是 `g` 在球上的 Lipschitz 界。二者由**中值不等式**连接：
`g` 在凸球上的导数就是 `I − Y·(∂F/∂x)`，故

  `‖g y − g x‖ ≤ K · ‖y − x‖`（`Convex.norm_image_sub_le_of_norm_fderiv_le`）。

⇒ 至此 **G1 的剩余义务只剩"三条区间不等式"里真正的数值部分**：
`K` 与 `η` 的**精确有理上界**（`Q ≤ 0.0043719716348663187201 < 1`、`η + Q·ρ < ρ`）。
所有非数值环节（中值不等式、Banach 收缩、包含性、唯一性）都已 kernel 付清。

**真实等级**：kernel-proved，无条件（除显式前提），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-- **导数算子界 ⇒ 球上的 Lipschitz 界**（中值不等式）。

若 `F` 在闭球上可微且 `‖I − Y·(fderiv F x)‖ ≤ K` 在球上成立，则
`g = fun x ↦ x − Y (F x)` 在球上是 `K`-Lipschitz。 -/
theorem lipschitzOn_ball_of_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (Y : E →L[ℝ] E) (c : E) (ρ K : ℝ)
    (hF : ∀ x ∈ closedBall c ρ, DifferentiableAt ℝ F x)
    (hbound : ∀ x ∈ closedBall c ρ, ‖ContinuousLinearMap.id ℝ E - Y.comp (fderiv ℝ F x)‖ ≤ K)
    {x y : E} (hx : x ∈ closedBall c ρ) (hy : y ∈ closedBall c ρ) :
    dist (x - Y (F x)) (y - Y (F y)) ≤ K * dist x y := by
  have hderiv : ∀ z ∈ closedBall c ρ,
      fderiv ℝ (fun z : E => z - Y (F z)) z
        = ContinuousLinearMap.id ℝ E - Y.comp (fderiv ℝ F z) := by
    intro z hz
    exact ((hasFDerivAt_id z).sub (Y.hasFDerivAt.comp z (hF z hz).hasFDerivAt)).fderiv
  have hdiff : ∀ z ∈ closedBall c ρ, DifferentiableAt ℝ (fun z : E => z - Y (F z)) z := by
    intro z hz
    exact (differentiableAt_id).sub (Y.differentiableAt.comp z (hF z hz))
  have hnorm : ∀ z ∈ closedBall c ρ, ‖fderiv ℝ (fun z : E => z - Y (F z)) z‖ ≤ K := by
    intro z hz
    rw [hderiv z hz]
    exact hbound z hz
  have hkey : ‖(y - Y (F y)) - (x - Y (F x))‖ ≤ K * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hnorm (convex_closedBall c ρ) hx hy
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (x - Y (F x)) (y - Y (F y)), norm_sub_rev x y]
  exact hkey

/-- **完整解析链（G1 的可用形式）**：只要区间侧给出

* `hF`：`F` 在闭球上可微（`F = TCSystem`，残差由显式 §2 构型给出，故此项由语义桥承担）；
* `hbound`：`‖I − Y·(∂F/∂x)(x)‖ ≤ K` 在球上（**区间盒包含性**的读数，`K = Q < 1`）；
* `hres`：`‖Y (F c)‖ + K·ρ < ρ`（**残差的有理上界**，`= η`）；

则 `F` 在球 `B(c,ρ)` 内**存在唯一零点**——即 C891 的根存在唯一，
不需要 Brouwer、不需要在 Lean 里展开 6 步收缩树。 -/
theorem krawczyk_banach_of_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : E → E) (Y : E →L[ℝ] E) (hY : Function.Injective Y)
    (c : E) (ρ K : ℝ) (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hF : ∀ x ∈ closedBall c ρ, DifferentiableAt ℝ F x)
    (hbound : ∀ x ∈ closedBall c ρ, ‖ContinuousLinearMap.id ℝ E - Y.comp (fderiv ℝ F x)‖ ≤ K)
    (hres : dist c (c - Y (F c)) + K * ρ < ρ) :
    ∃! x : E, x ∈ closedBall c ρ ∧ F x = 0 :=
  krawczyk_banach F Y hY c ρ K hρ hK0 hK1
    (fun _ hx _ hy => lipschitzOn_ball_of_deriv_bound F Y c ρ K hF hbound hx hy) hres

end N11Formalization
