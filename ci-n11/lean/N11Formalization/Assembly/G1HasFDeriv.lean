import N11Formalization.KrawczykDeriv
import N11Formalization.OpNorm
import N11Formalization.TCSystem

/-!
# Krawczyk，把「导数」变成**显式可审计的供给对象**

`KrawczykDeriv.lean` 的变体用 `fderiv ℝ F x`（`fderiv` 的自动微分）。这带来一个记账问题：
G1 的义务 (2) 变成「证明 `TCSystem` 可微」这个**不显式**的命题；而对源系统而言，
`TCSystem` 的可微性**内在地是 `residualFun` 的 C² 义务**（乘子块 `adjointBlock` 里出现
`fderiv ℝ residualFun z`，对 `z` 还要再求一次导）。

本文件把导数换成**由区间侧供给的显式函数** `F' : E → E →L[ℝ] E`（对源系统即源文
`tc_s33_kkt.py` 自述的块 Jacobian `[∂f/∂z, 0; −ΣλᵢHᵢ, −J_f^T]`），只要求

  `∀ x ∈ B(c,ρ), HasFDerivAt F (F' x) x`

—— 一条**等式风味**的、可独立审计的义务。好处：

* 义务从「不显式的可微性」变成「`F'` 恰好是导数」这一条 `HasFDerivAt`；
* 区间侧只需要包络**显式函数** `F'` 的逐元素取值，**完全不需要**对 `fderiv` 的复合做推理；
* 与 §`KrawczykDeriv` 的链完全兼容（`HasFDerivAt.fderiv` 把两者接上）。

**真实等级**：kernel-proved，无条件（除显式前提），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-- **供给导数版的中值不等式**：若 `F` 在闭球上以 `F' x` 为导数，且
`‖I − Y·F'(x)‖ ≤ K` 在球上，则 `g = fun x ↦ x − Y (F x)` 在球上 `K`-Lipschitz。 -/
theorem lipschitzOn_ball_of_hasFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (F' : E → E →L[ℝ] E) (Y : E →L[ℝ] E) (c : E) (ρ K : ℝ)
    (hdiff : ∀ x ∈ closedBall c ρ, HasFDerivAt F (F' x) x)
    (hbound : ∀ x ∈ closedBall c ρ, ‖ContinuousLinearMap.id ℝ E - Y.comp (F' x)‖ ≤ K)
    {x y : E} (hx : x ∈ closedBall c ρ) (hy : y ∈ closedBall c ρ) :
    dist (x - Y (F x)) (y - Y (F y)) ≤ K * dist x y := by
  have hderiv : ∀ z ∈ closedBall c ρ,
      fderiv ℝ (fun z : E => z - Y (F z)) z = ContinuousLinearMap.id ℝ E - Y.comp (F' z) := by
    intro z hz
    exact ((hasFDerivAt_id z).sub (Y.hasFDerivAt.comp z (hdiff z hz))).fderiv
  have hdiff : ∀ z ∈ closedBall c ρ, DifferentiableAt ℝ (fun z : E => z - Y (F z)) z := by
    intro z hz
    exact (differentiableAt_id).sub (Y.differentiableAt.comp z (hdiff z hz).differentiableAt)
  have hnorm : ∀ z ∈ closedBall c ρ, ‖fderiv ℝ (fun z : E => z - Y (F z)) z‖ ≤ K := by
    intro z hz
    rw [hderiv z hz]
    exact hbound z hz
  have hkey : ‖(y - Y (F y)) - (x - Y (F x))‖ ≤ K * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hnorm (convex_closedBall c ρ) hx hy
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (x - Y (F x)) (y - Y (F y)), norm_sub_rev x y]
  exact hkey

/-- **供给导数版的完整解析链**：`F'` 是 `F` 的导数（在球上）+ 算子界 + 残差界
⇒ 球内唯一根。与 `krawczyk_banach_of_deriv_bound` 完全等价，但导数前提显式可审计。 -/
theorem krawczyk_banach_of_hasFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : E → E) (F' : E → E →L[ℝ] E) (Y : E →L[ℝ] E)
    (hY : Function.Injective Y) (c : E) (ρ K : ℝ) (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ closedBall c ρ, HasFDerivAt F (F' x) x)
    (hbound : ∀ x ∈ closedBall c ρ, ‖ContinuousLinearMap.id ℝ E - Y.comp (F' x)‖ ≤ K)
    (hres : dist c (c - Y (F c)) + K * ρ < ρ) :
    ∃! x : E, x ∈ closedBall c ρ ∧ F x = 0 :=
  krawczyk_banach F Y hY c ρ K hρ hK0 hK1
    (fun _ hx _ hy => lipschitzOn_ball_of_hasFDeriv F F' Y c ρ K hdiff hbound hx hy) hres

/-- **G1 的显式义务形式（源系统 `TCSystem`）**：`J` = 源文的块 Jacobian
`[∂f/∂z, 0; −ΣλᵢHᵢ, −J_f^T]` 的**供给对象**；只需
`∀ x ∈ B(c,ρ), HasFDerivAt TCSystem (J x) x` 与逐元素包络的行和界。 -/
theorem TCSystem_unique_root_of_hasFDeriv {c : Fin 12 → ℝ} {ρ K : ℝ}
    (J : (Fin 12 → ℝ) → (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ))
    (Y : (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ)) (hY : Function.Injective Y)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ closedBall c ρ, HasFDerivAt TCSystem (J x) x)
    (lo hi : Fin 12 → Fin 12 → ℝ)
    (henc : ∀ x ∈ closedBall c ρ, ∀ i j : Fin 12,
      lo i j ≤ (ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (J x)) (Pi.single j 1) i ∧
        (ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (J x)) (Pi.single j 1) i ≤ hi i j)
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12, max |lo i j| |hi i j| ≤ K)
    (hres : dist c (c - Y (TCSystem c)) + K * ρ < ρ) :
    ∃! x : Fin 12 → ℝ, x ∈ closedBall c ρ ∧ TCSystem x = 0 :=
  krawczyk_banach_of_hasFDeriv TCSystem J Y hY c ρ K hρ hK0 hK1 hdiff
    (fun x hx => opNorm_le_of_entry_bounds _ hK0 lo hi (fun i j => henc x hx i j) hsum) hres

end N11Formalization
