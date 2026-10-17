import Mathlib
import N11Formalization.FlashLocalDirectional
import N11Formalization.ResumeAdaptiveRows
import N11Formalization.ResumeAdaptiveBalance
import N11Formalization.ResumeResponseBound

/-!
# FlashLocal — 120 局部叶承重链 · 第十一环：**Actual consumer**（具名前件换成真实导出）

Lead 2026-09-30 指示：继续 `FlashLocalDirectionalActual`，读真实 Rows/Balance 源；
并用新件 `ResumeResponseBound.network_response_bound`（`hresp + hsym + PSD + anchorWeight ≤ d`）
**导出 full `hΛ`**，故本件**删掉 `hΛ`**（`hCcross` 与所有具名前件保持显式未付）。

**本件把 `FlashLocalDirectional.directional_lower` 的三条具名前件换成真实导出**：
* `hδrel`（`∀e, |Qx … e| ≤ (τBp)·α_e`）← **`ResumeAdaptiveRows.Qx_relative`**（前件 `hrow : ∀e, √(Σ_a N_ea²) ≤ B·α_e`）；
* `hds`（`Σ_e Qx … e = 0`）← **`ResumeAdaptiveRows.Qx_sum_zero`**（前件 `hNcol : ∀a, Σ_e N ea = 0`）；
* `hd`（node-balance 行）← **`ResumeAdaptiveBalance.Qx_balance`**（前件 `hNbal : ∀a v, Σ_e (N ea · incidence e v) • D e = 0`）；
* `hΛ`（full Λ bound）**删除** ← **`ResumeResponseBound.network_response_bound`**（前件 `hsym/hpsd/hresp/anchorWeight ≤ d`）。

**仍然显式未付（不得说"只剩两个缺口"）**：`hCcross`（pinned Cmat operator 常数）、
`hfluxα`（径向 `flux α … = ρ_i • circle θ_i`）、`hfδ`（`frob (flux δ …) ≤ τAp`）、`hresp`
（响应身份，Lead 的 `ResumeResponseGram`）、`hρ/hpin/hsym/hpsd/hdiag/hq2/hp2`，
以及 **μ-coercivity 与源常数（C920 那组）**。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset
open N11Formalization.ResumeNetwork N11Formalization.ResumeDirichlet
  N11Formalization.ResumeDirichletShift N11Formalization.ResumeStressComparison
  N11Formalization.ResumeAdaptiveRoot N11Formalization.ResumeAnchorFlux
  N11Formalization.ResumeAdaptiveRows N11Formalization.ResumeAdaptiveBalance
  N11Formalization.ResumeResponseBound
  N11Formalization.ResumeFluxTaylor N11Formalization.ResumeFluxRemainder
  N11Formalization.ResumeAdaptiveShift

/-- **Actual L11 下界**：`hδrel/hds/hd` 由 Rows/Balance 导出，`hΛ` 由 `network_response_bound` 导出
（不再作为前件）；其余具名前件如实保留。 -/
theorem directional_lower_actual
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ}
    {τ d A B Ccross Rstar q p : ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    (hα : ∀ e, 0 ≤ α e) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hd0 : 0 ≤ d)
    (hgate : τ * B * p < 1)
    -- ① 每列有限证书（Rows/Balance 的真实前件）
    (hrow : ∀ e, Real.sqrt (∑ a, (N e a) ^ 2) ≤ B * α e)
    (hNcol : ∀ a, ∑ e, N e a = 0)
    (hNbal : ∀ a v, ∑ e, (N e a * incidence e v) • edgeVector U C Z e = 0)
    (hs : ∑ e, α e = 1)
    -- α 侧节点平衡（balanced base；仍显式未付）
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hU : ∀ i, ‖(U + disp θ x) i‖ ≤ 1)
    (hdiag : ∀ j, anchorWeight α j ≤ d)
    (hq0 : 0 ≤ q) (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    -- ② 响应身份（**具名**，Lead 的 ResumeResponseGram）
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform Λα W W)
    -- ③ 仍显式未付
    (hCcross0 : 0 ≤ Ccross)
    (hC : ∀ x' z : Fin 9 → ℝ, x' pidx = 0 → z pidx = 0 →
        |∑ i, ∑ j, Cmat Λα θ i j * x' i * z j|
          ≤ Ccross * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ i, z i ^ 2))
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    (hA : 0 ≤ A)
    (hp2 : p ^ 2 = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2)
    (hfδ : frob (flux (Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x)
        U C Z) ≤ τ * A * p) :
    (1 / 2) * (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j)
        + τ * p ^ 2
        - Ccross * q ^ 3 - d * q ^ 4 / 3 - τ * (B * d + A) * p * q ^ 2
      ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  -- `δ` 侧三条由 Rows / Balance 导出
  have hδrel : ∀ e, |Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k))
      N τ x e| ≤ (τ * B * p) * α e :=
    Qx_relative anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N x α
      hτ hp0 hp2 hrow
  have hds : ∑ e, Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x e = 0 :=
    Qx_sum_zero anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N x τ hNcol
  have hdb : ∀ v : Free, ∑ e, (Qx anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N τ x e * incidence e v) • edgeVector U C Z e = 0 :=
    fun v => Qx_balance anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N x τ
      hNbal v
  -- `hΛ` 由 ResponseBound 导出（本体删除该前件）
  have hΛ : ∀ U' W : Fin 9 → Point, |Eform Λα U' W| ≤ d * frob U' * frob W :=
    fun U' W => network_response_bound α Λα d hd0 hα hsym hpsd hresp hdiag U' W
  -- 交给已验证的合成
  exact directional_lower (α := α) (U := U) (C := C) (Z := Z) θ x ρ (N := N)
    (τ := τ) (d := d) (A := A) (B := B) (Ccross := Ccross) (Rstar := Rstar) (q := q) (p := p)
    pidx (Λα := Λα) hα hτ hB hp0 hd0 hgate hδrel hs hds ha hdb hl hU hdiag hq0 hq2 hresp
    hpin hsym hpsd hCcross0 hC hΛ hρ hfluxα hA hp2 hfδ

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.directional_lower_actual
