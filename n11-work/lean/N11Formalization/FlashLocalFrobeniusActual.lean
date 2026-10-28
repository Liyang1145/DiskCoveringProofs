import N11Formalization.FlashLocalFrobenius

/-!
# FlashLocal — 120 局部叶承重链 · 第十三环：**Actual 消费者的 Frobenius 版本**

本件把已核 `FlashLocalDirectionalActual.directional_lower_actual` 的两条黑箱前件
换成源脚本实际可供给的 **Frobenius 有限证书**：

| 原文（黑箱） | 本件替换为 |
|---|---|
| `hC : ∀ x' z, x' p = 0 → z p = 0 → \|Σ_ij Cmat_ij x'_i z_j\| ≤ Ccross·‖x'‖‖z‖` | `hCfrob : Σ_ij (pin 后 Cmat_ij)² ≤ Ccross²`（源脚本 8×8 `cnorm`） |
| `hfδ : frob (flux (Qx …)) ≤ τ·A·p` | `hFsq : Σ_a (frob (flux (fun e => N e a)))² ≤ A²`（源脚本 18×4 `Anorm`） |

替换后仍**保留**其全部其余具名前件（Rows/Balance 真实导出、`hpin/hsym/hpsd/hresp`、
`hfluxα/hρ`、`hdiag/hq2/hp2` 等），并且**不触碰** μ-coercivity 与源 α/H/Λ/constants ——
那些仍显式未付。本件只是把"Frobenius 数字 → operator 常数"这一段接实。

**证据口径**：`hCfrob` 的指标形态是 pin 指标 `p = pidx` 的行列全置零后求和
（`pinned_frobenius_filter_eq` 给出其与 `Finset.univ.filter (· ≠ p)` 上 8×8 求和相等）；
`hFsq` 的族 `F_a` 与源脚本 `flux[i,j]`（18×4）逐列一致，其数值由源 `certify_relative_stress_ball.py`
L20/L24 的区间 `aq/cq` 供给，本件**不声称任何数字**。
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

/-- **Actual L11 下界（Frobenius 版）**：`hδrel/hds/hd` 由 Rows/Balance 导出、`hΛ` 由
`network_response_bound` 导出、`hCcross` 与 `hfδ` 由 Frobenius 有限证书
（`hCfrob`/`hFsq`）导出；其余具名前件与 μ-coercivity/源常数如实保留。 -/
theorem directional_lower_actual_frobenius
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
    -- ③ Frobenius 有限证书（替换 hCcross/hfδ 黑箱；数字由源脚本区间证书供给）
    (hCcross0 : 0 ≤ Ccross)
    (hCfrob : ∑ i, ∑ j, (if i = pidx ∨ j = pidx then 0 else Cmat Λα θ i j) ^ 2
        ≤ Ccross ^ 2)
    (hFsq : ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2 ≤ A ^ 2)
    -- ④ 其余仍显式未付
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    (hA : 0 ≤ A)
    (hp2 : p ^ 2 = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2) :
    (1 / 2) * (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j)
        + τ * p ^ 2
        - Ccross * q ^ 3 - d * q ^ 4 / 3 - τ * (B * d + A) * p * q ^ 2
      ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  have hC : ∀ x' z : Fin 9 → ℝ, x' pidx = 0 → z pidx = 0 →
      |∑ i, ∑ j, Cmat Λα θ i j * x' i * z j|
        ≤ Ccross * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ i, z i ^ 2) :=
    pinned_operator_le_of_frobenius pidx (Cmat Λα θ) hCcross0 hCfrob
  have hfδ : frob (flux (Qx anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N τ x) U C Z) ≤ τ * A * p :=
    frob_flux_Qx_le anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k))
      N τ x U C Z hτ hA hp0 hp2 hFsq
  exact directional_lower_actual (α := α) (U := U) (C := C) (Z := Z) θ x ρ (N := N)
    (τ := τ) (d := d) (A := A) (B := B) (Ccross := Ccross) (Rstar := Rstar) (q := q) (p := p)
    pidx (Λα := Λα) hα hτ hB hp0 hd0 hgate hrow hNcol hNbal hs ha hl hU hdiag hq0 hq2 hresp
    hpin hsym hpsd hCcross0 hC hρ hfluxα hA hp2 hfδ

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.directional_lower_actual_frobenius
