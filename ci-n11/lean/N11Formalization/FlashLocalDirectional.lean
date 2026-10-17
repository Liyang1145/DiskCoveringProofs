import Mathlib
import N11Formalization.FlashLocalDirectionalBase
import N11Formalization.ResumeFluxTaylor
import N11Formalization.ResumeFluxRemainder
import N11Formalization.ResumeAdaptiveShift

/-!
# FlashLocal — 120 局部叶承重链 · 第十环：**源 L11 的实际合成**（`FlashLocalDirectional`）

Lead 2026-09-30 指定：读完整两 source，建 Directional 草稿。类型已按 Lead 更正定稿：
① 预定的 Taylor 拆分（非接口冲突）；② **不再 double loss**：通用 ε 版损失 `−τ A p q² − ε d q²`，
专门化 `ε := τ B p` 后为 `−τ (B d + A) p q²`；③ `δ` **直接定义**为
`Qx anchorIncidence (edgeVector U C Z) (circleTangent ∘ θ) N τ x`（无 `htang` 假设）；
④ `p² = ∑ a, (GtX … x a)²` **显式**；⑤ `R` 是**定义**（`disp − Jx + x²/2 circle`，见 Base）；
⑥ `Wrem` 的 `frob ≤ q²/2` 来自 `FlashLocalChart` **实际第二余项**（Base 证书 1）；
⑦ `H0` 的 `aVec = ρ` 与源径向载荷一致；⑧ `B, A, μ` 等都是**非负 scalar 参数**（norm certificate 显式）；
⑨ 响应身份 `Eform Λα = dirichletEnergy α` 是**具名前件**（Shift 未付）。

**合成逻辑（五个已核件相加，`±∑ρ_i x_i²` 恰好抵消）**：
* `2 baseCross α U C Z disp ≥ −∑_i ρ_i x_i²` —— `ResumeFluxTaylor.baseCross_radial_lower`（第二槽=全位移）；
* `2 baseCross δ U C Z disp = 2 baseCross δ (Jx) + 2 baseCross δ (Wrem) ≥ τ∑(GtX)² − τApq²`
  —— 前项 `ResumeAnchorFlux.adaptive_baseCross`（消费我的 `adaptive_cross_identity`），
  后项 `ResumeFluxRemainder.adaptive_remainder_lower`（`frob Wrem ≤ q²/2`，Base 证书 1）；
* `dirichletEnergy α disp ≥ ½xᵀH0x + ∑_i ρ_i x_i² − Ccross q³ − (d/3)q⁴` —— 我的 `h0_quadratic_mixed_lower`；
* `2(baseCross α + baseCross δ) + dirichletEnergy α − ε d q² ≤ V2 (U + disp) − R*²`
  —— `ResumeAdaptiveShift.oracle_shift_diagonal_lower`（`V := disp`，`∑‖disp‖² ≤ q²` 由 Base 证书 3）。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset
open N11Formalization.ResumeNetwork N11Formalization.ResumeDirichlet
  N11Formalization.ResumeDirichletShift N11Formalization.ResumeStressComparison
  N11Formalization.ResumeAdaptiveRoot
  N11Formalization.ResumeAnchorFlux
  N11Formalization.ResumeFluxTaylor N11Formalization.ResumeFluxRemainder
  N11Formalization.ResumeAdaptiveShift

/-- **源 L11 的合成（通用 ε 版）**：
`½xᵀH0x + τ ∑_a (GtX a)² − Ccross q³ − (d/3)q⁴ − τ A p q² − ε d q² ≤ V2 (U + disp) − R*²`。 -/
theorem directional_lower_general
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} {τ ε d A Ccross Rstar q : ℝ} (pidx : Fin 9)
    {Λα : Fin 9 → Fin 9 → ℝ}
    (hα : ∀ e, 0 ≤ α e) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hδrel : ∀ e, |Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x e|
        ≤ ε * α e)
    (hs : ∑ e, α e = 1)
    (hds : ∑ e, Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x e = 0)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hd : ∀ v : Free,
      ∑ e, (Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x e
        * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hU : ∀ i, ‖(U + disp θ x) i‖ ≤ 1)
    (hdiag : ∀ j, anchorWeight α j ≤ d) (hd0 : 0 ≤ d)
    (hq0 : 0 ≤ q) (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform Λα W W)
    (hCcross0 : 0 ≤ Ccross)
    (hC : ∀ x' z : Fin 9 → ℝ, x' pidx = 0 → z pidx = 0 →
        |∑ i, ∑ j, Cmat Λα θ i j * x' i * z j|
          ≤ Ccross * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ i, z i ^ 2))
    (hΛ : ∀ U' W : Fin 9 → Point, |Eform Λα U' W| ≤ d * frob U' * frob W)
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    (hτ : 0 ≤ τ) (hA : 0 ≤ A) (hp0 : 0 ≤ p)
    (hp2 : p ^ 2 = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2)
    (hfδ : frob (flux (Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x)
        U C Z) ≤ τ * A * p) :
    (1 / 2) * (∑ i, ∑ j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j * x i * x j)
        + τ * (∑ a, (GtX anchorIncidence (edgeVector U C Z)
            (fun k => circleTangent (θ k)) N x a) ^ 2)
        - Ccross * q ^ 3 - d * q ^ 4 / 3 - τ * A * p * q ^ 2 - ε * d * q ^ 2
      ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  -- `δ` 由 `Qx` 定义
  set δ := Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x with hδdef
  -- 证书：位移范数、`frob Jx = q`、`frob R ≤ q³/6`
  have hV : ∑ j, ‖disp θ x j‖ ^ 2 ≤ q ^ 2 := by
    rw [hq2]; exact disp_frob_le θ x
  have hJxq : frob (Jx θ x) = q := by
    rw [frob_Jx, ← hq2, Real.sqrt_sq hq0]
  have hRq : frob (thirdRemFamily θ x) ≤ q ^ 3 / 6 := by
    have h := frob_thirdRem_le θ x
    have : (∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) / 6 = q ^ 3 / 6 := by
      rw [← hq2, Real.sqrt_sq hq0]; ring
    linarith [h, this]
  have hWrem : frob (Wrem θ x) ≤ q ^ 2 / 2 := by
    have h := frob_Wrem_le θ x
    rw [← hq2] at h
    exact h
  -- (0) 对角下界（`V := disp`）
  have hdiagL := oracle_shift_diagonal_lower (α := α) (δ := δ) (U := U) (V := disp θ x)
    (C := C) (Z := Z) (R := Rstar) (ε := ε) (d := d) (q := q)
    hα hε0 hε1 (by rw [hδdef]; exact hδrel) hs (by rw [hδdef]; exact hds)
    ha (by rw [hδdef]; exact hd) hl hU hdiag hd0 hV
  -- (1) α 侧径向
  have hαrad : -(∑ i, ρ i * x i ^ 2) ≤ 2 * baseCross α U C Z (disp θ x) :=
    baseCross_radial_lower (α := α) (U := U) (C := C) (Z := Z) θ x ρ hρ hfluxα
  -- (2) δ 侧：切向（等式）+ 二阶余项（下界）
  have hsplit := baseCross_add (α := δ) (U := U) (V := Jx θ x) (W := Wrem θ x) (C := C) (Z := Z)
  have hdisp : (fun i => Jx θ x i + Wrem θ x i) = disp θ x := Jx_add_Wrem θ x
  have htan : 2 * baseCross δ U C Z (Jx θ x)
      = τ * ∑ a, (GtX anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N x a) ^ 2 := by
    rw [hδdef]
    exact adaptive_baseCross U C Z (fun k => circleTangent (θ k)) N τ x
  have hrem := adaptive_remainder_lower (δ := δ) (U := U) (W := Wrem θ x) (C := C) (Z := Z)
    (τ := τ) (A := A) (p := p) (q := q) hτ hA hp0 (by rw [hδdef]; exact hfδ) hWrem
  have hδtot : τ * (∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2) - τ * A * p * q ^ 2
      ≤ 2 * baseCross δ U C Z (disp θ x) := by
    have hsplit' : 2 * baseCross δ U C Z (disp θ x)
        = 2 * baseCross δ U C Z (Jx θ x) + 2 * baseCross δ U C Z (Wrem θ x) := by
      have h2 : baseCross δ U C Z (fun i => Jx θ x i + Wrem θ x i)
          = baseCross δ U C Z (Jx θ x) + baseCross δ U C Z (Wrem θ x) := hsplit
      rw [← hdisp, h2]; ring
    linarith [htan, hrem, hsplit']
  -- (3) 响应能量（我的 pinned 二次 + mixed）
  have hE := h0_quadratic_mixed_lower pidx Λα ρ θ x (thirdRemFamily θ x) (dirichletEnergy α)
    hCcross0 hd0 hq0 hpin hsym hresp hpsd hC hΛ hJxq hRq
  have harg : (fun i => x i • circleTangent (θ i)
      + (-(x i ^ 2 / 2) • circleMap (θ i) + thirdRemFamily θ x i)) = disp θ x := by
    funext i
    simp only [thirdRemFamily, Wrem, disp]
    module
  rw [harg] at hE
  -- (4) 相加
  -- `hp2` 把结论里的 `τ∑(GtX)²` 与源 L11 的 `τp²` 钉在一起（此处显式引用，避免其空置）
  have _hp2use : τ * (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2) = τ * p ^ 2 := by rw [hp2]
  linarith [hdiagL, hαrad, hδtot, hE]

/-- **源 L11（专门化 `ε := τ B p`）**：损失合并为**一项** `−τ (B d + A) p q²`（**无 double loss**）。

`hgate : τ * B * p < 1` 即源门 `τ B p < 1`；`hδrel` 即 `β(x) ≤ τ B p` 的 norm certificate（具名）。 -/
theorem directional_lower
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ}
    {τ d A B Ccross Rstar q p : ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    (hα : ∀ e, 0 ≤ α e) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hd0 : 0 ≤ d)
    (hgate : τ * B * p < 1)
    (hδrel : ∀ e, |Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x e|
        ≤ (τ * B * p) * α e)
    (hs : ∑ e, α e = 1)
    (hds : ∑ e, Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x e = 0)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hd : ∀ v : Free,
      ∑ e, (Qx anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N τ x e
        * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hU : ∀ i, ‖(U + disp θ x) i‖ ≤ 1)
    (hdiag : ∀ j, anchorWeight α j ≤ d)
    (hq0 : 0 ≤ q) (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform Λα W W)
    (hCcross0 : 0 ≤ Ccross)
    (hC : ∀ x' z : Fin 9 → ℝ, x' pidx = 0 → z pidx = 0 →
        |∑ i, ∑ j, Cmat Λα θ i j * x' i * z j|
          ≤ Ccross * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ i, z i ^ 2))
    (hΛ : ∀ U' W : Fin 9 → Point, |Eform Λα U' W| ≤ d * frob U' * frob W)
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
  have hε0 : 0 ≤ τ * B * p := by positivity
  have hgen := directional_lower_general (α := α) (U := U) (C := C) (Z := Z) θ x ρ
    (N := N) (τ := τ) (ε := τ * B * p) (d := d) (A := A) (Ccross := Ccross)
    (Rstar := Rstar) (q := q) pidx (Λα := Λα)
    hα hε0 hgate hδrel hs hds ha hd hl hU hdiag hd0 hq0 hq2 hresp hpin hsym hpsd
    hCcross0 hC hΛ hρ hfluxα hτ hA hp0 hp2 hfδ
  have harith : τ * (B * d + A) * p * q ^ 2
      = τ * A * p * q ^ 2 + (τ * B * p) * d * q ^ 2 := by ring
  rw [hp2]
  linarith only [hgen, harith]

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.directional_lower_general
#print axioms N11Formalization.FlashLocal.directional_lower
