import N11Formalization.FlashLocalFrobeniusGain

/-!
# FlashLocal — 120 局部叶承重链 · 第十五环：**用 G 的 Frobenius 证书消掉 `hgate`**

Lead 2026-09-30 指定：源脚本的 gate 本来就是
`τ · B · ‖G‖_F · ρ < 1`（`ρ` = local ball 半径），不是待付黑箱门。
本件把 `hgate : τ·B·p < 1`（`p = ‖Gᵀx‖`）从**实际 `Gmat` 的 Frobenius 证书**导出：

1. `sum_sq_mul_le_frobenius`（通用）：`Σ_a (Σ_i G_ia x_i)² ≤ (Σ_iΣ_a G_ia²)·(Σ_i x_i²)`
   —— 逐列 Cauchy-Schwarz（与 `bilinear_frobenius_le` 同一引擎）；
2. `gtX_norm_le_frobenius`：`Σ_{i,a} Gmat² ≤ g²`、`p² = Σ_a (Gᵀx)_a²`、`q² = Σ x²`
   ⇒ `p ≤ g·q`（scalar matrix 作用范数 ≤ Frobenius）；
3. `local_gain_actual_frobenius_gate`：把 `local_gain_actual_frobenius` 的 `hgate` 换成
   源形状的 `hgFrob : Σ_{i,a} Gmat² ≤ (15363/10⁶)²`；由 `q ≤ 729/50000` 精确 `norm_num`
   得 `1468·(99/200)·(15363/10⁶)·(729/50000) < 1`，从而 `τ·B·p < 1`。

**边界**：`hgFrob` 仍是**源区间证书的有限数字义务**（未付）；`hρ/hfluxα/hresp/hCfrob/hFsq/
hcSym/hcDom` 与源 α/H/Λ/constants 一律保持显式，**不**因本件而声称已数值付。
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
  N11Formalization.ResumeCoercivityCertificate N11Formalization.ResumePinnedCoercivity

/-- **通用 Frobenius 作用界**：`Σ_a (Σ_i G_ia x_i)² ≤ (Σ_iΣ_a G_ia²)·(Σ_i x_i²)`。
逐列 finite Cauchy-Schwarz。 -/
theorem sum_sq_mul_le_frobenius {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) (x : ι → ℝ) :
    ∑ a, (∑ i, G i a * x i) ^ 2 ≤ (∑ i, ∑ a, G i a ^ 2) * ∑ i, x i ^ 2 := by
  have h : ∀ a, (∑ i, G i a * x i) ^ 2 ≤ (∑ i, G i a ^ 2) * ∑ i, x i ^ 2 :=
    fun a => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (f := fun i => G i a) (g := x)
  calc ∑ a, (∑ i, G i a * x i) ^ 2 ≤ ∑ a, (∑ i, G i a ^ 2) * ∑ i, x i ^ 2 :=
        Finset.sum_le_sum (fun a _ => h a)
    _ = (∑ a, ∑ i, G i a ^ 2) * ∑ i, x i ^ 2 := by rw [Finset.sum_mul]
    _ = (∑ i, ∑ a, G i a ^ 2) * ∑ i, x i ^ 2 := by rw [Finset.sum_comm]

/-- **`p ≤ g·q`**：`g` 是 `Gmat` 的 Frobenius 上界，`p = ‖Gᵀx‖`、`q = ‖x‖`。 -/
theorem gtX_norm_le_frobenius (s : Edge → Fin 9 → ℝ) (D : Edge → Point) (tang : Fin 9 → Point)
    (N : Edge → Fin 4 → ℝ) (x : Fin 9 → ℝ) {g p q : ℝ}
    (hg0 : 0 ≤ g) (hG : ∑ i, ∑ a, (Gmat s D tang N i a) ^ 2 ≤ g ^ 2)
    (hq0 : 0 ≤ q) (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hp0 : 0 ≤ p) (hp2 : p ^ 2 = ∑ a, (GtX s D tang N x a) ^ 2) :
    p ≤ g * q := by
  have h2 : (∑ a, (GtX s D tang N x a) ^ 2)
      ≤ (∑ i, ∑ a, Gmat s D tang N i a ^ 2) * (∑ i, x i ^ 2) := by
    calc (∑ a, (GtX s D tang N x a) ^ 2)
        = ∑ a, (∑ i, Gmat s D tang N i a * x i) ^ 2 := rfl
      _ ≤ (∑ i, ∑ a, Gmat s D tang N i a ^ 2) * (∑ i, x i ^ 2) :=
          sum_sq_mul_le_frobenius (Gmat s D tang N) x
  have h3 : (∑ i, ∑ a, Gmat s D tang N i a ^ 2) * (∑ i, x i ^ 2) ≤ g ^ 2 * q ^ 2 := by
    rw [← hq2]
    exact mul_le_mul_of_nonneg_right hG (sq_nonneg q)
  have hsq : p ^ 2 ≤ g ^ 2 * q ^ 2 := by
    calc p ^ 2 = (∑ a, (GtX s D tang N x a) ^ 2) := hp2
      _ ≤ (∑ i, ∑ a, Gmat s D tang N i a ^ 2) * (∑ i, x i ^ 2) := h2
      _ ≤ g ^ 2 * q ^ 2 := h3
  have h1 : Real.sqrt (p ^ 2) ≤ Real.sqrt (g ^ 2 * q ^ 2) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hp0, Real.sqrt_mul (sq_nonneg g) (q ^ 2), Real.sqrt_sq hg0,
    Real.sqrt_sq hq0] at h1
  exact h1

/-- **实际局部增益（gate 由 G 的 Frobenius 证书导出）**：
与 `local_gain_actual_frobenius` 同結論，但删掉黑箱 `hgate`，换成源形状的
`hgFrob : Σ_{i,a} Gmat² ≤ (15363/10⁶)²`；`q ≤ 729/50000` 直接给 gate 的精确数值检查。 -/
theorem local_gain_actual_frobenius_gate
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    {Rstar q p η : ℝ} (C8 : Matrix (Fin 8) (Fin 8) ℝ)
    (hα : ∀ e, 0 ≤ α e)
    (hgFrob : ∑ i, ∑ a, (Gmat anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N i a) ^ 2 ≤ (15363 / 1000000 : ℝ) ^ 2)
    (hrow : ∀ e, Real.sqrt (∑ a, (N e a) ^ 2) ≤ (99 / 200) * α e)
    (hNcol : ∀ a, ∑ e, N e a = 0)
    (hNbal : ∀ a v, ∑ e, (N e a * incidence e v) • edgeVector U C Z e = 0)
    (hs : ∑ e, α e = 1)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hU : ∀ i, ‖(U + disp θ x) i‖ ≤ 1)
    (hdiag : ∀ j, anchorWeight α j ≤ 2 / 25)
    (hq0 : 0 ≤ q) (hr : q ≤ 729 / 50000) (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform Λα W W)
    (hCfrob : ∑ i, ∑ j, (if i = pidx ∨ j = pidx then 0 else Cmat Λα θ i j) ^ 2
        ≤ (179 / 5000 : ℝ) ^ 2)
    (hFsq : ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2 ≤ (429 / 50000 : ℝ) ^ 2)
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    (hp0 : 0 ≤ p)
    (hp2 : p ^ 2 = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N x a) ^ 2)
    (hη : 0 < η)
    (hcSym : ∀ i j, actualGram pidx Λα ρ θ N U C Z C8 i j
        = actualGram pidx Λα ρ θ N U C Z C8 j i)
    (hcDom : ∀ i, η + ∑ j, |actualGram pidx Λα ρ θ N U C Z C8 i j| ≤
      actualGram pidx Λα ρ θ N U C Z C8 i i
        + |actualGram pidx Λα ρ θ N U C Z C8 i i|) :
    q ^ 2 / 100000 ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  have hp_le : p ≤ (15363 / 1000000 : ℝ) * q :=
    gtX_norm_le_frobenius anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k))
      N x (by norm_num) hgFrob hq0 hq2 hp0 hp2
  have hgate : 1468 * (99 / 200) * p < 1 := by
    calc 1468 * (99 / 200) * p
        ≤ 1468 * (99 / 200) * ((15363 / 1000000 : ℝ) * q) :=
          mul_le_mul_of_nonneg_left hp_le (by norm_num)
      _ ≤ 1468 * (99 / 200) * ((15363 / 1000000 : ℝ) * (729 / 50000)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hr (by norm_num)
      _ < 1 := by norm_num
  exact local_gain_actual_frobenius (α := α) (U := U) (C := C) (Z := Z) θ x ρ (N := N)
    (Rstar := Rstar) (q := q) (p := p) (η := η) pidx (Λα := Λα) C8
    hα hgate hrow hNcol hNbal hs ha hl hU hdiag hq0 hr hq2 hresp hpin hsym hpsd
    hCfrob hFsq hρ hfluxα hp0 hp2 hη hcSym hcDom

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.sum_sq_mul_le_frobenius
#print axioms N11Formalization.FlashLocal.gtX_norm_le_frobenius
#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius_gate
