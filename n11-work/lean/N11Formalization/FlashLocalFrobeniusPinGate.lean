import N11Formalization.FlashLocalFrobeniusGate
import N11Formalization.ResumePinnedCoercivity

/-!
# FlashLocal — 120 局部叶承重链 · 第十七环：**pinned G 范数版 gate**（source 形状）

Lead 2026-09-30 纠正（读 `certify_relative_stress_ball.py` L9/L25）：
源 `G = k.G8 * R` 是 **raw8 pinned** 的 8×4 矩阵，`gnorm = √(Σ_{i<8, a} G_ia²)`
**只对 8 行求和**；因此 **不能**要求 full `Fin 9` 的 `Σ_iΣ_a Gmat² ≤ (15363/10⁶)²`
（source 不保证）。正确接法：

* `hgFrob` 只对 **pinned** 行求和：`Σ_{k:Fin 8} Σ_a (Gmat (pidx.succAbove k) a)² ≤ g²`；
* `(Gᵀx)_a = Σ_i G_ia x_i = Σ_{k:Fin 8} G (pidx.succAbove k) a · x (pidx.succAbove k)`
  由 `ResumePinnedCoercivity.sum_delete_pin`（利用 `x pidx = 0`）得到，**不重标 source 常数**；
* 再对 8 维向量做 Cauchy-Schwarz（`sum_sq_mul_le_frobenius`）⇒ `p ≤ g·q`。

本件两个定理：`gtX_norm_le_frobenius_pinned`（通用 `Fin (n+1)`）与
`local_gain_actual_frobenius_pin_gate`（gate 版的 pinned 替换；其余前件与 gate 版相同）。
旧 `FlashLocalFrobeniusGate` 的 full-9 前提比 source 供给强，保留为记录但**不作为源形状接口**。
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

/-- **pinned `p ≤ g·q`**：`g` 只界 pinned 8 行的 `Gmat` Frobenius 平方和；
`(Gᵀx)_a` 的 full 9 行和经 `sum_delete_pin`（需要 `x p = 0`）化为 8 行和后再 Cauchy。 -/
theorem gtX_norm_le_frobenius_pinned {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin (n + 1)) (G : Fin (n + 1) → κ → ℝ) (x : Fin (n + 1) → ℝ) {g pY q : ℝ}
    (hg0 : 0 ≤ g) (hG : ∑ k : Fin n, ∑ a, (G (p.succAbove k) a) ^ 2 ≤ g ^ 2)
    (hq0 : 0 ≤ q) (hq2 : q ^ 2 = ∑ i, x i ^ 2)
    (hp0 : 0 ≤ pY) (hp2 : pY ^ 2 = ∑ a, (∑ i, G i a * x i) ^ 2)
    (hx : x p = 0) :
    pY ≤ g * q := by
  have hsum : ∀ a, (∑ i, G i a * x i)
      = ∑ k : Fin n, G (p.succAbove k) a * x (p.succAbove k) :=
    fun a => sum_delete_pin p _ (by simp [hx])
  have hsum2 : (∑ i, x i ^ 2) = ∑ k : Fin n, x (p.succAbove k) ^ 2 :=
    sum_delete_pin p _ (by simp [hx])
  have hCS := sum_sq_mul_le_frobenius (fun k : Fin n => G (p.succAbove k))
    (fun k : Fin n => x (p.succAbove k))
  have hsq : pY ^ 2 ≤ g ^ 2 * q ^ 2 := by
    calc pY ^ 2 = ∑ a, (∑ i, G i a * x i) ^ 2 := hp2
      _ = ∑ a, (∑ k : Fin n, G (p.succAbove k) a * x (p.succAbove k)) ^ 2 := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [hsum a]
      _ ≤ (∑ k : Fin n, ∑ a, (G (p.succAbove k) a) ^ 2)
            * (∑ k : Fin n, x (p.succAbove k) ^ 2) := hCS
      _ ≤ g ^ 2 * q ^ 2 := by
          rw [hq2, ← hsum2]
          exact mul_le_mul_of_nonneg_right hG (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))
  have h1 : Real.sqrt (pY ^ 2) ≤ Real.sqrt (g ^ 2 * q ^ 2) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hp0, Real.sqrt_mul (sq_nonneg g) (q ^ 2), Real.sqrt_sq hg0,
    Real.sqrt_sq hq0] at h1
  exact h1

/-- **pinned-G gate 版实际局部增益**：与 `local_gain_actual_frobenius_gate` 同結論，
但 `hgFrob` 改为 pinned 8 行形状（source `k.G8`），由 `sum_delete_pin` + Cauchy 给 `p ≤ g·q`。 -/
theorem local_gain_actual_frobenius_pin_gate
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    {Rstar q p η : ℝ} (C8 : Matrix (Fin 8) (Fin 8) ℝ)
    (hα : ∀ e, 0 ≤ α e)
    (hgFrob : ∑ k : Fin 8, ∑ a, (Gmat anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N (pidx.succAbove k) a) ^ 2 ≤ (15363 / 1000000 : ℝ) ^ 2)
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
    gtX_norm_le_frobenius_pinned pidx
      (Gmat anchorIncidence (edgeVector U C Z) (fun k => circleTangent (θ k)) N) x
      (by norm_num) hgFrob hq0 hq2 hp0 hp2 hpin
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

#print axioms N11Formalization.FlashLocal.gtX_norm_le_frobenius_pinned
#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius_pin_gate
