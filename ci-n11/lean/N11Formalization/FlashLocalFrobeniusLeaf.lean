import N11Formalization.FlashLocalFrobeniusPinGate
import N11Formalization.ResumeIntervalCoercivity

/-!
# FlashLocal — 120 局部叶承重链 · 第十六环：**新 leaf 消费者**（消 hU、定义 q/p、interval dominance）

按 Lead 2026-09-30 指示（三处替换，一个真实消费者，不新增重复 wrapper 链）：

1. **(a) 消 `hU`**：`hU : ∀ i, ‖(U + disp θ x) i‖ ≤ 1` 换成**源身份**
   `hUeq : ∀ i, U i = circleMap (θ i)`；由 `disp θ x i = circleMap (θ i + x i) − circleMap (θ i)`
   得 `(U + disp θ x) i = circleMap (θ i + x i)`，再用 kernel 的 `circleMap_norm`。
2. **(b) 定义 q/p**：`q := √(Σ_i x_i²)`（= ‖x‖）、`p := √(Σ_a (Gᵀx)_a²)`（= ‖Gᵀx‖），
   `hq0/hq2/hp0/hp2` 全部由 `Real.sqrt_nonneg`/`Real.sqrt_sq` 内部导出，不再作前件。
3. **(c) interval dominance**：`hcDom`（复数不等式）换成源可供给的**有理区间外向包含**：
   `B8 : Fin 8 → Fin 8 → RatInterval`、`η : ℚ`、`hmem : ∀ i j, RatInterval.Mem (B8 i j) (actualGram … i j)`、
   `hintrow : ∀ i, η + Σ_{j≠i} (B8 i j).abs.hi ≤ (B8 i i).lo`；
   经已核 `ResumeIntervalCoercivity.dominance_of_intervals` 导出 `hcDom`（成员资格不可省略）。
   同时 `hcSym`（8×8 同余矩阵对称）**不再是前件**：由 `hsym`（Λ 对称）经
   `H0mat_symm`/`augmented_symm`/`transpose_mul_mul_symm` 内部导出。

`hgFrob`（pinned 8 行 G 的 Frobenius 证书，source `k.G8` 形状：`Σ_{k:Fin8}Σ_a Gmat(pidx.succAbove k)a² ≤ (15363/10⁶)²`，
经 `sum_delete_pin` + Cauchy 给 `p ≤ g·q`）与 `hCfrob/hFsq`（flux/Cmat Frobenius 证书）保持显式未付；
源 α/H/Λ/constants 与 hρ/hfluxα/hresp 等身份一律显式未付。
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
  N11Formalization.ResumeIntervalCoercivity

/-- `H0mat` 在 `Λ` 对称时对称。 -/
theorem H0mat_symm {ι : Type*} [DecidableEq ι] (Λ : ι → ι → ℝ) (a : ι → ℝ) (J : ι → Point)
    (hsym : ∀ i j, Λ i j = Λ j i) :
    ∀ i j, H0mat Λ a J i j = H0mat Λ a J j i := by
  intro i j
  unfold H0mat
  rw [hsym i j, (real_inner_comm (J i) (J j)).symm]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `augmented (H + 2t GGᵀ − μI)` 在 `H` 对称时对称（`GGᵀ` 与对角项自动对称）。 -/
theorem augmented_symm {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (H : ι → ι → ℝ) (G : ι → κ → ℝ) (t μ : ℝ) (hH : ∀ i j, H i j = H j i) :
    ∀ i j, augmented H G t μ i j = augmented H G t μ j i := by
  intro i j
  unfold augmented
  have hsum : (∑ a, G i a * G j a) = ∑ a, G j a * G i a :=
    Finset.sum_congr rfl (fun a _ => by ring)
  rw [hH i j, hsum]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `M` 对称 ⇒ `CᵀMC` 对称（任意 `C`）。 -/
theorem transpose_mul_mul_symm {ι : Type*} [Fintype ι] (M C : Matrix ι ι ℝ)
    (hM : ∀ i j, M i j = M j i) :
    ∀ i j, (C.transpose * M * C) i j = (C.transpose * M * C) j i := by
  have hMt : M.transpose = M := by
    ext i j
    simpa [Matrix.transpose_apply] using hM j i
  have hQ : (C.transpose * M * C).transpose = C.transpose * M * C := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hMt, Matrix.mul_assoc]
  intro i j
  have h := congrArg (fun N : Matrix ι ι ℝ => N i j) hQ
  simpa [Matrix.transpose_apply] using h.symm

/-- **(a) 圆周身份 ⇒ `hU`**：`U i = circleMap (θ i)` 时
`(U + disp θ x) i = circleMap (θ i + x i)`，故范数为 1。 -/
theorem hU_of_circle {U : Fin 9 → Point} {θ x : Fin 9 → ℝ}
    (hUeq : ∀ i, U i = circleMap (θ i)) :
    ∀ i, ‖(U + disp θ x) i‖ ≤ 1 := by
  intro i
  have h1 : (U + disp θ x) i = circleMap (θ i + x i) := by
    simp only [Pi.add_apply, disp, hUeq i]
    module
  rw [h1]
  simp [circleMap_norm]

/-- **新 leaf 消费者**：消 `hU`（改为 `hUeq`）、定义 q/p、`hcDom` 由 interval dominance 导出；
其余前件（`hα/hgFrob/hrow/hNcol/hNbal/hs/ha/hl/hdiag/hr/hresp/hpin/hsym/hpsd/hCfrob/hFsq/hρ/hfluxα`）
保持显式。结论：`(Σx²)/100000 ≤ V2(U + disp θ x) − R*²`。 -/
theorem local_gain_actual_frobenius_leaf
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (θ x ρ : Fin 9 → ℝ) {N : Edge → Fin 4 → ℝ} (pidx : Fin 9) {Λα : Fin 9 → Fin 9 → ℝ}
    {Rstar : ℝ} (C8 : Matrix (Fin 8) (Fin 8) ℝ)
    (B8 : Fin 8 → Fin 8 → RatInterval) (η : ℚ)
    (hα : ∀ e, 0 ≤ α e)
    (hgFrob : ∑ k : Fin 8, ∑ a, (Gmat anchorIncidence (edgeVector U C Z)
        (fun k => circleTangent (θ k)) N (pidx.succAbove k) a) ^ 2
        ≤ (15363 / 1000000 : ℝ) ^ 2)
    (hrow : ∀ e, Real.sqrt (∑ a, (N e a) ^ 2) ≤ (99 / 200) * α e)
    (hNcol : ∀ a, ∑ e, N e a = 0)
    (hNbal : ∀ a v, ∑ e, (N e a * incidence e v) • edgeVector U C Z e = 0)
    (hs : ∑ e, α e = 1)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = Rstar ^ 2)
    (hUeq : ∀ i, U i = circleMap (θ i))
    (hdiag : ∀ j, anchorWeight α j ≤ 2 / 25)
    (hr : Real.sqrt (∑ i, x i ^ 2) ≤ 729 / 50000)
    (hresp : ∀ W : Fin 9 → Point, Eform Λα W W = dirichletEnergy α W)
    (hpin : x pidx = 0) (hsym : ∀ i j, Λα i j = Λα j i)
    (hpsd : ∀ W : Fin 9 → Point, 0 ≤ Eform Λα W W)
    (hCfrob : ∑ i, ∑ j, (if i = pidx ∨ j = pidx then 0 else Cmat Λα θ i j) ^ 2
        ≤ (179 / 5000 : ℝ) ^ 2)
    (hFsq : ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2 ≤ (429 / 50000 : ℝ) ^ 2)
    (hρ : ∀ i, 0 ≤ ρ i) (hfluxα : ∀ i, flux α U C Z i = ρ i • circleMap (θ i))
    (hη : 0 < η)
    (hmem : ∀ i j, RatInterval.Mem (B8 i j) (actualGram pidx Λα ρ θ N U C Z C8 i j))
    (hintrow : ∀ i, η + (∑ j, if j = i then 0 else (B8 i j).abs.hi) ≤ (B8 i i).lo) :
    (∑ i, x i ^ 2) / 100000 ≤ V2 (U + disp θ x) - Rstar ^ 2 := by
  have hsx : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hgy : 0 ≤ ∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have hq0 : 0 ≤ Real.sqrt (∑ i, x i ^ 2) := Real.sqrt_nonneg _
  have hq2 : (Real.sqrt (∑ i, x i ^ 2)) ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hsx
  have hp0 : 0 ≤ Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2) := Real.sqrt_nonneg _
  have hp2 : (Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2)) ^ 2
      = ∑ a, (GtX anchorIncidence (edgeVector U C Z)
          (fun k => circleTangent (θ k)) N x a) ^ 2 := Real.sq_sqrt hgy
  have hH0 : ∀ i j, H0mat Λα ρ (fun k => circleTangent (θ k)) i j
      = H0mat Λα ρ (fun k => circleTangent (θ k)) j i :=
    H0mat_symm _ _ _ hsym
  have hMsym : ∀ i j, actualAugmented pidx Λα ρ θ N U C Z i j
      = actualAugmented pidx Λα ρ θ N U C Z j i :=
    augmented_symm _ _ _ _ (fun i j => hH0 (pidx.succAbove i) (pidx.succAbove j))
  have hcSym : ∀ i j, actualGram pidx Λα ρ θ N U C Z C8 i j
      = actualGram pidx Λα ρ θ N U C Z C8 j i :=
    transpose_mul_mul_symm (actualAugmented pidx Λα ρ θ N U C Z) C8 hMsym
  have hcd : ∀ i, (η : ℝ) + ∑ j, |actualGram pidx Λα ρ θ N U C Z C8 i j| ≤
      actualGram pidx Λα ρ θ N U C Z C8 i i
        + |actualGram pidx Λα ρ θ N U C Z C8 i i| :=
    dominance_of_intervals (actualGram pidx Λα ρ θ N U C Z C8) B8 η hmem hintrow
  have h := local_gain_actual_frobenius_pin_gate (α := α) (U := U) (C := C) (Z := Z)
    θ x ρ (N := N) (Rstar := Rstar) (q := Real.sqrt (∑ i, x i ^ 2))
    (p := Real.sqrt (∑ a, (GtX anchorIncidence (edgeVector U C Z)
      (fun k => circleTangent (θ k)) N x a) ^ 2))
    (η := (η : ℝ)) pidx (Λα := Λα) C8
    hα hgFrob hrow hNcol hNbal hs ha hl (hU_of_circle hUeq) hdiag hq0 hr hq2 hresp hpin hsym
    hpsd hCfrob hFsq hρ hfluxα hp0 hp2 (by exact_mod_cast hη) hcSym hcd
  rw [hq2] at h
  exact h

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.hU_of_circle
#print axioms N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf
#check @N11Formalization.FlashLocal.local_gain_actual_frobenius_leaf
