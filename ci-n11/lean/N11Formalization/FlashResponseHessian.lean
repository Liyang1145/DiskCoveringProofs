import Mathlib
import N11Formalization.ResumeResponseGram
import N11Formalization.ResumeHarmonicResponse

/-!
# FlashResponseHessian — source `H` (L91–95) 与 `FlashLocal.H0mat` 的**矩阵身份**，
以及它与真实 radial flux / response（`response α K`、`edge_lift`）的等价形式

flash-tiling 独占新件。**不做数值**；完整 type + 推导；一般 lemma（任意 `Fintype ι`）。

## 两个对象（逐字读入定义）

source `interval_network_envelope.py` L91–95：非对角 `H_ij = 2 Λ_ij ⟪U_i,U_j⟫`，对角由**行和为零**定义。
`FlashLocal.H0mat Λ a J i j = 2 * (Λ i j * ⟪J_i,J_j⟫ − δ_ij a_i)`（源文档 L29）。

## 推导（唯一要用的代数）

取 `J := U`。非对角两者恒等；对角用 `⟪J_i,J_i⟫ = ‖J_i‖²` 把 `Λ_ii‖J_i‖²` 并回 `j = i` 项，得
`hsrc_ii − H0mat_ii = −2 · rowsum_i`，`rowsum_i := Σ_j Λ_ij ⟪J_i,J_j⟫ − a_i`。于是：
1. `hsrc` 每行和恒 0；2. `hsrc = H0mat ⟺ ∀ i, rowsum_i = 0`；3. `½xᵀhsrc x = ½xᵀH0mat x − Σ_i rowsum_i x_i²`。

`rowsum_i = 0`（= 旋转方向为 H 的零方向）在真实构型里**不是自动的**（source 的 α 只满足 4 条选定角行
+ 归一化），故 **source `H` 与 `H0mat` 的等式是 conditional 的**；末节把该条件写成**真实边向量上的 9 条
通量恒等式**（用 `response` 与 `ResumeHarmonic.edge_lift`），下游据此**不必再具名 `hH0`**。

无 sorry / 自定义 axiom / native_decide。
-/

namespace N11Formalization.FlashResponseHessian

noncomputable section

open Finset
open N11Formalization FlashLocal ResumeNetwork ResumeDirichlet ResumeResponseGram ResumeHarmonic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **source L91–95 的 `H`**：非对角 `2 Λ_ij ⟪J_i,J_j⟫`，对角 = 负的非对角行和（行和恒 0）。 -/
def hsrc (Λ : ι → ι → ℝ) (J : ι → Point) : ι → ι → ℝ :=
  fun i j => if i = j then -(∑ j' ∈ Finset.univ.erase i, 2 * Λ i j' * inner ℝ (J i) (J j'))
    else 2 * Λ i j * inner ℝ (J i) (J j)

/-- 对角项。 -/
theorem hsrc_self (Λ : ι → ι → ℝ) (J : ι → Point) (i : ι) :
    hsrc Λ J i i = -(∑ j ∈ Finset.univ.erase i, 2 * Λ i j * inner ℝ (J i) (J j)) := by
  simp [hsrc]

/-- 非对角项（`j ≠ i`）。 -/
theorem hsrc_off {Λ : ι → ι → ℝ} {J : ι → Point} {i j : ι} (hij : j ≠ i) :
    hsrc Λ J i j = 2 * Λ i j * inner ℝ (J i) (J j) := by
  simp [hsrc, if_neg (Ne.symm hij)]

/-- source `H` 的每一行和恒为 `0`（这正是它对角线的定义内容）。 -/
theorem hsrc_rowsum (Λ : ι → ι → ℝ) (J : ι → Point) (i : ι) :
    ∑ j, hsrc Λ J i j = 0 := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset ι) (hsrc Λ J i) (Finset.mem_univ i)]
  have hoff : ∑ j ∈ Finset.univ.erase i, hsrc Λ J i j
      = ∑ j ∈ Finset.univ.erase i, 2 * Λ i j * inner ℝ (J i) (J j) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    exact hsrc_off (Finset.mem_erase.mp hj).1
  rw [hsrc_self, hoff]
  ring

/-- 逐点形式：`H0mat = hsrc + 对角修正`，修正量正是 `2 * rowsum_i`。 -/
theorem H0mat_eq_hsrc_add (Λ : ι → ι → ℝ) (a : ι → ℝ) (J : ι → Point) (i j : ι) :
    H0mat Λ a J i j
      = hsrc Λ J i j
        + (if i = j then 2 * ((∑ j', Λ i j' * inner ℝ (J i) (J j')) - a i) else 0) := by
  by_cases hij : i = j
  · subst hij
    have hsplit : (∑ j ∈ Finset.univ.erase i, 2 * Λ i j * inner ℝ (J i) (J j))
        = (∑ j, 2 * Λ i j * inner ℝ (J i) (J j)) - 2 * Λ i i * inner ℝ (J i) (J i) := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
        (fun j => 2 * Λ i j * inner ℝ (J i) (J j)) (Finset.mem_univ i)]
      ring
    have hS : (∑ j, 2 * Λ i j * inner ℝ (J i) (J j))
        = 2 * ∑ j, Λ i j * inner ℝ (J i) (J j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hself : inner ℝ (J i) (J i) = ‖J i‖ ^ 2 := real_inner_self_eq_norm_sq (J i)
    rw [hsrc_self, hsplit, hS, if_pos rfl, H0mat, if_pos rfl, hself]
    ring
  · rw [hsrc_off (Ne.symm hij), if_neg hij, add_zero, H0mat, if_neg hij]
    ring

/-- **行和判据**：`hsrc = H0mat` ⟺ `∀ i, Σ_j Λ_ij ⟪J_i,J_j⟫ = a i`（即 `H0mat` 行和为 0）。 -/
theorem hsrc_eq_H0mat_iff (Λ : ι → ι → ℝ) (a : ι → ℝ) (J : ι → Point) :
    hsrc Λ J = H0mat Λ a J ↔ ∀ i, (∑ j, Λ i j * inner ℝ (J i) (J j)) = a i := by
  constructor
  · intro h i
    have hrow : ∑ j, H0mat Λ a J i j = 0 := by
      rw [← h]
      exact hsrc_rowsum Λ J i
    have hsplit : ∑ j, H0mat Λ a J i j
        = 2 * ((∑ j, Λ i j * inner ℝ (J i) (J j)) - a i) := by
      have h1 : ∑ j, H0mat Λ a J i j
          = ∑ j ∈ Finset.univ.erase i, 2 * (Λ i j * inner ℝ (J i) (J j))
            + 2 * (Λ i i * inner ℝ (J i) (J i) - a i) := by
        rw [← Finset.sum_erase_add (Finset.univ : Finset ι) (H0mat Λ a J i) (Finset.mem_univ i)]
        congr 1
        · refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [H0mat, if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]
          ring
        · rw [H0mat, if_pos rfl]
      have h2 : ∑ j ∈ Finset.univ.erase i, 2 * (Λ i j * inner ℝ (J i) (J j))
          = (∑ j, 2 * (Λ i j * inner ℝ (J i) (J j))) - 2 * (Λ i i * inner ℝ (J i) (J i)) := by
        rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
          (fun j => 2 * (Λ i j * inner ℝ (J i) (J j))) (Finset.mem_univ i)]
        ring
      have hS : (∑ j, 2 * (Λ i j * inner ℝ (J i) (J j)))
          = 2 * ∑ j, Λ i j * inner ℝ (J i) (J j) := by
        rw [Finset.mul_sum]
      rw [h1, h2, hS]
      ring
    linarith [hrow, hsplit]
  · intro h
    funext i j
    rw [H0mat_eq_hsrc_add Λ a J i j, h i]
    by_cases hij : i = j <;> simp [hij]

/-- **二次型恒等式**（核心矩阵身份，恒成立、无前件）：
`½ xᵀ hsrc x = ½ xᵀ H0mat x − Σ_i rowsum_i x_i²`。 -/
theorem hsrc_quadform (Λ : ι → ι → ℝ) (a : ι → ℝ) (J : ι → Point) (x : ι → ℝ) :
    (1 / 2) * (∑ i, ∑ j, hsrc Λ J i j * x i * x j)
      = (1 / 2) * (∑ i, ∑ j, H0mat Λ a J i j * x i * x j)
        - ∑ i, ((∑ j, Λ i j * inner ℝ (J i) (J j)) - a i) * x i ^ 2 := by
  have hpt : ∀ i j : ι, H0mat Λ a J i j * x i * x j
      = hsrc Λ J i j * x i * x j
        + (if i = j then 2 * ((∑ j', Λ i j' * inner ℝ (J i) (J j')) - a i) else 0)
            * x i * x j := by
    intro i j
    rw [H0mat_eq_hsrc_add Λ a J i j]
    ring
  have hdiag : ∀ i : ι,
      (∑ j, (if i = j then 2 * ((∑ j', Λ i j' * inner ℝ (J i) (J j')) - a i) else 0)
          * x i * x j)
        = 2 * ((∑ j, Λ i j * inner ℝ (J i) (J j)) - a i) * x i ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      ring
    · intro j _ hj
      rw [if_neg (Ne.symm hj)]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  have houter : (∑ i, ∑ j, H0mat Λ a J i j * x i * x j)
      = (∑ i, ∑ j, hsrc Λ J i j * x i * x j)
        + ∑ i, 2 * ((∑ j, Λ i j * inner ℝ (J i) (J j)) - a i) * x i ^ 2 := by
    simp only [hpt, Finset.sum_add_distrib]
    rw [add_right_inj]
    exact Finset.sum_congr rfl (fun i _ => hdiag i)
  have hD : (∑ i, 2 * ((∑ j, Λ i j * inner ℝ (J i) (J j)) - a i) * x i ^ 2)
      = 2 * ∑ i, ((∑ j, Λ i j * inner ℝ (J i) (J j)) - a i) * x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [houter, hD]
  ring

/-- `J = circleTangent θ` 时的余弦核版本（用 `FlashLocal.tangent_inner_eq`）。 -/
theorem hsrc_quadform_cos (Λ : ι → ι → ℝ) (a θ x : ι → ℝ) :
    (1 / 2) * (∑ i, ∑ j, hsrc Λ (fun k => circleTangent (θ k)) i j * x i * x j)
      = (1 / 2) * (∑ i, ∑ j, H0mat Λ a (fun k => circleTangent (θ k)) i j * x i * x j)
        - ∑ i, ((∑ j, Λ i j * Real.cos (θ i - θ j)) - a i) * x i ^ 2 := by
  have h : ∀ i j : ι, inner ℝ (circleTangent (θ i)) (circleTangent (θ j))
      = Real.cos (θ i - θ j) := fun i j => tangent_inner_eq (θ i) (θ j)
  rw [hsrc_quadform Λ a (fun k => circleTangent (θ k)) x]
  rw [sub_right_inj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hi : (∑ j, Λ i j * inner ℝ (circleTangent (θ i)) (circleTangent (θ j))) - a i
      = (∑ j, Λ i j * Real.cos (θ i - θ j)) - a i :=
    congrArg (fun t => t - a i) (Finset.sum_congr rfl (fun j _ => by rw [h i j]))
  rw [hi]

/-! ## 与真实 radial flux / response / harmonic columns 的等价形式 -/

/-- **Gram 的行和 = 真实边向量上的通量**：
`Σ_e α_e * K_e i * ⟪U_i, Σ_j K_e j • U_j⟫ = Σ_j (response α K) i j * ⟪U_i, U_j⟫`。 -/
theorem rowsum_response_eq_flux (K : Edge → Fin 9 → ℝ) (α : Edge → ℝ) (U : Fin 9 → Point)
    (i : Fin 9) :
    (∑ e, α e * K e i * inner ℝ (U i) (∑ j, K e j • U j))
      = ∑ j, response α K i j * inner ℝ (U i) (U j) := by
  have hperm : (∑ e, α e * K e i * inner ℝ (U i) (∑ j, K e j • U j))
      = ∑ e, ∑ j, α e * K e i * K e j * inner ℝ (U i) (U j) := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_smul_right]
    ring
  rw [hperm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [response, Finset.sum_mul]

/-- **通量形式（含 harmonic columns）**：把 `Σ_j K_e j • U_j` 换成**实际边向量**（`edge_lift`）。 -/
theorem rowsum_response_eq_flux_edge (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (U : Fin 9 → Point)
    (i : Fin 9) :
    (∑ j, response α (ResumeHarmonic.coeff H) i j * inner ℝ (U i) (U j))
      = ∑ e, α e * ResumeHarmonic.coeff H e i *
          inner ℝ (U i) (edgeVector U (fun i' => ResumeHarmonic.lift H U (.inl i'))
            (fun f => ResumeHarmonic.lift H U (.inr f)) e) := by
  rw [← rowsum_response_eq_flux (ResumeHarmonic.coeff H) α U i]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [ResumeHarmonic.edge_lift H U e]

/-- **下游可直接使用的判据（无需再具名 `hH0`）**：source `H`（对 `Λ = response α (coeff H)`）
等于 `H0mat` ⟺ 上述 9 条**真实边向量通量恒等式**成立。 -/
theorem hsrc_eq_H0mat_iff_flux (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (a : Fin 9 → ℝ)
    (U : Fin 9 → Point) :
    hsrc (response α (ResumeHarmonic.coeff H)) U
        = H0mat (response α (ResumeHarmonic.coeff H)) a U
      ↔ ∀ i, (∑ e, α e * ResumeHarmonic.coeff H e i *
          inner ℝ (U i) (edgeVector U (fun i' => ResumeHarmonic.lift H U (.inl i'))
            (fun f => ResumeHarmonic.lift H U (.inr f)) e)) = a i := by
  rw [hsrc_eq_H0mat_iff]
  constructor
  · intro h i
    exact (rowsum_response_eq_flux_edge α H U i).symm.trans (h i)
  · intro h i
    exact (rowsum_response_eq_flux_edge α H U i).trans (h i)

end

end N11Formalization.FlashResponseHessian

#print axioms N11Formalization.FlashResponseHessian.hsrc_rowsum
#print axioms N11Formalization.FlashResponseHessian.H0mat_eq_hsrc_add
#print axioms N11Formalization.FlashResponseHessian.hsrc_eq_H0mat_iff
#print axioms N11Formalization.FlashResponseHessian.hsrc_quadform
#print axioms N11Formalization.FlashResponseHessian.hsrc_quadform_cos
#print axioms N11Formalization.FlashResponseHessian.rowsum_response_eq_flux
#print axioms N11Formalization.FlashResponseHessian.rowsum_response_eq_flux_edge
#print axioms N11Formalization.FlashResponseHessian.hsrc_eq_H0mat_iff_flux
