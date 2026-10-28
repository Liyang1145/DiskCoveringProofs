import Mathlib
import N11Formalization.FlashResponseHessian
import N11Formalization.ResumeHarmonicResponse

/-!
# FlashResponseHessianFlux — 把 `hsrc = H0mat` 从 iff 重述**闭合为身份**

前置件 `FlashResponseHessian.lean`（已冻结，SHA256 `7FC3CC6E…07A1`）给出
`hsrc = H0mat ↔ ∀ i, Σ_j Λ_ij ⟪J_i,J_j⟫ = a i`。本件按 lead 指定的链把它**闭合成身份**：

1. **`coeff` 核身份**（读真实定义）：`coeff H e i = anchorIncidence e i + Σ_v incidence e v * H v i`，
   其中 `anchorIncidence e i` 是边界边锚点项 `-(if i = anchorIndex k s then 1 else 0)`，面边为 0。
2. **free-node balance ⟹ 通量**：`hbal : ∀ v j, Σ_e (α e * incidence e v) * coeff H e j = 0`
   把 (1) 中的自由节点项整体消掉，得
   `Σ_e α_e * coeff H e i • edgeVector U C Z e = Σ_e α_e * anchorIncidence e i • edgeVector U C Z e`
   （= 只在锚点侧计费的「通量」`flux α U C Z i`）。
3. **`hflux` 与单位性 ⟹ rowsum = ρ_i**：若 `flux α U C Z i = ρ i • U i` 且 `‖U i‖ = 1`，则
   `Σ_j (response α K) i j * ⟪U i, U j⟫ = ρ i`。
4. **旋转保内积 ⟹ 实际 `J` 版**：`⟪circleTangent a, circleTangent b⟫ = ⟪circleMap a, circleMap b⟫`；
   于是把 (3) 的 `U` 版 rowsum 换成实际 `J` 版（`J_i = circleTangent θ_i`），再用前置件的
   `hsrc_eq_H0mat_iff` 得 **`hsrc (response α K) (circleTangent ∘ θ) = H0mat (response α K) ρ (circleTangent ∘ θ)`**
   —— 身份，不再是 iff；且**不留 9 条 flux scalars 作为额外前件**（`hflux` 是单条向量值物理输入）。

无 sorry / 自定义 axiom / native_decide。
-/

namespace N11Formalization.FlashResponseHessianFlux

noncomputable section

open Finset
open N11Formalization FlashLocal ResumeNetwork ResumeDirichlet ResumeResponseGram ResumeHarmonic
open N11Formalization.FlashResponseHessian

/-- 边界边的锚点系数：`.inl (k,s)` 的锚点是 `U (anchorIndex k s)`，取 −1；面边为 0。 -/
def anchorIncidence (e : Edge) (i : Fin 9) : ℝ :=
  match e with
  | .inl (k, s) => -(if i = anchorIndex k s then 1 else 0)
  | .inr _ => 0

/-- **核身份**：`coeff` 分解成「锚点项 + 自由节点 incidence 组合」。 -/
theorem coeff_eq (H : Free → Fin 9 → ℝ) (e : Edge) (i : Fin 9) :
    coeff H e i = anchorIncidence e i + ∑ v : Free, incidence e v * H v i := by
  rcases e with ⟨k, s⟩ | ⟨f, v⟩
  · simp only [coeff, anchorIncidence, incidence, Free, Fintype.sum_sum_type]
    rw [Finset.sum_eq_single (⟨k.val, by omega⟩ : Fin 11),
      Finset.sum_eq_single (⟨k.val, by omega⟩ : Fin 11)]
    all_goals
      first
        | (simp_all [Sum.inr_ne_inl]; try ring)

  · simp only [coeff, anchorIncidence, incidence, Free, Fintype.sum_sum_type]
    rw [Finset.sum_eq_single (face f v), Finset.sum_eq_single f]
    all_goals
      first
        | (simp_all [Sum.inr_ne_inl]; try ring)


/-- **第 2 步：`ha`（free-node balance）消掉 `coeff` 的自由节点部分**，只剩锚点项
（几何取 `ResumeHarmonic.lift` 的 C/Z，正是 `balance_of_columns` 的适用形态）。 -/
theorem flux_reduction (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (U : Fin 9 → Point) (i : Fin 9)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0) :
    (∑ e, (α e * coeff H e i) •
        edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e)
      = ∑ e, (α e * anchorIncidence e i) •
          edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e := by
  have hterm : ∀ e : Edge,
      (α e * coeff H e i) •
          edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e
        = (α e * anchorIncidence e i) •
            edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e
          + ∑ v : Free, (α e * incidence e v * H v i) •
              edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e := by
    intro e
    rw [coeff_eq H e i, mul_add, add_smul, Finset.mul_sum, Finset.sum_smul]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by rw [mul_assoc])
  have hzero : (∑ e, ∑ v : Free, (α e * incidence e v * H v i) •
      edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun v _ => ?_)
    have hv : (∑ e, (α e * incidence e v) •
        edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e) = 0 :=
      balance_of_columns α H hbal U v
    calc (∑ e, (α e * incidence e v * H v i) •
          edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e)
        = H v i • (∑ e, (α e * incidence e v) •
            edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun e _ => by rw [smul_smul]; ring)
      _ = 0 := by rw [hv, smul_zero]
  rw [Finset.sum_congr rfl (fun e _ => hterm e), Finset.sum_add_distrib, hzero, add_zero]

/-- **第 3 步：`hflux`（径向 α）+ 圆单位性 ⟹ 行和 = ρ_i**（`hflux` 是单条向量值物理输入）。 -/
theorem rowsum_eq_rho (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (U : Fin 9 → Point) (ρ : Fin 9 → ℝ)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (hflux : ∀ i, (∑ e, (α e * anchorIncidence e i) •
        edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e) = ρ i • U i)
    (hunit : ∀ i, ‖U i‖ = 1) (i : Fin 9) :
    (∑ j, response α (coeff H) i j * inner ℝ (U i) (U j)) = ρ i := by
  have hfluxvec : (∑ e, (α e * coeff H e i) •
      edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e) = ρ i • U i :=
    (flux_reduction α H U i hbal).trans (hflux i)
  have hinner : inner ℝ (U i) (∑ e, (α e * coeff H e i) •
      edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e)
      = ∑ e, α e * coeff H e i *
          inner ℝ (U i)
            (edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e) := by
    rw [inner_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [real_inner_smul_right]
  rw [rowsum_response_eq_flux_edge α H U i, ← hinner, hfluxvec, real_inner_smul_right,
    real_inner_self_eq_norm_sq (U i), hunit i]
  ring

/-- **旋转保内积**：切向量内积 = 半径内积（同一个余弦核）。 -/
theorem circleTangent_inner_eq_circleMap (a b : ℝ) :
    inner ℝ (circleTangent a) (circleTangent b) = inner ℝ (circleMap a) (circleMap b) := by
  rw [tangent_inner_eq, inner_circleMap]

/-- **第 4 步（闭合）：实际 `J` 版 `hsrc = H0mat`**。
`U_i = circleMap (θ i)` 时余弦核一致，行和条件 `hrow` 直接给出**身份**（不再是 iff 重述）。 -/
theorem hsrc_eq_H0mat_of_flux (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ) (θ ρ : Fin 9 → ℝ)
    (hrow : ∀ i, (∑ j, response α K i j *
        inner ℝ (circleMap (θ i)) (circleMap (θ j))) = ρ i) :
    hsrc (response α K) (fun i => circleTangent (θ i))
      = H0mat (response α K) ρ (fun i => circleTangent (θ i)) := by
  rw [hsrc_eq_H0mat_iff]
  intro i
  have hker : ∀ j : Fin 9, inner ℝ (circleTangent (θ i)) (circleTangent (θ j))
      = inner ℝ (circleMap (θ i)) (circleMap (θ j)) := fun j =>
    circleTangent_inner_eq_circleMap (θ i) (θ j)
  have hsum : (∑ j, response α K i j * inner ℝ (circleTangent (θ i)) (circleTangent (θ j)))
      = (∑ j, response α K i j * inner ℝ (circleMap (θ i)) (circleMap (θ j))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hker j]
  rw [hsum, hrow i]

/-- **真正闭合版**：`ha`(free-node balance) + `hflux`(径向 α) + 单位圆 + 圆几何，直接给
**实际 `J` 版 `hsrc = H0mat`**（**不再以 `hrow` 为前件**：`hrow` 由 `rowsum_eq_rho` 现场推出）。 -/
theorem hsrc_eq_H0mat_closed (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (U : Fin 9 → Point)
    (θ ρ : Fin 9 → ℝ)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (hflux : ∀ i, (∑ e, (α e * anchorIncidence e i) •
        edgeVector U (fun k => lift H U (.inl k)) (fun f => lift H U (.inr f)) e) = ρ i • U i)
    (hunit : ∀ i, ‖U i‖ = 1)
    (hU : ∀ i, U i = circleMap (θ i)) :
    hsrc (response α (coeff H)) (fun i => circleTangent (θ i))
      = H0mat (response α (coeff H)) ρ (fun i => circleTangent (θ i)) := by
  refine hsrc_eq_H0mat_of_flux α (coeff H) θ ρ (fun i => ?_)
  have hrow := rowsum_eq_rho α H U ρ hbal hflux hunit i
  rw [← hrow]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hU i, hU j]

end

end N11Formalization.FlashResponseHessianFlux

#print axioms N11Formalization.FlashResponseHessianFlux.coeff_eq
#print axioms N11Formalization.FlashResponseHessianFlux.flux_reduction
#print axioms N11Formalization.FlashResponseHessianFlux.rowsum_eq_rho
#print axioms N11Formalization.FlashResponseHessianFlux.circleTangent_inner_eq_circleMap
#print axioms N11Formalization.FlashResponseHessianFlux.hsrc_eq_H0mat_of_flux
#print axioms N11Formalization.FlashResponseHessianFlux.hsrc_eq_H0mat_closed
