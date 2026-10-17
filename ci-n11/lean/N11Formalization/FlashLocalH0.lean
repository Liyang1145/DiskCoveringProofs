import Mathlib
import N11Formalization.FlashLocalMix

/-!
# FlashLocal — 120 局部叶承重链 · 第五环：源 `H0` 与**实际 circle-Taylor 能量二次项**的连接

源 `team-current/lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md` 第 21/29 行：

```
21. F(x)=E_alpha(x)(U(x))=R*^2+2<l0+Mx,delta>+<delta,Lambda_alpha(x)delta>.
29. Likewise H0=2[J_U^T (Lambda0 tensor I2) J_U - diag(a_0,...,a_7)], by differentiating
    E_alpha0(U(x)); hence its quadratic term is exactly half x^T H0 x.
```

Lead（2026-09-30）要求：**不只做 H0 的定义等式（纯 ring 展开收益低），必须用实际
circle-Taylor / 能量二次项把它接上**；`Λ0` 的 response 若未给，**显式 conditional**，
不伪装已付。本件按此做三件事：

1. `Eform Λ U V := Σ_{i,j} Λ_ij ⟪U_i,V_j⟫` —— 即 `(Λ0 ⊗ I₂)` 作用在 ℝ² 值族上的二次/双线性型；
   `frob U` = 族上的 Frobenius 范数（与第一环 `anchorRemainder_frob_norm_le` **同一个量**）。
2. **H0 ⟷ 实际图的一次运动**：`V i := x_i • circleTangent (θ_i)`（= 源 `v_i = J U0_i x_i`，**真实切向**），
   `Eform Λ V V = ½ xᵀH0x + Σ_i a_i x_i²`（`h0_eq_response`）。
   其中 `⟪circleTangent θ_i, circleTangent θ_j⟫ = cos(θ_i − θ_j)`（`tangent_inner_eq`）
   ⇒ `H0_ij = 2(Λ_ij cos(θ_i−θ_j) − δ_ij a_i)`，即**边系数 × 余弦核**（`h0_eq_cosine`）。
3. **circle-Taylor 余项接入**：真实锚位移 `δ = V + W`（`W := δ − V`，第一环给 `frob W ≤ q²/2`），
   `Eform Λ δ δ = Eform Λ V V + 2 Eform Λ V W + Eform Λ W W`（`Eform_decomp`，**精确恒等式**），
   在 response 支配 `|Eform Λ U W| ≤ d·frob U·frob W`（**显式 conditional**，对应 Lead 已付的 `Λ0 ≤ dI`）
   与半正定下得 **`½xᵀH0x + Σa_ix_i² − d q³ ≤ Eform Λ δ δ`**（`h0_energy_quadratic_lower`）。

**明确未付（不伪装）**：
* `Λ0` 的 **Dirichlet-response 语义**（哪个图/Schur 补）——本件 `Λ` 是**任意**双指标族，
  其 response 性质以 `hcross`/`hpsd` 两个**显式前件**出现；
* `H0` 在 **pinned** 临界空间上的 **coercivity**（`≥ μ > 0`）——**不**假设、**不**证明；
* `E_{α0}(U(x))` 二阶导 = `⟨v,Λ0v⟩ − Σa_ix_i²` 的**调和延拓**证明（属下一件）。

**scope**：全部对任意 `Fintype ι`（含 `Fin 8` pinned / `Fin 9`）与任意 `Λ, a, θ, x` 成立，无条件。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset

/-- `(Λ ⊗ I₂)` 在 ℝ² 值族上的双线性型：`⟨U, (Λ⊗I₂)V⟩ = Σ_{i,j} Λ_ij ⟪U_i,V_j⟫`。 -/
def Eform {ι : Type*} [Fintype ι] (Λ : ι → ι → ℝ) (U V : ι → Point) : ℝ :=
  ∑ i, ∑ j, Λ i j * inner ℝ (U i) (V j)

/-- 族上的 Frobenius 范数（**与第一环 `anchorRemainder_frob_norm_le` 同一个量**）。 -/
def frob {ι : Type*} [Fintype ι] (U : ι → Point) : ℝ := Real.sqrt (∑ i, ‖U i‖ ^ 2)

/-- `Λ` 对称 ⇒ 型对称。 -/
theorem Eform_comm {ι : Type*} [Fintype ι] (Λ : ι → ι → ℝ) (hsym : ∀ i j, Λ i j = Λ j i)
    (U W : ι → Point) : Eform Λ W U = Eform Λ U W := by
  unfold Eform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hsym j i, real_inner_comm]

/-- 展开形态的对称性（`Eform_comm` 的逐项版，供 `calc` 里 `rw`）。 -/
theorem Eform_term_comm {ι : Type*} [Fintype ι] (Λ : ι → ι → ℝ) (hsym : ∀ i j, Λ i j = Λ j i)
    (U W : ι → Point) :
    (∑ i, ∑ j, Λ i j * inner ℝ (W i) (U j))
      = (∑ i, ∑ j, Λ i j * inner ℝ (U i) (W j)) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hsym j i, real_inner_comm]

/-- `V i = x_i • t_i` 时型退化为标量二次型。 -/
theorem Eform_smul_eq {ι : Type*} [Fintype ι] (Λ : ι → ι → ℝ) (t : ι → Point) (x : ι → ℝ) :
    Eform Λ (fun i => x i • t i) (fun i => x i • t i)
      = ∑ i, ∑ j, Λ i j * inner ℝ (t i) (t j) * x i * x j := by
  unfold Eform
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [realInner_smul_left', realInner_smul_right']
  ring

/-- 精确分解（二次型的双线性展开，**恒等式**，无余项）。 -/
theorem Eform_decomp {ι : Type*} [Fintype ι] (Λ : ι → ι → ℝ) (hsym : ∀ i j, Λ i j = Λ j i)
    (U W : ι → Point) :
    Eform Λ (fun i => U i + W i) (fun i => U i + W i)
      = Eform Λ U U + 2 * Eform Λ U W + Eform Λ W W := by
  have key : ∀ i j : ι, inner ℝ (U i + W i) (U j + W j)
      = inner ℝ (U i) (U j) + inner ℝ (U i) (W j) + inner ℝ (W i) (U j)
        + inner ℝ (W i) (W j) := by
    intro i j
    rw [inner_add_left, inner_add_right, inner_add_right]
    ring
  calc Eform Λ (fun i => U i + W i) (fun i => U i + W i)
      = ∑ i, ∑ j, Λ i j * (inner ℝ (U i) (U j) + inner ℝ (U i) (W j)
          + inner ℝ (W i) (U j) + inner ℝ (W i) (W j)) := by
          unfold Eform
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [key i j]
    _ = (∑ i, ∑ j, Λ i j * inner ℝ (U i) (U j)) + (∑ i, ∑ j, Λ i j * inner ℝ (U i) (W j))
          + (∑ i, ∑ j, Λ i j * inner ℝ (W i) (U j)) + (∑ i, ∑ j, Λ i j * inner ℝ (W i) (W j)) := by
          simp only [mul_add, Finset.sum_add_distrib]
    _ = Eform Λ U U + 2 * Eform Λ U W + Eform Λ W W := by
          rw [Eform_term_comm Λ hsym U W]
          simp only [Eform]
          ring

/-! ## H0（源 L29）与余弦核 -/

/-- 源 L29 的 `H0`：`H0_ij = 2 * (Λ_ij * ⟪J_i, J_j⟫ − δ_ij a_i)`。 -/
def H0mat {ι : Type*} [DecidableEq ι] (Λ : ι → ι → ℝ) (a : ι → ℝ) (J : ι → Point) :
    ι → ι → ℝ :=
  fun i j => 2 * (Λ i j * inner ℝ (J i) (J j) - (if i = j then a i else 0))

/-- 源 L29 的 "exactly half x^T H0 x"：`½xᵀH0x = Σ_{i,j}Λ_ij⟪J_i,J_j⟫x_ix_j − Σ_i a_i x_i²`。 -/
theorem h0_quadform {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : ι → ι → ℝ) (a : ι → ℝ)
    (J : ι → Point) (x : ι → ℝ) :
    (1 / 2) * (∑ i, ∑ j, H0mat Λ a J i j * x i * x j)
      = (∑ i, ∑ j, Λ i j * inner ℝ (J i) (J j) * x i * x j) - ∑ i, a i * x i ^ 2 := by
  have hd : ∀ i : ι, (∑ j, (if i = j then a i else 0) * x i * x j) = a i * x i ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      ring
    · intro j _ hj
      rw [if_neg (Ne.symm hj)]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  unfold H0mat
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← hd i, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i = j
  · subst h
    ring
  · rw [if_neg h]
    ring

/-- `H0` 对称。 -/
theorem h0_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : ι → ι → ℝ) (a : ι → ℝ)
    (J : ι → Point) (hΛ : ∀ i j, Λ i j = Λ j i)
    (hJ : ∀ i j, inner ℝ (J i) (J j) = inner ℝ (J j) (J i)) (i j : ι) :
    H0mat Λ a J i j = H0mat Λ a J j i := by
  unfold H0mat
  rw [hΛ i j, hJ i j]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- **`J = 真实切向` ⇒ 余弦核**：`⟪circleTangent θ_i, circleTangent θ_j⟫ = cos(θ_i − θ_j)`。 -/
theorem tangent_inner_eq (a b : ℝ) :
    inner ℝ (circleTangent a) (circleTangent b) = Real.cos (a - b) := by
  rw [circleTangent_eq_circleMap, circleTangent_eq_circleMap, inner_circleMap]
  congr 1
  ring

/-- **H0 与能量的连接（本件的核心）**：真实一次运动 `V_i = x_i • circleTangent (θ_i)` 的
`(Λ⊗I₂)` 能量 `Eform Λ V V` **恰等于** `½xᵀH0x + Σ_i a_i x_i²`。 -/
theorem h0_eq_response {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : ι → ι → ℝ) (a : ι → ℝ)
    (θ x : ι → ℝ) :
    Eform Λ (fun i => x i • circleTangent (θ i)) (fun i => x i • circleTangent (θ i))
      = (1 / 2) * (∑ i, ∑ j, H0mat Λ a (fun k => circleTangent (θ k)) i j * x i * x j)
        + ∑ i, a i * x i ^ 2 := by
  rw [Eform_smul_eq]
  have h := h0_quadform Λ a (fun k => circleTangent (θ k)) x
  linarith [h]

/-- **边系数 × 余弦核**（源 audit 的 `H_ij`）：`J_i := circleTangent (θ_i)` 时
`H0_ij = 2 (Λ_ij cos(θ_i−θ_j) − δ_ij a_i)`。 -/
theorem h0_eq_cosine {ι : Type*} [DecidableEq ι] (θ : ι → ℝ) (Λ : ι → ι → ℝ) (a : ι → ℝ)
    (i j : ι) :
    H0mat Λ a (fun k => circleTangent (θ k)) i j
      = 2 * (Λ i j * Real.cos (θ i - θ j) - (if i = j then a i else 0)) := by
  unfold H0mat
  rw [tangent_inner_eq]

/-! ## circle-Taylor 余项接入：真实位移 `δ = V + W` -/

/-- **实际锚位移下的能量二次下界（源 L21/29 的连接）**。

* `V` = 一次（切向）运动，`W` = 圆图二阶余项（`frob W ≤ q²/2`，由第一环供给）；
* `hcross` = response 支配 `|Eform Λ U W| ≤ d·frob U·frob W`（**显式 conditional**，对应 `Λ0 ≤ dI`）；
* `hpsd` = 半正定（**显式 conditional**）。

结论：`½xᵀH0x + Σa_ix_i² − d q³ ≤ Eform Λ (V+W) (V+W)` ——
即 `H0` 的二次型加上径向项，**在 circle-Taylor 余项 `O(q³)` 误差内**等于真实族的 `(Λ⊗I₂)` 能量。 -/
theorem h0_energy_quadratic_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : ι → ι → ℝ) (a : ι → ℝ) (θ x : ι → ℝ) (W : ι → Point) {d q : ℝ}
    (hd : 0 ≤ d) (hq : 0 ≤ q) (hsym : ∀ i j, Λ i j = Λ j i)
    (hcross : ∀ U W' : ι → Point, |Eform Λ U W'| ≤ d * frob U * frob W')
    (hpsd : ∀ U : ι → Point, 0 ≤ Eform Λ U U)
    (hVn : frob (fun i => x i • circleTangent (θ i)) = q)
    (hWn : frob W ≤ q ^ 2 / 2) :
    (1 / 2) * (∑ i, ∑ j, H0mat Λ a (fun k => circleTangent (θ k)) i j * x i * x j)
        + (∑ i, a i * x i ^ 2) - d * q ^ 3
      ≤ Eform Λ (fun i => x i • circleTangent (θ i) + W i)
          (fun i => x i • circleTangent (θ i) + W i) := by
  have hdecomp : Eform Λ (fun i => x i • circleTangent (θ i) + W i)
      (fun i => x i • circleTangent (θ i) + W i)
      = Eform Λ (fun i => x i • circleTangent (θ i)) (fun i => x i • circleTangent (θ i))
        + 2 * Eform Λ (fun i => x i • circleTangent (θ i)) W + Eform Λ W W :=
    Eform_decomp Λ hsym (fun i => x i • circleTangent (θ i)) W
  have hVeq := h0_eq_response Λ a θ x
  have hcs := hcross (fun i => x i • circleTangent (θ i)) W
  rw [hVn] at hcs
  have hhalf : d * q * (q ^ 2 / 2) = d * q ^ 3 / 2 := by ring
  have hcross3 : -(d * q ^ 3) ≤ 2 * Eform Λ (fun i => x i • circleTangent (θ i)) W := by
    have hneg : -(Eform Λ (fun i => x i • circleTangent (θ i)) W)
        ≤ |Eform Λ (fun i => x i • circleTangent (θ i)) W| := neg_le_abs _
    have hmul : d * q * frob W ≤ d * q * (q ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hWn (by positivity : (0 : ℝ) ≤ d * q)
    linarith [hneg, hcs, hmul, hhalf]
  have hpsdW := hpsd W
  linarith [hdecomp, hVeq, hcross3, hpsdW]

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.Eform_comm
#print axioms N11Formalization.FlashLocal.Eform_smul_eq
#print axioms N11Formalization.FlashLocal.Eform_decomp
#print axioms N11Formalization.FlashLocal.h0_quadform
#print axioms N11Formalization.FlashLocal.h0_symmetric
#print axioms N11Formalization.FlashLocal.tangent_inner_eq
#print axioms N11Formalization.FlashLocal.h0_eq_response
#print axioms N11Formalization.FlashLocal.h0_eq_cosine
#print axioms N11Formalization.FlashLocal.h0_energy_quadratic_lower
