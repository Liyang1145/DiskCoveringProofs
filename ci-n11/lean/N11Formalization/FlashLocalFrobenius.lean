import Mathlib
import N11Formalization.FlashLocalDirectionalActual

/-!
# FlashLocal — 120 局部叶承重链 · 第十二环：**Frobenius 具体接法**（flux / pinned Cmat）

Lead 2026-09-30（实读 `research-2026/team-current/lead/certify_relative_stress_ball.py` L12–24）：

```python
flux=iv.matrix(18,4)                     # 18 = 9 节点 × 2 坐标，4 = N 的列
Anorm=iv.sqrt(sum(flux[i,j]**2 for i in range(18) for j in range(4)))
Cross=iv.matrix(n,n)                     # n = 8：raw8 基底
Cross[i,j]=k.Lam[i,j]*(-k.U[i][1]*k.U[j][0]+k.U[i][0]*k.U[j][1])
cnorm=iv.sqrt(sum(Cross[i,j]**2 for i in range(n) for j in range(n)))
```

即：`A` 是 **18×4 flux 的 Frobenius 范数**，`Ccross` 是 **pinned 8×8 Cross 的 Frobenius 范数**
（**不是** 9×9，也**不是** sharp operator norm）。因此这一环**不需要新的谱/特征值核**：
只要两条通用 finite Cauchy（矩阵双线性 + 族级 smul），就能把源脚本的 Frobenius 数
转成 `FlashLocalDirectionalActual` 消费的 operator 型前件。

本件四块（全部 kernel，无新公理）：

1. **`flux_Qx_eq`**（源 `flux` 的线性性）：`flux (Qx …) = τ • Σ_a (Gᵀx)_a • F_a`，
   其中 `F a := flux (fun e => N e a)` 就是源脚本的 18×4 矩阵（逐列）；
2. **`bilinear_frobenius_le`**：`|Σ_ij x_i M_ij z_j| ≤ √(Σ M²)·√(Σx²)·√(Σz²)`（Frobenius ≥ op）；
   配合 **`pinned_operator_le_of_frobenius`**（pin 指标 `p` 的行列置零，即 8×8）给出 `hCcross`；
3. **`frob_smul_family_le`**：`frob (Σ_a z_a • F a) ≤ √(Σ z²)·√(Σ (frob F a)²)`；
   配合 **`frob_flux_Qx_le`**（前件 `Σ_a (frob (F a))² ≤ A²`、`p² = Σ_a (Gᵀx)_a²`）给出 `hfδ`；
4. **`pinned_frobenius_filter_eq`**：把 pin 后的稀疏和写成 `univ.erase/filter` 形态，
   便于与源脚本的 8×8 求和逐项对齐（纯有限和，无附加前提）。

**边界（不得越界声称）**：本件**只做 Frobenius → operator 的通用桥**。
`A`、`Ccross` 的**实际数值**仍由源脚本的区间证书（`aq/cq`）供给，本件**不声称任何数字**；
`hfluxα/hρ/hresp/coercivity` 与源 α/H/Λ/constants 一律不动。本件不声称
`FlashLocalDirectionalActual` 的其余具名前件已付。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset
open N11Formalization.ResumeNetwork N11Formalization.ResumeDirichlet
  N11Formalization.ResumeDirichletShift N11Formalization.ResumeAnchorFlux

/-! ## 1. `flux` 的线性性：`flux (Qx …) = τ • Σ_a (Gᵀx)_a • F_a` -/

/-- **源 `flux` 线性性**：`F a := flux (fun e => N e a) U C Z`（源脚本的 18×4 矩阵逐列）时
`flux (fun e => Qx … e) U C Z j = τ • Σ_a (Gᵀx)_a • F a j`。纯有限和重排。 -/
theorem flux_Qx_eq (s : Edge → Fin 9 → ℝ) (D : Edge → Point) (tang : Fin 9 → Point)
    (N : Edge → Fin 4 → ℝ) (τ : ℝ) (x : Fin 9 → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    (j : Fin 9) :
    flux (fun e => Qx s D tang N τ x e) U C Z j
      = τ • ∑ a, (GtX s D tang N x a) • flux (fun e => N e a) U C Z j := by
  have hL : flux (fun e => Qx s D tang N τ x e) U C Z j
      = ∑ e, ∑ a, (anchorIncidence e j * (τ * (N e a * GtX s D tang N x a)))
          • edgeVector U C Z e := by
    unfold flux
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [Qx]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_smul]
  have hR : τ • (∑ a, (GtX s D tang N x a) • flux (fun e => N e a) U C Z j)
      = ∑ a, ∑ e, (anchorIncidence e j * (τ * (N e a * GtX s D tang N x a)))
          • edgeVector U C Z e := by
    simp only [flux, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    congr 1
    ring
  rw [hL, hR, Finset.sum_comm]

/-! ## 2. 通用矩阵 finite Cauchy（给出 `hCcross`） -/

/-- **通用矩阵 finite Cauchy**：`|Σ_ij x_i M_ij z_j| ≤ √(Σ_{ij} M_ij²)·√(Σ_i x_i²)·√(Σ_j z_j²)`。
Frobenius 范数 ≥ operator 2-范数（对任意 `Fintype` 指标集）。 -/
theorem bilinear_frobenius_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℝ) (x : ι → ℝ) (z : κ → ℝ) :
    |∑ i, ∑ j, M i j * x i * z j|
      ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * Real.sqrt (∑ i, x i ^ 2)
        * Real.sqrt (∑ j, z j ^ 2) := by
  have hCS : ∀ u v : ι → ℝ,
      |∑ i, u i * v i| ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
    intro u v
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (f := u) (g := v)
    have h1 : (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * ∑ i, v i ^ 2 := h
    have h2 : (∑ i, u i * v i) ^ 2 ≤ (Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (u i)),
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
      exact h1
    calc |∑ i, u i * v i| = Real.sqrt ((∑ i, u i * v i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) :=
          Real.sqrt_sq (by positivity)
  have hz : ∀ i, (∑ j, M i j * z j) ^ 2 ≤ (∑ j, M i j ^ 2) * (∑ j, z j ^ 2) := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (f := fun j => M i j) (g := z)
    simpa [mul_assoc] using h
  have hrow : ∑ i, (∑ j, M i j * z j) ^ 2
      ≤ (∑ i, ∑ j, M i j ^ 2) * ∑ j, z j ^ 2 := by
    calc ∑ i, (∑ j, M i j * z j) ^ 2 ≤ ∑ i, (∑ j, M i j ^ 2) * (∑ j, z j ^ 2) :=
          Finset.sum_le_sum (fun i _ => hz i)
      _ = (∑ i, ∑ j, M i j ^ 2) * ∑ j, z j ^ 2 := by rw [Finset.sum_mul]
  have hz0 : 0 ≤ ∑ j, z j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (z j)
  have hCS2 := hCS x (fun i => ∑ j, M i j * z j)
  have hsq : ∑ i, (∑ j, M i j * z j) ^ 2
      ≤ (Real.sqrt (∑ i, ∑ j, M i j ^ 2) * Real.sqrt (∑ j, z j ^ 2)) ^ 2 := by
    rw [mul_pow,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (M i j)),
      Real.sq_sqrt hz0]
    exact hrow
  have hfin : Real.sqrt (∑ i, (∑ j, M i j * z j) ^ 2)
      ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * Real.sqrt (∑ j, z j ^ 2) := by
    calc Real.sqrt (∑ i, (∑ j, M i j * z j) ^ 2)
        ≤ Real.sqrt ((Real.sqrt (∑ i, ∑ j, M i j ^ 2) * Real.sqrt (∑ j, z j ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ i, ∑ j, M i j ^ 2) * Real.sqrt (∑ j, z j ^ 2) := Real.sqrt_sq (by positivity)
  have hfinal := hCS2
  rw [show (∑ i, x i * (∑ j, M i j * z j)) = ∑ i, ∑ j, M i j * x i * z j from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring] at hfinal
  calc |∑ i, ∑ j, M i j * x i * z j|
      ≤ Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, (∑ j, M i j * z j) ^ 2) := hfinal
    _ ≤ Real.sqrt (∑ i, x i ^ 2)
          * (Real.sqrt (∑ i, ∑ j, M i j ^ 2) * Real.sqrt (∑ j, z j ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hfin (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ i, ∑ j, M i j ^ 2) * Real.sqrt (∑ i, x i ^ 2)
          * Real.sqrt (∑ j, z j ^ 2) := by ring

/-! ## 3. pin 指标（canonical6 / raw8）：Frobenius → 受限 operator 界 -/

/-- **pinned 8×8 Frobenius → operator 界**：`hCf` 是 pin 指标 `p` 的行列全置零后的
Frobenius 平方和（指标集为 8 个非 pin 坐标时正是 8×8）。若 `x' p = 0`、`z p = 0`，
则双线性型只看到非 pin 坐标，故 `hCf` 足以给出 operator 型前件 `hC`。 -/
theorem pinned_operator_le_of_frobenius {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι)
    (M : ι → ι → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hCf : ∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2 ≤ C ^ 2) :
    ∀ x' z : ι → ℝ, x' p = 0 → z p = 0 →
      |∑ i, ∑ j, M i j * x' i * z j|
        ≤ C * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ j, z j ^ 2) := by
  intro x' z hx hz
  have hsum : ∑ i, ∑ j, M i j * x' i * z j
      = ∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) * x' i * z j := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hi : i = p
    · rw [hi, hx]
      simp
    · by_cases hj : j = p
      · rw [hj, hz]
        simp [hi]
      · simp [hi, hj]
  rw [hsum]
  have hb := bilinear_frobenius_le (fun i j => if i = p ∨ j = p then 0 else M i j) x' z
  have hMle : Real.sqrt (∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2) ≤ C := by
    calc Real.sqrt (∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2)
        ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hCf
      _ = C := Real.sqrt_sq hC0
  calc |∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) * x' i * z j|
      ≤ Real.sqrt (∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2)
          * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ j, z j ^ 2) := hb
    _ ≤ C * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ j, z j ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMle (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)

/-- **pin 后 Frobenius 和的 filter 形态 = 置零指标形态**（纯有限和恒等）。
`Finset.univ.filter (· ≠ p)` 上的双重和就是源脚本的 8×8 求和（对 `Fin 9`, `p = 6` 而言）。 -/
theorem pinned_frobenius_filter_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι)
    (M : ι → ι → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => i ≠ p),
        ∑ j ∈ Finset.univ.filter (fun j => j ≠ p), M i j ^ 2)
      = ∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2 := by
  have hzero_i : ∀ i, i ∉ Finset.univ.filter (fun i => i ≠ p) →
      (∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2) = 0 := by
    intro i hi
    have hip : i = p := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    rw [hip]
    simp
  have h1 : (∑ i, ∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2)
      = ∑ i ∈ Finset.univ.filter (fun i => i ≠ p),
          ∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2 :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => hzero_i i hi)).symm
  rw [h1]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≠ p := (Finset.mem_filter.mp hi).2
  have hzero_j : ∀ j, j ∉ Finset.univ.filter (fun j => j ≠ p) →
      (if i = p ∨ j = p then 0 else M i j) ^ 2 = 0 := by
    intro j hj
    have hjp : j = p := by
      by_contra h
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    rw [hjp]
    simp
  have h2 : (∑ j, (if i = p ∨ j = p then 0 else M i j) ^ 2)
      = ∑ j ∈ Finset.univ.filter (fun j => j ≠ p),
          (if i = p ∨ j = p then 0 else M i j) ^ 2 :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => hzero_j j hj)).symm
  rw [h2]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≠ p := (Finset.mem_filter.mp hj).2
  simp [hi', hj']

/-! ## 4. 族级 finite Cauchy 与 `hfδ` -/

/-- `frob (c • U) = |c| * frob U`。 -/
theorem frob_smul {ι : Type*} [Fintype ι] (c : ℝ) (U : ι → Point) :
    frob (fun i => c • U i) = |c| * frob U := by
  unfold frob
  have h : ∑ i, ‖c • U i‖ ^ 2 = c ^ 2 * ∑ i, ‖U i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **族级 finite Cauchy**：`frob (Σ_a z_a • F a) ≤ √(Σ_a z_a²)·√(Σ_a (frob (F a))²)`
（对 `Point` 值族，逐坐标 Cauchy + 交换有限和）。 -/
theorem frob_smul_family_le {κ ι : Type*} [Fintype κ] [Fintype ι] (z : κ → ℝ)
    (F : κ → ι → Point) :
    frob (fun j => ∑ a, z a • F a j)
      ≤ Real.sqrt (∑ a, z a ^ 2) * Real.sqrt (∑ a, (frob (F a)) ^ 2) := by
  have hcoord : ∀ j, ‖∑ a, z a • F a j‖ ^ 2
      ≤ (∑ a, z a ^ 2) * ∑ a, ‖F a j‖ ^ 2 := by
    intro j
    have h1 : ‖∑ a, z a • F a j‖ ≤ ∑ a, |z a| * ‖F a j‖ := by
      calc ‖∑ a, z a • F a j‖ ≤ ∑ a, ‖z a • F a j‖ := norm_sum_le _ _
        _ = ∑ a, |z a| * ‖F a j‖ := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [norm_smul, Real.norm_eq_abs]
    have h0 : 0 ≤ ∑ a, |z a| * ‖F a j‖ :=
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have h2 : (∑ a, |z a| * ‖F a j‖) ^ 2 ≤ (∑ a, z a ^ 2) * ∑ a, ‖F a j‖ ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (f := fun a => |z a|) (g := fun a => ‖F a j‖)
      simpa [sq_abs] using h
    calc ‖∑ a, z a • F a j‖ ^ 2 ≤ (∑ a, |z a| * ‖F a j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ a, z a ^ 2) * ∑ a, ‖F a j‖ ^ 2 := h2
  have hsum : ∑ j, ‖∑ a, z a • F a j‖ ^ 2 ≤ (∑ a, z a ^ 2) * ∑ a, ∑ j, ‖F a j‖ ^ 2 := by
    calc ∑ j, ‖∑ a, z a • F a j‖ ^ 2 ≤ ∑ j, (∑ a, z a ^ 2) * ∑ a, ‖F a j‖ ^ 2 :=
          Finset.sum_le_sum (fun j _ => hcoord j)
      _ = (∑ a, z a ^ 2) * ∑ j, ∑ a, ‖F a j‖ ^ 2 := by
        conv_rhs => rw [Finset.mul_sum]
      _ = (∑ a, z a ^ 2) * ∑ a, ∑ j, ‖F a j‖ ^ 2 := by
        conv_rhs => rw [Finset.sum_comm]
  have hfrob : ∀ a, (frob (F a)) ^ 2 = ∑ j, ‖F a j‖ ^ 2 := by
    intro a
    rw [frob, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg ‖F a j‖)]
  have hrhs : (∑ a, z a ^ 2) * ∑ a, ∑ j, ‖F a j‖ ^ 2
      = ((Real.sqrt (∑ a, z a ^ 2) * Real.sqrt (∑ a, (frob (F a)) ^ 2)) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg (z a)),
      Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg (frob (F a)))]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact (hfrob a).symm
  calc frob (fun j => ∑ a, z a • F a j)
      = Real.sqrt (∑ j, ‖∑ a, z a • F a j‖ ^ 2) := rfl
    _ ≤ Real.sqrt ((Real.sqrt (∑ a, z a ^ 2) * Real.sqrt (∑ a, (frob (F a)) ^ 2)) ^ 2) := by
        rw [← hrhs]
        exact Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (∑ a, z a ^ 2) * Real.sqrt (∑ a, (frob (F a)) ^ 2) := Real.sqrt_sq (by positivity)

/-- **`hfδ` 的 Frobenius 接法**：源脚本的 18×4 Frobenius 证书
`Σ_a (frob F_a)² ≤ A²`（`F_a = flux (fun e => N e a)`）、`p² = Σ_a (Gᵀx)_a²`
（`0 ≤ τ, 0 ≤ p, 0 ≤ A`）⇒ `frob (flux (Qx …)) ≤ τ·A·p`。 -/
theorem frob_flux_Qx_le (s : Edge → Fin 9 → ℝ) (D : Edge → Point) (tang : Fin 9 → Point)
    (N : Edge → Fin 4 → ℝ) (τ : ℝ) (x : Fin 9 → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    {A p : ℝ} (hτ : 0 ≤ τ) (hA0 : 0 ≤ A) (hp0 : 0 ≤ p)
    (hp2 : p ^ 2 = ∑ a, (GtX s D tang N x a) ^ 2)
    (hFsq : ∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2 ≤ A ^ 2) :
    frob (flux (fun e => Qx s D tang N τ x e) U C Z) ≤ τ * A * p := by
  have hfun : (fun j => flux (fun e => Qx s D tang N τ x e) U C Z j)
      = fun j => τ • (∑ a, (GtX s D tang N x a) • flux (fun e => N e a) U C Z j) := by
    funext j
    exact flux_Qx_eq s D tang N τ x U C Z j
  change frob (fun j => flux (fun e => Qx s D tang N τ x e) U C Z j) ≤ τ * A * p
  rw [hfun, frob_smul, abs_of_nonneg hτ]
  have hfam := frob_smul_family_le (z := GtX s D tang N x)
    (F := fun a => flux (fun e => N e a) U C Z)
  have hzp : Real.sqrt (∑ a, (GtX s D tang N x a) ^ 2) = p := by
    rw [← hp2, Real.sqrt_sq hp0]
  have hFA : Real.sqrt (∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2) ≤ A := by
    calc Real.sqrt (∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2)
        ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt hFsq
      _ = A := Real.sqrt_sq hA0
  calc τ * frob (fun j => ∑ a, (GtX s D tang N x a) • flux (fun e => N e a) U C Z j)
      ≤ τ * (Real.sqrt (∑ a, (GtX s D tang N x a) ^ 2)
          * Real.sqrt (∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hfam hτ
    _ = τ * (p * Real.sqrt (∑ a, (frob (flux (fun e => N e a) U C Z)) ^ 2)) := by rw [hzp]
    _ ≤ τ * (p * A) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFA hp0) hτ
    _ = τ * A * p := by ring

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.flux_Qx_eq
#print axioms N11Formalization.FlashLocal.bilinear_frobenius_le
#print axioms N11Formalization.FlashLocal.pinned_operator_le_of_frobenius
#print axioms N11Formalization.FlashLocal.pinned_frobenius_filter_eq
#print axioms N11Formalization.FlashLocal.frob_smul
#print axioms N11Formalization.FlashLocal.frob_smul_family_le
#print axioms N11Formalization.FlashLocal.frob_flux_Qx_le
