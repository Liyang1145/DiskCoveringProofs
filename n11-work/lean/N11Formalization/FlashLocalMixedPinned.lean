import Mathlib
import N11Formalization.FlashLocalMixed
import N11Formalization.FlashLocalH0

/-!
# FlashLocal — 120 局部叶承重链 · 第九环：**pinned 混界 + 二次+mixed 下界**

Lead（2026-09-30）：实际 `C = .0358` 是 **raw8 restricted**，**不是全 9**；须证明对
**canonical6 = 0 子空间**（= raw8 pin，`EXACT-ORACLE-INDEX-MAP.md` L9–13）`hC` 足够，
且**第三余项与径向 `x²` 在该 pin 处也为 0**；**不得**把全 9 `hC` 当已付。
并要求：把我 `hH0` 的二次下界**经 raw8→canon6 pin 的实际消费者**输出**二次 + mixed** 下界，
**`Eform = dirichletEnergy` 保留为具名前件**。

本件四块：
1. **pin 消亡事实**（kernel）：`x p = 0` ⇒ `Jx`、`Rad(x²)`、三阶余项在该处**全为 0**；
2. `mixed_cross_lower_of_instance`：混界只需 `hC` 在**单一实例** `(x, x²)` 上成立
   ——因为原 `FlashLocalMixed.mixed_cross_lower` 的证明只在该实例用到 `hC`（已冻结件不能改，
   故此处给出**弱前件**版本）；
3. `mixed_cross_lower_pinned`：**限制在 `x' p = 0 ∧ z p = 0` 的 `hC`**（= raw8 restricted，即 `.0358` 的真实量词）
   即可推出同一下界；
4. `h0_quadratic_mixed_lower`：**二次 + mixed** 下界，形式 `½xᵀH0x + Σa_ix_i² − C q³ − (d/3)q⁴ ≤ dirichletForm (V+W)`，
   其中 `hresp : Eform Λ U U = dirichletForm U` 是**具名前件**（由 Lead 的 `ResumeDirichletShift` 付）。

**scope**：全部为 kernel-checked **conditional types**；`C d q` 具名；不含 μ-coercivity、
不含 adaptive/variational 损耗、不含叶/图。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset

/-! ## 1. pin 消亡事实 -/

/-- `x p = 0` ⇒ 切向族在该 pin 处为 0。 -/
theorem Jx_pin_zero {ι : Type*} (θ x : ι → ℝ) (p : ι) (hx : x p = 0) : Jx θ x p = 0 := by
  simp [Jx, hx]

/-- `x p = 0` ⇒ **径向 `x²` 在该 pin 处为 0**（`z = x²` 的 pin 同步）。 -/
theorem Rad_sq_pin_zero {ι : Type*} (θ x : ι → ℝ) (p : ι) (hx : x p = 0) :
    Rad θ (fun i => x i ^ 2) p = 0 := by
  simp [Rad, hx]

/-- `x p = 0` ⇒ **三阶余项在该 pin 处为 0**（同步）。 -/
theorem thirdRem_pin_zero {ι : Type*} (θ x : ι → ℝ) (p : ι) (hx : x p = 0) :
    circleMap (θ p + x p) - circleMap (θ p) - x p • circleTangent (θ p)
      + (x p ^ 2 / 2) • circleMap (θ p) = 0 := by
  simp [hx]

/-! ## 2. 混界只需**单一实例**的 `hC` -/

/-- **弱前件版混界**：只需 `hC` 在**唯一实例** `(x, x²)` 上成立（原 `mixed_cross_lower` 的证明
只在此处用它）。 -/
theorem mixed_cross_lower_of_instance {ι : Type*} [Fintype ι]
    (Λ : ι → ι → ℝ) (θ x : ι → ℝ) (R : ι → Point) {C d q : ℝ}
    (hC0 : 0 ≤ C) (hd0 : 0 ≤ d) (hq : 0 ≤ q)
    (hCs : |∑ i, ∑ j, Cmat Λ θ i j * x i * x j ^ 2|
        ≤ C * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, (x i ^ 2) ^ 2))
    (hΛ : ∀ U W : ι → Point, |Eform Λ U W| ≤ d * frob U * frob W)
    (hJx : frob (Jx θ x) = q) (hR : frob R ≤ q ^ 3 / 6) :
    -(C * q ^ 3) - d * q ^ 4 / 3
      ≤ 2 * Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i) := by
  have hsnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hqsum : Real.sqrt (∑ i, x i ^ 2) = q := by rw [← frob_Jx, hJx]
  have hq2 : q ^ 2 = ∑ i, x i ^ 2 := by rw [← hqsum, Real.sq_sqrt hsnn]
  have hdecomp : Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
      = Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i)) + Eform Λ (Jx θ x) R :=
    Eform_add_right Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i)) R
  have hfirst : Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i))
      = -(1 / 2) * (∑ i, ∑ j, Cmat Λ θ i j * x i * x j ^ 2) := by
    rw [Eform_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold Cmat Jx
    rw [realInner_smul_left']
    ring
  have hb1 : |∑ i, ∑ j, Cmat Λ θ i j * x i * x j ^ 2| ≤ C * q ^ 3 := by
    rw [hqsum] at hCs
    have h4eq : Real.sqrt (∑ j, (x j ^ 2) ^ 2) = Real.sqrt (∑ j, x j ^ 4) := by
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h4eq] at hCs
    have hle : Real.sqrt (∑ j, x j ^ 4) ≤ q ^ 2 := by
      calc Real.sqrt (∑ j, x j ^ 4) ≤ ∑ j, x j ^ 2 := sqrt_sum_four_le x
        _ = q ^ 2 := hq2.symm
    have hmul : C * q * Real.sqrt (∑ j, x j ^ 4) ≤ C * q * q ^ 2 :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have he : C * q * q ^ 2 = C * q ^ 3 := by ring
    linarith [hCs, hmul, he]
  have hb2 : |Eform Λ (Jx θ x) R| ≤ d * q ^ 4 / 6 := by
    have h := hΛ (Jx θ x) R
    rw [hJx] at h
    have hmul : d * q * frob R ≤ d * q * (q ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ d * q)
    have he : d * q * (q ^ 3 / 6) = d * q ^ 4 / 6 := by ring
    linarith [h, hmul, he]
  have hgoal : 2 * Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
      = -(∑ i, ∑ j, Cmat Λ θ i j * x i * x j ^ 2) + 2 * Eform Λ (Jx θ x) R := by
    rw [hdecomp, hfirst]
    ring
  rw [hgoal]
  have h1 := abs_le.mp hb1
  have h2 := abs_le.mp hb2
  linarith [h1.1, h1.2, h2.1, h2.2, hq, hC0, hd0]

/-! ## 3. **pinned**（raw8 = canonical6）限制下的混界 -/

/-- `x p = 0`（raw8 pin = canonical6）时，限制在 `x' p = 0 ∧ z p = 0` 的 `hC` 即足够
——这正是 `.0358` 的真实量词（**不是全 9**）。 -/
theorem mixed_cross_lower_pinned {ι : Type*} [Fintype ι] (p : ι)
    (Λ : ι → ι → ℝ) (θ x : ι → ℝ) (R : ι → Point) {C d q : ℝ}
    (hC0 : 0 ≤ C) (hd0 : 0 ≤ d) (hq : 0 ≤ q) (hx0 : x p = 0)
    (hC : ∀ x' z : ι → ℝ, x' p = 0 → z p = 0 →
        |∑ i, ∑ j, Cmat Λ θ i j * x' i * z j|
          ≤ C * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ i, z i ^ 2))
    (hΛ : ∀ U W : ι → Point, |Eform Λ U W| ≤ d * frob U * frob W)
    (hJx : frob (Jx θ x) = q) (hR : frob R ≤ q ^ 3 / 6) :
    -(C * q ^ 3) - d * q ^ 4 / 3
      ≤ 2 * Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i) :=
  mixed_cross_lower_of_instance Λ θ x R hC0 hd0 hq
    (hC x (fun j => x j ^ 2) hx0 (by simp [hx0])) hΛ hJx hR

/-! ## 4. **二次 + mixed 下界**（经 pin 的实际消费者；响应为具名前件） -/

/-- **主交付**：经 raw8→canon6 pin 的实际消费者，输出**二次 + mixed**下界：
`½xᵀH0x + Σ_i a_i x_i² − C q³ − (d/3) q⁴ ≤ dirichletForm (V + W)`,
其中 `V = Jx θ x`、`W = −Rad(x²)/2 + R`、`dirichletForm` 是**真实响应**（`hresp` 为**具名前件**，
由 Lead 的 `ResumeDirichletShift` 付——本件**不**声称它已付）。 -/
theorem h0_quadratic_mixed_lower {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι)
    (Λ : ι → ι → ℝ) (a θ x : ι → ℝ) (R : ι → Point)
    (dirichletForm : (ι → Point) → ℝ) {C d q : ℝ}
    (hC0 : 0 ≤ C) (hd0 : 0 ≤ d) (hq : 0 ≤ q) (hx0 : x p = 0)
    (hsym : ∀ i j, Λ i j = Λ j i)
    -- **具名**响应等同（不声称已付）
    (hresp : ∀ U : ι → Point, Eform Λ U U = dirichletForm U)
    (hpsd : ∀ U : ι → Point, 0 ≤ Eform Λ U U)
    (hC : ∀ x' z : ι → ℝ, x' p = 0 → z p = 0 →
        |∑ i, ∑ j, Cmat Λ θ i j * x' i * z j|
          ≤ C * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ i, z i ^ 2))
    (hΛ : ∀ U W : ι → Point, |Eform Λ U W| ≤ d * frob U * frob W)
    (hJx : frob (Jx θ x) = q) (hR : frob R ≤ q ^ 3 / 6) :
    (1 / 2) * (∑ i, ∑ j, H0mat Λ a (fun k => circleTangent (θ k)) i j * x i * x j)
        + (∑ i, a i * x i ^ 2) - C * q ^ 3 - d * q ^ 4 / 3
      ≤ dirichletForm (fun i => x i • circleTangent (θ i)
          + (-(x i ^ 2 / 2) • circleMap (θ i) + R i)) := by
  have hdecomp : Eform Λ (fun i => x i • circleTangent (θ i)
        + (-(x i ^ 2 / 2) • circleMap (θ i) + R i))
      (fun i => x i • circleTangent (θ i) + (-(x i ^ 2 / 2) • circleMap (θ i) + R i))
      = Eform Λ (Jx θ x) (Jx θ x)
        + 2 * Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
        + Eform Λ (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
            (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i) :=
    Eform_decomp Λ hsym (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
  have hH0 : Eform Λ (Jx θ x) (Jx θ x)
      = (1 / 2) * (∑ i, ∑ j, H0mat Λ a (fun k => circleTangent (θ k)) i j * x i * x j)
        + ∑ i, a i * x i ^ 2 := h0_eq_response Λ a θ x
  have hmix := mixed_cross_lower_pinned p Λ θ x R hC0 hd0 hq hx0 hC hΛ hJx hR
  have hQ : 0 ≤ Eform Λ (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
      (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i) := hpsd _
  rw [hresp _] at hdecomp
  linarith [hdecomp, hH0, hmix, hQ]

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.Jx_pin_zero
#print axioms N11Formalization.FlashLocal.Rad_sq_pin_zero
#print axioms N11Formalization.FlashLocal.thirdRem_pin_zero
#print axioms N11Formalization.FlashLocal.mixed_cross_lower_of_instance
#print axioms N11Formalization.FlashLocal.mixed_cross_lower_pinned
#print axioms N11Formalization.FlashLocal.h0_quadratic_mixed_lower
