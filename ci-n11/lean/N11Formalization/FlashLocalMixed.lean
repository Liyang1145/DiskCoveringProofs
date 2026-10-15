import Mathlib
import N11Formalization.FlashLocalH0
import N11Formalization.FlashLocalThirdFrob

/-!
# FlashLocal — 120 局部叶承重链 · 第八环：**各向异性混合交叉界**（源 L5–8）

按 Lead 2026-09-30 指定的构造实现（`ANISOTROPIC-STRESS-REMAINDER.md` L5–8，我逐行读过）：

```
5. Put R_i=U_i(x)-U_i-v_i+(x_i^2/2)U_i, ||R||<=q^3/6. Let J8 map raw8 x to the 9vector
   tangential v, and radial9 z to components U_i z_i. Define C_cross=||J8^T (Lambda0 tensor
   I2) Rad8||_op, with x8=0. Then
6.   2<v,Lambda0 w> = - x^T Cmat x^{(2)} + 2<v,Lambda0 R>
7.   >= -C_cross q^3 - (d/3)q^4.
8. (The full i,j sum is indispensable; offdiagonal terms do not vanish.)
```

**本件只做这一个 mixed cross theorem**（Lead 明示：不宣称能直接提供整个 `h`，
μ-coercivity 与 adaptive 损失另缺）。构造逐字对应：

* `Jx θ x i = x_i • tangent θ_i`（切向族 = `J8 x`）；
* `Rad θ z i = z_i • circle θ_i`（径向族 = `Rad8 z`）；
* **混合矩阵** `Cmat Λ θ i j = Λ_ij * ⟪tangent θ_i, circle θ_j⟫`（切向-径向交叉，
  **完整 (i,j) 双和，不用对角**——源 L8）；
* `W = −Rad(x²)/2 + R`（`z = x²`，即二阶余项 `w = δ − v`）；
* `hC`：**显式** operator bound `|Σ_ij x_i Cmat_ij z_j| ≤ C √(Σx²) √(Σz²)`（= `C_cross` 的定义性界，raw8 pin 或 9 均可）；
* `hΛ`：**全 Λ** bound `|Eform Λ U W| ≤ d ‖U‖‖W‖`（`frob`）。

结论（源 L7）：`−(C q³) − (d/3) q⁴ ≤ 2 Eform Λ (Jx θ x) W`，其中
`q = ‖J8x‖`（由 `frob (Jx θ x) = q` 给出）、`‖R‖ ≤ q³/6`（第一/三阶件供给）。
第一项用 `√(Σx⁴) ≤ q²`；第二项用全 Λ bound。

**scope**：单件定理；`C`/`d`/`q` 全是**具名参数**（**不硬塞 .0358**），
不含 μ-coercivity、不含 adaptive 损失、不含 `p=‖G8ᵀx‖` 方向损失、不含叶/图。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset

/-- 切向族 `(J8 x)_i = x_i • tangent θ_i`（源 L5 的 `J8` 作用）。 -/
def Jx {ι : Type*} (θ x : ι → ℝ) : ι → Point := fun i => x i • circleTangent (θ i)

/-- 径向族 `(Rad8 z)_i = z_i • circle θ_i`（源 L5 的 `Rad8` 作用）。 -/
def Rad {ι : Type*} (θ z : ι → ℝ) : ι → Point := fun i => z i • circleMap (θ i)

/-- **混合矩阵** `Cmat_ij = Λ_ij ⟪tangent θ_i, circle θ_j⟫`（切向行 × 径向列）。 -/
def Cmat {ι : Type*} (Λ : ι → ι → ℝ) (θ : ι → ℝ) : ι → ι → ℝ :=
  fun i j => Λ i j * inner ℝ (circleTangent (θ i)) (circleMap (θ j))

/-- `Eform` 在第二槽的加法性。 -/
theorem Eform_add_right {ι : Type*} [Fintype ι] (Λ : ι → ι → ℝ) (U S T : ι → Point) :
    Eform Λ U (fun i => S i + T i) = Eform Λ U S + Eform Λ U T := by
  unfold Eform
  simp only [inner_add_right, mul_add, Finset.sum_add_distrib]

/-- `Eform` 在第二槽的数乘性。 -/
theorem Eform_smul_right {ι : Type*} [Fintype ι] (Λ : ι → ι → ℝ) (U : ι → Point)
    (c : ι → ℝ) (T : ι → Point) :
    Eform Λ U (fun i => c i • T i) = ∑ i, ∑ j, Λ i j * c j * inner ℝ (U i) (T j) := by
  unfold Eform
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [realInner_smul_right']
  ring

/-- `frob (J8 x) = √(Σ x_i²)`（切向单位、正交方向不改变范数）。 -/
theorem frob_Jx {ι : Type*} [Fintype ι] (θ x : ι → ℝ) :
    frob (Jx θ x) = Real.sqrt (∑ i, x i ^ 2) := by
  unfold frob Jx
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [norm_smul, circleTangent_norm, mul_one, Real.norm_eq_abs, sq_abs]

/-- `√(Σ x_i⁴) ≤ Σ x_i²`（用第一环的 `sum_four_le_sq_sum`）。 -/
theorem sqrt_sum_four_le {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (∑ i, x i ^ 4) ≤ ∑ i, x i ^ 2 := by
  have h := sum_four_le_sq_sum x
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  calc Real.sqrt (∑ i, x i ^ 4) ≤ Real.sqrt ((∑ i, x i ^ 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = |∑ i, x i ^ 2| := Real.sqrt_sq_eq_abs _
    _ = ∑ i, x i ^ 2 := abs_of_nonneg hs

/-- **主定理（源 L6–7）**：`2 Eform Λ (J8x) W ≥ −C q³ − (d/3) q⁴`，
其中 `W = −Rad(x²)/2 + R`、`q = frob (J8x)`、`‖R‖ ≤ q³/6`、`C` 为混合 operator 常数、`d` 为全 Λ 常数。 -/
theorem mixed_cross_lower {ι : Type*} [Fintype ι]
    (Λ : ι → ι → ℝ) (θ x : ι → ℝ) (R : ι → Point) {C d q : ℝ}
    (hC0 : 0 ≤ C) (hd0 : 0 ≤ d) (hq : 0 ≤ q)
    (hC : ∀ x' z : ι → ℝ, |∑ i, ∑ j, Cmat Λ θ i j * x' i * z j|
        ≤ C * Real.sqrt (∑ i, x' i ^ 2) * Real.sqrt (∑ i, z i ^ 2))
    (hΛ : ∀ U W : ι → Point, |Eform Λ U W| ≤ d * frob U * frob W)
    (hJx : frob (Jx θ x) = q) (hR : frob R ≤ q ^ 3 / 6) :
    -(C * q ^ 3) - d * q ^ 4 / 3
      ≤ 2 * Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i) := by
  have hsnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hqsum : Real.sqrt (∑ i, x i ^ 2) = q := by rw [← frob_Jx, hJx]
  have hq2 : q ^ 2 = ∑ i, x i ^ 2 := by rw [← hqsum, Real.sq_sqrt hsnn]
  -- 第二槽分解
  have hdecomp : Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
      = Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i)) + Eform Λ (Jx θ x) R :=
    Eform_add_right Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i)) R
  -- 第一项：`Eform (J8x) (−Rad(x²)/2) = −(1/2) Σ_ij Cmat_ij x_i x_j²`
  have hfirst : Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i))
      = -(1 / 2) * (∑ i, ∑ j, Cmat Λ θ i j * x i * x j ^ 2) := by
    rw [Eform_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold Cmat Jx
    rw [realInner_smul_left']
    ring
  -- 第一项的界（`√(Σx²) = q`、`√(Σx⁴) ≤ q²`）
  have hb1 : |∑ i, ∑ j, Cmat Λ θ i j * x i * x j ^ 2| ≤ C * q ^ 3 := by
    have h := hC x (fun j => x j ^ 2)
    have h4 : (∑ j, (x j ^ 2) ^ 2) = ∑ j, x j ^ 4 :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [h4, hqsum] at h
    have hle : Real.sqrt (∑ j, x j ^ 4) ≤ q ^ 2 := by
      calc Real.sqrt (∑ j, x j ^ 4) ≤ ∑ j, x j ^ 2 := sqrt_sum_four_le x
        _ = q ^ 2 := hq2.symm
    have hmul : C * q * Real.sqrt (∑ j, x j ^ 4) ≤ C * q * q ^ 2 :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have he : C * q * q ^ 2 = C * q ^ 3 := by ring
    linarith [h, hmul, he]
  -- 第二项的界（全 Λ bound）
  have hb2 : |Eform Λ (Jx θ x) R| ≤ d * q ^ 4 / 6 := by
    have h := hΛ (Jx θ x) R
    rw [hJx] at h
    have hmul : d * q * frob R ≤ d * q * (q ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ d * q)
    have he : d * q * (q ^ 3 / 6) = d * q ^ 4 / 6 := by ring
    linarith [h, hmul, he]
  -- 合成
  have hgoal : 2 * Eform Λ (Jx θ x) (fun i => -(x i ^ 2 / 2) • circleMap (θ i) + R i)
      = -(∑ i, ∑ j, Cmat Λ θ i j * x i * x j ^ 2) + 2 * Eform Λ (Jx θ x) R := by
    rw [hdecomp, hfirst]
    ring
  rw [hgoal]
  have h1 := abs_le.mp hb1
  have h2 := abs_le.mp hb2
  linarith [h1.1, h1.2, h2.1, h2.2, hq, hC0, hd0]

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.Eform_add_right
#print axioms N11Formalization.FlashLocal.Eform_smul_right
#print axioms N11Formalization.FlashLocal.frob_Jx
#print axioms N11Formalization.FlashLocal.sqrt_sum_four_le
#print axioms N11Formalization.FlashLocal.mixed_cross_lower
