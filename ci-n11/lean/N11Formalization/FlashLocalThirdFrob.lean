import Mathlib
import N11Formalization.FlashLocalThird

/-!
# FlashLocal — 120 局部叶承重链 · 第七环：三阶余项的**族级（九锚 Frobenius）聚合**

独立新件（**不修改冻结的 `FlashLocalThird`**，按 Lead 2026-09-30 指示）。
`FlashLocalThird` 给**逐锚**三阶余项 `‖u(a+x) − u(a) − x u'(a) + (x²/2)u(a)‖ ≤ |x|³/6`；
本件把它聚合成**族级**形态（源要的 `‖U(x) − U − v + (x²/2)U‖ ≤ q³/6`，`q² = Σ_i x_i²`）：

* `thirdRemSq_eq_pointNorm` —— 逐锚 `Point` 桥（真实 `circleMap`/`circleTangent`）；
* `sum_six_le_cube_sum` —— `Σ x_i^6 ≤ (Σ x_i^2)^3`（常数 1；用第一环 `sum_four_le_sq_sum`）；
* `anchorThird_frob_le` —— 平方形态 `Σ_i ‖R_i‖² ≤ (Σ_i x_i²)^3 / 36`；
* `anchorThird_frob_norm_le` —— **范数形态 `‖R‖_F ≤ (Σ_i x_i²)^{3/2} / 6 = q³/6`**。

**scope**：全部对任意 `θ x : Fin 9 → ℝ` 无条件；不含 `Λ`、不含响应、不含 `H0`、不含图/叶。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset

/-- **Point 桥**：逐锚三阶残差的 `Point` 范数平方 = `FlashLocalThird.chartThirdSq`。 -/
theorem thirdRemSq_eq_pointNorm (a x : ℝ) :
    ‖circleMap (a + x) - circleMap a - x • circleTangent a + (x ^ 2 / 2) • circleMap a‖ ^ 2
      = chartThirdSq a x := by
  rw [norm_sq_two]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, circleMap_apply_zero,
    circleMap_apply_one, circleTangent_apply_zero, circleTangent_apply_one, chartThirdSq]
  ring

/-- `Σ x_i^6 ≤ (Σ x_i^2)^3`（常数 1 一步；用 `sum_four_le_sq_sum`）。 -/
theorem sum_six_le_cube_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∑ i, x i ^ 6 ≤ (∑ i, x i ^ 2) ^ 3 := by
  have h1 : ∀ i, x i ^ 6 ≤ (∑ j, x j ^ 2) * x i ^ 4 := by
    intro i
    have hle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    calc x i ^ 6 = x i ^ 2 * x i ^ 4 := by ring
      _ ≤ (∑ j, x j ^ 2) * x i ^ 4 := mul_le_mul_of_nonneg_right hle (by positivity)
  calc ∑ i, x i ^ 6 ≤ ∑ i, (∑ j, x j ^ 2) * x i ^ 4 := Finset.sum_le_sum (fun i _ => h1 i)
    _ = (∑ j, x j ^ 2) * ∑ i, x i ^ 4 := by rw [Finset.mul_sum]
    _ ≤ (∑ j, x j ^ 2) * (∑ i, x i ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_four_le_sq_sum x) (by positivity)
    _ = (∑ i, x i ^ 2) ^ 3 := by ring

/-- **族级聚合（平方形态）**：`Σ_i ‖R_i‖² ≤ (Σ_i x_i²)^3 / 36`。 -/
theorem anchorThird_frob_le (θ x : Fin 9 → ℝ) :
    ∑ i, ‖circleMap (θ i + x i) - circleMap (θ i) - x i • circleTangent (θ i)
        + (x i ^ 2 / 2) • circleMap (θ i)‖ ^ 2 ≤ (∑ i, x i ^ 2) ^ 3 / 36 := by
  have h : ∀ i, ‖circleMap (θ i + x i) - circleMap (θ i) - x i • circleTangent (θ i)
      + (x i ^ 2 / 2) • circleMap (θ i)‖ ^ 2 ≤ (x i ^ 3 / 6) ^ 2 := by
    intro i
    rw [thirdRemSq_eq_pointNorm]
    exact chartThirdSq_le (θ i) (x i)
  calc ∑ i, ‖circleMap (θ i + x i) - circleMap (θ i) - x i • circleTangent (θ i)
        + (x i ^ 2 / 2) • circleMap (θ i)‖ ^ 2
      ≤ ∑ i, (x i ^ 3 / 6) ^ 2 := Finset.sum_le_sum (fun i _ => h i)
    _ = ∑ i, x i ^ 6 / 36 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = (∑ i, x i ^ 6) / 36 := by rw [Finset.sum_div]
    _ ≤ (∑ i, x i ^ 2) ^ 3 / 36 := by
        have hsum := sum_six_le_cube_sum x
        linarith

/-- **族级聚合（范数形态）**：`‖R‖_F ≤ (Σ_i x_i²)^{3/2} / 6`，即源要的 `q³/6`
（`q = sqrt (Σ_i x_i²)`）。 -/
theorem anchorThird_frob_norm_le (θ x : Fin 9 → ℝ) :
    Real.sqrt (∑ i, ‖circleMap (θ i + x i) - circleMap (θ i) - x i • circleTangent (θ i)
        + (x i ^ 2 / 2) • circleMap (θ i)‖ ^ 2)
      ≤ (∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) / 6 := by
  have h := anchorThird_frob_le θ x
  have hs : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hcube : ((∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) / 6) ^ 2
      = (∑ i, x i ^ 2) ^ 3 / 36 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hs]
    ring
  calc Real.sqrt (∑ i, ‖circleMap (θ i + x i) - circleMap (θ i)
        - x i • circleTangent (θ i) + (x i ^ 2 / 2) • circleMap (θ i)‖ ^ 2)
      ≤ Real.sqrt (((∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) / 6) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [hcube]; exact h)
    _ = |(∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) / 6| := Real.sqrt_sq_eq_abs _
    _ = (∑ i, x i ^ 2) * Real.sqrt (∑ i, x i ^ 2) / 6 := abs_of_nonneg (by positivity)

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.thirdRemSq_eq_pointNorm
#print axioms N11Formalization.FlashLocal.sum_six_le_cube_sum
#print axioms N11Formalization.FlashLocal.anchorThird_frob_le
#print axioms N11Formalization.FlashLocal.anchorThird_frob_norm_le
