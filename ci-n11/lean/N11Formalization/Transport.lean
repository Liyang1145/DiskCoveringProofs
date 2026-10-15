import N11Formalization.TCSystemSmooth

/-!
# 搬运引理：把 G1 义务 (2) 的两条前提并成一条

`differentiableAt_TCSystem` 的两条前提在物理上是同一组非退化条件，但表述在**两个不同点**上：
* `hres` 的条件在 `x : Fin 12 → ℝ` 上；
* `hadj` 的条件在 `pad12 (first7 x)` 上。

本文件证明 **`pad12 (first7 x)` 与 `x` 在前 7 个坐标上逐点相等**（`pad12_first7_*`），
并由此把 `residual` 及其全部构件（`angleVec`/`thetaOf`/`rhoK`/`hub0`/`hub1`/`wPoint`/`ringCenter`/`arcEnd`/`Uvec`）
的两种表述逐条搬平，最终给出**单条前提**的 `differentiableAt_TCSystem_of_conditions`。

**真实等级**：kernel-proved，无条件，零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-! ## 1. 前 7 个坐标逐点相等 -/

@[simp] theorem pad12_first7_0 (x : Fin 12 → ℝ) : pad12 (first7 x) 0 = x 0 := by
  simp [pad12, first7]
@[simp] theorem pad12_first7_1 (x : Fin 12 → ℝ) : pad12 (first7 x) 1 = x 1 := by
  simp [pad12, first7]
@[simp] theorem pad12_first7_2 (x : Fin 12 → ℝ) : pad12 (first7 x) 2 = x 2 := by
  simp [pad12, first7]
@[simp] theorem pad12_first7_3 (x : Fin 12 → ℝ) : pad12 (first7 x) 3 = x 3 := by
  simp [pad12, first7]
@[simp] theorem pad12_first7_4 (x : Fin 12 → ℝ) : pad12 (first7 x) 4 = x 4 := by
  simp [pad12, first7]
@[simp] theorem pad12_first7_5 (x : Fin 12 → ℝ) : pad12 (first7 x) 5 = x 5 := by
  simp [pad12, first7]
@[simp] theorem pad12_first7_6 (x : Fin 12 → ℝ) : pad12 (first7 x) 6 = x 6 := by
  simp [pad12, first7]

/-! ## 2. 构件逐条搬平 -/

theorem angleVec_transport (x : Fin 12 → ℝ) : angleVec (pad12 (first7 x)) = angleVec x := by
  funext k
  fin_cases k <;> simp [angleVec]

theorem thetaOf_transport (x : Fin 12 → ℝ) (k : Fin 9) :
    thetaOf (angleVec (pad12 (first7 x))) k = thetaOf (angleVec x) k := by
  rw [angleVec_transport]

theorem rhoK_transport (x : Fin 12 → ℝ) (k : Fin 9) :
    rhoK (pad12 (first7 x)) k = rhoK x k := by
  simp only [rhoK]
  rw [angleVec_transport, pad12_first7_6]

theorem hub0_transport (x : Fin 12 → ℝ) : hub0 (pad12 (first7 x)) = hub0 x := by
  simp only [hub0]
  rw [pad12_first7_4]

theorem hub1_transport (x : Fin 12 → ℝ) : hub1 (pad12 (first7 x)) = hub1 x := by
  simp only [hub1]
  rw [pad12_first7_5]

theorem ringCenter_transport (x : Fin 12 → ℝ) (k : Fin 9) :
    ringCenter (pad12 (first7 x)) k = ringCenter x k := by
  simp only [ringCenter]
  rw [rhoK_transport x k, thetaOf_transport x k]

theorem arcEnd_transport (x : Fin 12 → ℝ) (k : Fin 9) :
    arcEnd (pad12 (first7 x)) k = arcEnd x k := by
  simp only [arcEnd]
  rw [thetaOf_transport x k, angleVec_transport]

theorem Uvec_transport (x : Fin 12 → ℝ) (k : Fin 9) :
    Uvec (pad12 (first7 x)) k = Uvec x k := by
  simp only [Uvec]
  rw [ringCenter_transport x k, ringCenter_transport x (k + 1), arcEnd_transport x k]

theorem wPoint_transport (x : Fin 12 → ℝ) : wPoint (pad12 (first7 x)) = wPoint x := by
  simp only [wPoint]
  rw [pad12_first7_4, pad12_first7_5, pad12_first7_6]

theorem residual_transport (x : Fin 12 → ℝ) : residual (pad12 (first7 x)) = residual x := by
  simp only [residual]
  rw [Uvec_transport x 1, Uvec_transport x 2, Uvec_transport x 3, Uvec_transport x 8,
    hub1_transport x, hub0_transport x, wPoint_transport x, ringCenter_transport x 6,
    pad12_first7_6]

/-! ## 3. 单条前提的收口 -/

/-- `residualFun` 在 `first7 x` 处的光滑性，条件只写在 `x` 上。 -/
theorem contDiffAt_residualFun_first7 {n : WithTop ℕ∞} (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hradW : (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hU1 : Uvec x 1 ≠ hub1 x) (hU2 : Uvec x 2 ≠ hub0 x)
    (hU3 : Uvec x 3 ≠ hub0 x) (hU8 : Uvec x 8 ≠ hub1 x)
    (hW : wPoint x ≠ ringCenter x 6) (i : Fin 5) :
    ContDiffAt ℝ n (fun z : Fin 7 → ℝ => residualFun z i) (first7 x) := by
  refine contDiffAt_residualFun (n := n) (first7 x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ i
  · intro j
    rw [pad12_first7_6, angleVec_transport]
    exact hrho j
  · rw [pad12_first7_6, pad12_first7_5, pad12_first7_4]
    exact hradW
  · rw [Uvec_transport x 1, hub1_transport x]
    exact hU1
  · rw [Uvec_transport x 2, hub0_transport x]
    exact hU2
  · rw [Uvec_transport x 3, hub0_transport x]
    exact hU3
  · rw [Uvec_transport x 8, hub1_transport x]
    exact hU8
  · rw [wPoint_transport x, ringCenter_transport x 6]
    exact hW

/-- **G1 义务 (2) 的单条前提收口**：`TCSystem` 在 `x` 处可微，
非退化条件只写在 `x` 上（不再需要 `pad12 (first7 x)` 的第二套）。 -/
theorem differentiableAt_TCSystem_of_conditions (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hradW : (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hU1 : Uvec x 1 ≠ hub1 x) (hU2 : Uvec x 2 ≠ hub0 x)
    (hU3 : Uvec x 3 ≠ hub0 x) (hU8 : Uvec x 8 ≠ hub1 x)
    (hW : wPoint x ≠ ringCenter x 6) :
    DifferentiableAt ℝ TCSystem x := by
  refine differentiableAt_TCSystem x ?_ ?_
  · intro i
    exact (contDiffAt_residual (n := 1) i x hrho hradW hU1 hU2 hU3 hU8 hW).differentiableAt
      (by norm_num)
  · have h2 : ContDiffAt ℝ ((1 : WithTop ℕ∞) + 1)
        (fun w : Fin 7 → ℝ => residualFun w) (first7 x) := by
      rw [contDiffAt_pi]
      intro i
      exact contDiffAt_residualFun_first7 (n := (1 : WithTop ℕ∞) + 1) x hrho hradW hU1 hU2 hU3
        hU8 hW i
    exact (contDiffAt_fderiv_residualFun (m := 1) h2).differentiableAt (by norm_num)

end N11Formalization
