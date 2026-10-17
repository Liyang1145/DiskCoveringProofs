import N11Formalization.Smoothness

/-!
# C² 构件：`fderiv ℝ residualFun` 的可微性（G1 义务 (2) 的二阶)

`TCSystem` 的乘子块 `adjointBlock` 用 `fderiv ℝ residualFun z`，所以 `TCSystem` 关于 `u` 的可微性
需要 **`residualFun` 的 C²**。本文件把这一环 kernel 化：

* `pad12` / `residualFun_eq`：把 `residualFun` 写成 `residual ∘ pad12`（`pad12` 线性）；
* `contDiffAt_pad12`：`pad12` 光滑（逐坐标是投影或常函数）；
* `contDiffAt_residualFun`：`residualFun` 在非退化条件下 C^∞（由 `contDiffAt_residual` 复合得到）；
* **`contDiffAt_fderiv_residualFun`**：`ContDiffAt ℝ (m+1) residualFun z ⇒ ContDiffAt ℝ m (fun z => fderiv ℝ residualFun z) z`
  —— 用 `ContDiffAt.fderiv` 取 `f := fun _ => residualFun`、`g := id`，即
  `FunLike.uncurry f (p) = residualFun p.2`，故只需 `residualFun` 自身的光滑性。

**真实等级**：kernel-proved，无条件（除显式非退化假设），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-- 把 `Fin 7 → ℝ` 补零成 `Fin 12 → ℝ`（与 `residualFun` 定义里的 `if` 逐字相同）。 -/
def pad12 (z : Fin 7 → ℝ) : Fin 12 → ℝ :=
  fun i => if h : (i : ℕ) < 7 then z ⟨(i : ℕ), h⟩ else 0

theorem residualFun_eq (z : Fin 7 → ℝ) : residualFun z = residual (pad12 z) := rfl

/-- `pad12` 逐坐标是投影或常函数 ⇒ 光滑。 -/
theorem contDiffAt_pad12 {n : WithTop ℕ∞} (z : Fin 7 → ℝ) :
    ContDiffAt ℝ n (fun w : Fin 7 → ℝ => pad12 w) z := by
  rw [contDiffAt_pi]
  intro i
  by_cases h : (i : ℕ) < 7
  · have : (fun w : Fin 7 → ℝ => pad12 w i) = fun w => w ⟨(i : ℕ), h⟩ := by
      funext w
      simp only [pad12, dif_pos h]
    rw [this]
    exact (ContinuousLinearMap.proj (⟨(i : ℕ), h⟩ : Fin 7) :
      (Fin 7 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
  · have : (fun w : Fin 7 → ℝ => pad12 w i) = fun _ => (0 : ℝ) := by
      funext w
      simp only [pad12, dif_neg h]
    rw [this]
    exact contDiffAt_const

/-- **`residualFun` 光滑**（在 `pad12 z` 上的非退化条件下）。 -/
theorem contDiffAt_residualFun {n : WithTop ℕ∞} (z : Fin 7 → ℝ)
    (hrho : ∀ j : Fin 9, ((pad12 z) 6) ^ 2 - (Real.sin (angleVec (pad12 z) j)) ^ 2 ≠ 0)
    (hradW : ((pad12 z) 6) ^ 2 - (((pad12 z) 5 - (pad12 z) 4) / 2) ^ 2 ≠ 0)
    (hU1 : Uvec (pad12 z) 1 ≠ hub1 (pad12 z))
    (hU2 : Uvec (pad12 z) 2 ≠ hub0 (pad12 z))
    (hU3 : Uvec (pad12 z) 3 ≠ hub0 (pad12 z))
    (hU8 : Uvec (pad12 z) 8 ≠ hub1 (pad12 z))
    (hW : wPoint (pad12 z) ≠ ringCenter (pad12 z) 6) (i : Fin 5) :
    ContDiffAt ℝ n (fun w : Fin 7 → ℝ => residualFun w i) z := by
  rw [show (fun w : Fin 7 → ℝ => residualFun w i)
      = fun w => residual (pad12 w) i from funext fun w => by rw [residualFun_eq]]
  exact ContDiffAt.comp (x := z) (g := fun u : Fin 12 → ℝ => residual u i) (f := pad12)
    (contDiffAt_residual (n := n) i (pad12 z) hrho hradW hU1 hU2 hU3 hU8 hW)
    (contDiffAt_pad12 (n := n) z)

/-- **C² 构件**：`residualFun` 的 `fderiv` 光滑。

证明用 `ContDiffAt.fderiv` 取 `f := fun _ => residualFun`、`g := id`：
此时 `Function.uncurry f (p) = residualFun p.2`，故只需 `residualFun` 自身的 `m+1` 阶光滑性。 -/
theorem contDiffAt_fderiv_residualFun {m : WithTop ℕ∞} {z : Fin 7 → ℝ}
    (h : ContDiffAt ℝ (m + 1) (fun w : Fin 7 → ℝ => residualFun w) z) :
    ContDiffAt ℝ m (fun w : Fin 7 → ℝ => fderiv ℝ residualFun w) z := by
  have hg : ContDiffAt ℝ m (fun x : Fin 7 → ℝ => x) z := contDiffAt_id
  have hun : ContDiffAt ℝ (m + 1)
      (fun p : (Fin 7 → ℝ) × (Fin 7 → ℝ) => residualFun p.2) (z, z) :=
    ContDiffAt.comp (x := (z, z)) (g := fun w : Fin 7 → ℝ => residualFun w)
      (f := fun p : (Fin 7 → ℝ) × (Fin 7 → ℝ) => p.2) h
      ((ContinuousLinearMap.snd ℝ (Fin 7 → ℝ) (Fin 7 → ℝ)).contDiff.contDiffAt)
  exact ContDiffAt.fderiv (𝕜 := ℝ) (x₀ := z) (m := m) (n := m + 1)
    (f := fun _ : Fin 7 → ℝ => residualFun)
    (g := fun x : Fin 7 → ℝ => x) hun hg le_rfl

end N11Formalization
