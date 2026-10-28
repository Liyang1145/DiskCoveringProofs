import N11Formalization.SmoothnessC2

/-!
# `TCSystem` 的可微性 = G1 义务 (2) 的收口

把 `TCSystem` 的可微性归约到**两条已经付清**的前提：

* `hres`：`residual` 的每个分量在 `x` 处可微（由 `Smoothness.contDiffAt_residual` 给出）；
* `hadj`：`z ↦ fderiv ℝ residualFun z` 在 `first7 x` 处可微（由
  `SmoothnessC2.contDiffAt_fderiv_residualFun` + `contDiffAt_residualFun` 给出）。

`TCSystem` 的前 5 个分量就是 `residual`；其余分量是
`(if i = 11 then 1 else 0) - adjointBlock (first7 u) (last5 u) (i − 5)`，
而 `adjointBlock z lam i = Σ_k lam k · (fderiv ℝ residualFun z (single i 1)) k`，
故它关于 `z` 的可微性正需要上面那条 `hadj`。

**真实等级**：kernel-proved，无条件（除两条显式前提），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

theorem differentiableAt_first7 (x : Fin 12 → ℝ) :
    DifferentiableAt ℝ (fun u : Fin 12 → ℝ => first7 u) x := by
  rw [differentiableAt_pi]
  intro i
  simp only [first7]
  exact (ContinuousLinearMap.proj (⟨(i : ℕ), by omega⟩ : Fin 12) :
    (Fin 12 → ℝ) →L[ℝ] ℝ).differentiableAt

theorem differentiableAt_last5 (x : Fin 12 → ℝ) :
    DifferentiableAt ℝ (fun u : Fin 12 → ℝ => last5 u) x := by
  rw [differentiableAt_pi]
  intro i
  simp only [last5]
  exact (ContinuousLinearMap.proj (⟨(i : ℕ) + 7, by omega⟩ : Fin 12) :
    (Fin 12 → ℝ) →L[ℝ] ℝ).differentiableAt

theorem differentiableAt_coord (x : Fin 12 → ℝ) (i : Fin 12) :
    DifferentiableAt ℝ (fun u : Fin 12 → ℝ => u i) x :=
  (ContinuousLinearMap.proj i : (Fin 12 → ℝ) →L[ℝ] ℝ).differentiableAt

/-- **`adjointBlock` 在 `x` 处可微**（前提：`fderiv ℝ residualFun` 在 `first7 x` 处可微）。 -/
theorem differentiableAt_adjointBlock (x : Fin 12 → ℝ)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) (first7 x))
    (i : Fin 7) :
    DifferentiableAt ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x := by
  rw [show (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      = fun u => ∑ k : Fin 5,
          last5 u k * (fderiv ℝ residualFun (first7 u) (Pi.single i 1)) k from
        funext fun u => rfl]
  have hterm : ∀ k : Fin 5, DifferentiableAt ℝ (fun u : Fin 12 → ℝ =>
      last5 u k * (fderiv ℝ residualFun (first7 u) (Pi.single i 1)) k) x := by
    intro k
    have hk : DifferentiableAt ℝ (fun u : Fin 12 → ℝ => last5 u k) x :=
      (ContinuousLinearMap.proj k : (Fin 5 → ℝ) →L[ℝ] ℝ).differentiableAt.comp x
        (differentiableAt_last5 x)
    refine hk.mul ?_
    have h1 : DifferentiableAt ℝ
        (fun u : Fin 12 → ℝ => fderiv ℝ residualFun (first7 u)) x :=
      hadj.comp x (differentiableAt_first7 x)
    have h2 : DifferentiableAt ℝ
        (fun u : Fin 12 → ℝ => (fderiv ℝ residualFun (first7 u)) (Pi.single i 1)) x := by
      have hA : DifferentiableAt ℝ
          (fun A : (Fin 7 → ℝ) →L[ℝ] (Fin 5 → ℝ) => A (Pi.single i 1))
          (fderiv ℝ residualFun (first7 x)) :=
        (ContinuousLinearMap.apply ℝ (Fin 5 → ℝ) (Pi.single i 1)).differentiableAt
      exact hA.comp x h1
    exact (ContinuousLinearMap.proj k : (Fin 5 → ℝ) →L[ℝ] ℝ).differentiableAt.comp x h2
  exact DifferentiableAt.sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun k : Fin 5 => fun u : Fin 12 → ℝ =>
      last5 u k * (fderiv ℝ residualFun (first7 u) (Pi.single i 1)) k)
    (fun k _ => hterm k)

/-- **G1 义务 (2) 的收口**：`TCSystem` 在 `x` 处可微。 -/
theorem differentiableAt_TCSystem (x : Fin 12 → ℝ)
    (hres : ∀ i : Fin 5, DifferentiableAt ℝ (fun u : Fin 12 → ℝ => residual u i) x)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) (first7 x)) :
    DifferentiableAt ℝ TCSystem x := by
  rw [differentiableAt_pi]
  intro i
  by_cases hi : (i : ℕ) < 5
  · have : (fun u : Fin 12 → ℝ => TCSystem u i)
        = fun u => residual u ⟨(i : ℕ), hi⟩ := by
      funext u
      simp only [TCSystem, dif_pos hi]
    rw [this]
    exact hres ⟨(i : ℕ), hi⟩
  · have : (fun u : Fin 12 → ℝ => TCSystem u i)
        = fun u => ((if (i : ℕ) = 11 then (1 : ℝ) else 0)
            - adjointBlock (first7 u) (last5 u) ⟨(i : ℕ) - 5, by omega⟩) := by
      funext u
      simp only [TCSystem, dif_neg hi]
    rw [this]
    exact (differentiableAt_const (c := (if (i : ℕ) = 11 then (1 : ℝ) else 0))).sub
      (differentiableAt_adjointBlock x hadj ⟨(i : ℕ) - 5, by omega⟩)

end N11Formalization
