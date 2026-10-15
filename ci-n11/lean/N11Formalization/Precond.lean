import N11Formalization.KrawczykMatrix

/-!
# 预条件子与残差界的**有限有理化**：消掉最后两个"语义型"前提

`KrawczykMatrix.TCSystem_unique_root_of_jacobian_enclosure` 还留了两个语义型前提：

* `hY : Function.Injective (ratMatCLM Y)`——预条件子单射；
* `hres : dist c (c - Y (TCSystem c)) + K·ρ < ρ`——残差界。

本文件把二者都化成**有限有理数据检查**：

* `ratMatCLM_comp_of_leftInverse` / `injective_ratMatCLM_of_leftInverse`：
  给出有理**左逆** `Yinv`（`Yinv·Y = I`，逐元素有理等式）即得单射——`hY` 不再需要"信"；
* `dist_sub_eq_norm`：`dist c (c − v) = ‖v‖`；
* `incrMatVec` / `mem_incrMatVec` / `norm_ratMatCLM_le`：由 `TCSystem c` 的**逐项区间包络**
  给出 `‖Y (TCSystem c)‖ ≤ η`；
* **`TCSystem_unique_root_of_full_data`**：G1 的**完全有理化形态**——所有前提都是有限有理性数据。

**真实等级**：kernel-proved，无条件（除显式有理数据前提），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-! ## 1. 左逆 ⇒ 单射 -/

theorem ratMatCLM_comp_of_leftInverse {n : ℕ} (Y Yinv : Fin n → Fin n → ℚ)
    (h : ∀ i j : Fin n, ∑ k : Fin n, Yinv i k * Y k j = (if i = j then (1 : ℚ) else 0))
    (v : Fin n → ℝ) : ratMatCLM Yinv (ratMatCLM Y v) = v := by
  funext i
  simp only [ratMatCLM_apply]
  calc ∑ k : Fin n, (Yinv i k : ℝ) * ∑ j : Fin n, (Y k j : ℝ) * v j
      = ∑ k : Fin n, ∑ j : Fin n, (Yinv i k : ℝ) * ((Y k j : ℝ) * v j) := by
        exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
    _ = ∑ j : Fin n, ∑ k : Fin n, (Yinv i k : ℝ) * ((Y k j : ℝ) * v j) := Finset.sum_comm
    _ = ∑ j : Fin n, (∑ k : Fin n, (Yinv i k : ℝ) * (Y k j : ℝ)) * v j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        simp only [mul_assoc]
    _ = ∑ j : Fin n, ((if i = j then (1 : ℚ) else 0) : ℝ) * v j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hh := congrArg (fun q : ℚ => (q : ℝ)) (h i j)
        push_cast at hh
        rw [hh]
        by_cases hij : i = j <;> simp [hij]
    _ = v i := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]; ring
        · intro j _ hj; rw [if_neg (fun hcon => hj hcon.symm)]; ring
        · intro hi; exact absurd (Finset.mem_univ i) hi

/-- **有理左逆 ⇒ 预条件子单射**（把 `hY` 变成有限有理等式检查）。 -/
theorem injective_ratMatCLM_of_leftInverse {n : ℕ} (Y Yinv : Fin n → Fin n → ℚ)
    (h : ∀ i j : Fin n, ∑ k : Fin n, Yinv i k * Y k j = (if i = j then (1 : ℚ) else 0)) :
    Function.Injective (ratMatCLM Y) := by
  intro v w hvw
  have hv := ratMatCLM_comp_of_leftInverse Y Yinv h v
  have hw := ratMatCLM_comp_of_leftInverse Y Yinv h w
  rw [hvw] at hv
  exact hv.symm.trans hw

/-! ## 2. 残差界 -/

theorem dist_sub_eq_norm {n : ℕ} (c v : Fin n → ℝ) : dist c (c - v) = ‖v‖ := by
  rw [dist_eq_norm, sub_sub_cancel]

/-- `Y` 作用于区间向量：`Σ_k Y_ik · Fm_k`。 -/
def incrMatVec {n : ℕ} (Y : Fin n → Fin n → ℚ) (Fm : Fin n → RatInterval) (i : Fin n) :
    RatInterval :=
  RatInterval.dot (Y i) Fm

theorem mem_incrMatVec {n : ℕ} {Y : Fin n → Fin n → ℚ} {Fm : Fin n → RatInterval}
    {v : Fin n → ℝ} (hv : ∀ k : Fin n, (Fm k).Mem (v k)) (i : Fin n) :
    (incrMatVec Y Fm i).Mem (ratMatCLM Y v i) := by
  have hd := RatInterval.dot_mem (c := Y i) (A := Fm) (x := v) hv
  rw [dotR_eq_sum] at hd
  simp only [incrMatVec]
  rw [ratMatCLM_apply]
  exact hd

/-- **残差界的区间化**：由 `TCSystem c` 的逐项包络给出 `‖Y (TCSystem c)‖ ≤ η`。 -/
theorem norm_ratMatCLM_le {n : ℕ} {Y : Fin n → Fin n → ℚ} {Fm : Fin n → RatInterval}
    {v : Fin n → ℝ} (hv : ∀ k : Fin n, (Fm k).Mem (v k)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ i : Fin n, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η) :
    ‖ratMatCLM Y v‖ ≤ η := by
  rw [pi_norm_le_iff_of_nonneg hη0]
  intro i
  rw [Real.norm_eq_abs]
  exact le_trans (RatInterval.mem_le_hi (RatInterval.abs_mem (mem_incrMatVec hv i))) (hη i)

/-! ## 3. G1 的完全有理化形态 -/

/-- **G1：完全有理数据 ⇒ 源系统唯一根**。

所有前提都是**有限有理性数据**：
* `Y`/`Yinv` + `hYinv`：预条件子的有理**左逆**（逐元素有理等式）⇒ 由 `injective_ratMatCLM_of_leftInverse` 得单射；
* `Jt` + `hJ`：Jacobian 的**逐元素区间包络**（`interval-ad` 的区间 AD 层产出）；
* `hsum`：`I − Y·Jt` 的**有理行和不等式**；
* `Fm` + `hFm`：`TCSystem c` 的逐项包络 ⇒ `η`；
* `hres`：`η + K·ρ < ρ`；
* 七个非退化条件（箱内非零 / 两点不重合）——区间侧给它们的箱内有理下界。 -/
theorem TCSystem_unique_root_of_full_data {c : Fin 12 → ℝ} {ρ K η : ℝ}
    (Y Yinv : Fin 12 → Fin 12 → ℚ)
    (hYinv : ∀ i j : Fin 12, ∑ k : Fin 12, Yinv i k * Y k j = (if i = j then (1 : ℚ) else 0))
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hη0 : 0 ≤ η)
    (hndRho : ∀ x ∈ closedBall c ρ, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ closedBall c ρ, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ closedBall c ρ, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ closedBall c ρ, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ closedBall c ρ, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ closedBall c ρ, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ closedBall c ρ, wPoint x ≠ ringCenter x 6)
    (Jt : Fin 12 → Fin 12 → RatInterval)
    (hJ : ∀ x ∈ closedBall c ρ, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (Fm : Fin 12 → RatInterval)
    (hFm : ∀ k : Fin 12, (Fm k).Mem (TCSystem c k))
    (hηb : ∀ i : Fin 12, (((incrMatVec Y Fm i).abs).hi : ℝ) ≤ η)
    (hres : η + K * ρ < ρ) :
    ∃! x : Fin 12 → ℝ, x ∈ closedBall c ρ ∧ TCSystem x = 0 := by
  refine TCSystem_unique_root_of_jacobian_enclosure Y
    (injective_ratMatCLM_of_leftInverse Y Yinv hYinv) hρ hK0 hK1
    hndRho hndW hndU1 hndU2 hndU3 hndU8 hndWp Jt hJ hsum ?_
  rw [dist_sub_eq_norm]
  have h1 := norm_ratMatCLM_le (Y := Y) (Fm := Fm) (v := TCSystem c) hFm hη0 hηb
  linarith

end N11Formalization
