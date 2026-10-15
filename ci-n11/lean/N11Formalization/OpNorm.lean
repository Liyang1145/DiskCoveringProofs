import Mathlib

/-!
# 逐元素包络 ⇒ ∞-算子范数界（区间侧 `J` 的包络到 Krawczyk `hbound` 的桥）

`KrawczykDeriv.lean` 的 `hbound` 形如 `‖I − Y.comp (fderiv F x)‖ ≤ K`，
而区间侧能直接算出来的是该算子的**矩阵表示逐元素**的区间包络与**行和**上界。
本文件补上这一环（不依赖任何区间库，纯实分析 + 有限和）：

* `opNorm_le_rowSum`：`‖A‖ ≤ Q` ⟸ `∀ i, Σ_j |A (single j 1) i| ≤ Q`（用 `opNorm_le_bound`）；
* `abs_le_max_abs`：`lo ≤ x ≤ hi ⇒ |x| ≤ max |lo| |hi|`；
* `opNorm_le_of_entry_bounds`：逐元素包络 + 行和上界 ⇒ `‖A‖ ≤ Q`。

**真实等级**：kernel-proved，无条件，零 sorry、零自定义 axiom。
-/

namespace N11Formalization

/-- `lo ≤ x ≤ hi ⇒ |x| ≤ max |lo| |hi|`。 -/
theorem abs_le_max_abs {lo hi x : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    |x| ≤ max |lo| |hi| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_trans h2 (le_trans (le_abs_self hi) (le_max_right _ _))
  · rw [abs_of_nonpos hx]
    have hneg : -x ≤ -lo := by linarith
    exact le_trans hneg (le_trans (neg_le_abs lo) (le_max_left _ _))

/-- **∞-算子范数行和界**：`‖A‖ ≤ Q` ⟸ 各行的坐标绝对值之和 `≤ Q`。

证明：`v = Σ_j v_j • single j 1`，故 `A v i = Σ_j v_j · A(single j 1) i`；
再有 `|v_j| ≤ ‖v‖`（Pi 范数 = sup 范数）与 `|Σ ≤ Σ| · |`，最后由 `opNorm_le_bound` 收口。 -/
theorem opNorm_le_rowSum {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {Q : ℝ} (hQ : 0 ≤ Q)
    (hrow : ∀ i : Fin n, ∑ j : Fin n, |A (Pi.single j 1) i| ≤ Q) :
    ‖A‖ ≤ Q := by
  refine ContinuousLinearMap.opNorm_le_bound A hQ fun v => ?_
  have hv : ∀ i : Fin n, |v i| ≤ ‖v‖ := fun i => by
    have h := norm_le_pi_norm v i
    rwa [Real.norm_eq_abs] at h
  have hdecomp : v = ∑ j : Fin n, v j • Pi.single j 1 := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hexp : ∀ i : Fin n, A v i = ∑ j : Fin n, v j * A (Pi.single j 1) i := by
    intro i
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, hexp i]
  calc |∑ j : Fin n, v j * A (Pi.single j 1) i|
      ≤ ∑ j : Fin n, |v j * A (Pi.single j 1) i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |v j| * |A (Pi.single j 1) i| := by simp [abs_mul]
    _ ≤ ∑ j : Fin n, ‖v‖ * |A (Pi.single j 1) i| :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hv j) (abs_nonneg _)
    _ = ‖v‖ * ∑ j : Fin n, |A (Pi.single j 1) i| := by rw [Finset.mul_sum]
    _ ≤ ‖v‖ * Q := mul_le_mul_of_nonneg_left (hrow i) (norm_nonneg _)
    _ = Q * ‖v‖ := by ring

/-- **逐元素区间包络 ⇒ ∞-算子范数界**（区间侧到 `hbound` 的直接接口）。

若矩阵表示 `A_{ij} = A (single j 1) i` 被逐元素夹在 `[lo i j, hi i j]` 之间，
且各行 `Σ_j max |lo i j| |hi i j| ≤ Q`，则 `‖A‖ ≤ Q`。 -/
theorem opNorm_le_of_entry_bounds {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {Q : ℝ} (hQ : 0 ≤ Q)
    (lo hi : Fin n → Fin n → ℝ)
    (henc : ∀ i j : Fin n, lo i j ≤ A (Pi.single j 1) i ∧ A (Pi.single j 1) i ≤ hi i j)
    (hsum : ∀ i : Fin n, ∑ j : Fin n, max |lo i j| |hi i j| ≤ Q) :
    ‖A‖ ≤ Q :=
  opNorm_le_rowSum A hQ fun i =>
    le_trans (Finset.sum_le_sum fun j _ => abs_le_max_abs (henc i j).1 (henc i j).2) (hsum i)

end N11Formalization
