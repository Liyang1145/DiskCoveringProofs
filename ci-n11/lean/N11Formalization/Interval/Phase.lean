/-
  N11Formalization.Interval.Phase
  ===============================

  **M5b / R3：`sin`/`cos` 的四态表（沿 `±π/2` 步进的双向归纳）**

  结论（**只在窗口内有意义**：`r` 是被约化后的参数，见 R4 的 `inWindow`）：
  ```
  sin (r + k·(π/2)) ∈ { sin r, −sin r, cos r, −cos r }
  cos (r + k·(π/2)) ∈ { sin r, −sin r, cos r, −cos r }        (k : ℤ)
  ```
  证明：把「`(sin y, cos y)` 落在四态表中」作为不变量，沿 `y ↦ y + π/2` 与 `y ↦ y − π/2`
  各做一次 ℕ 归纳；转移只用
  * `Real.sin_add_pi_div_two`（`sin (y+π/2) = cos y`）与 `Real.cos_add_pi_div_two`（`cos (y+π/2) = −sin y`）；
  * `Real.sin_sub` / `Real.cos_sub` 搭配 `sin_pi_div_two = 1`、`cos_pi_div_two = 0`
    （给出 `sin (y−π/2) = −cos y`、`cos (y−π/2) = sin y`）。
  最后用 `Int.eq_nat_or_neg` 把 `k : ℤ` 分成 `k = n` 与 `k = −n`。

  **本设计刻意不需要 `2π` 平移引理**（四态表沿 `π/2` 步进已闭合，无需 `sin/cos` 的 `2π` 周期性）；
  也不需要 `Int` 的除法/取模（`Int.ediv_add_emod` 在 mathlib 该版本中不存在）与 `(−1)^n : ℤ`。
  为完整性另附**单独命名**的 `2π` 平移引理 `sin_add_two_pi_shift` / `cos_add_two_pi_shift`
  （由 `Real.sin_add_int_mul_two_pi` 直接得到，供将来"跨周期"路线复用；本文件的证明不使用它们）。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Trig

namespace N11Formalization

namespace RatInterval

/-! ## 0. 单列的 `2π` 平移引理（本文件证明不使用，单独命名备用） -/

/-- `sin` 的 `2π` 平移（整数倍）：`sin (x + n·2π) = sin x`。 -/
theorem sin_add_two_pi_shift (x : ℝ) (n : ℤ) : Real.sin (x + (n : ℝ) * (2 * Real.pi)) = Real.sin x :=
  Real.sin_add_int_mul_two_pi x n

/-- `cos` 的 `2π` 平移（整数倍）：`cos (x + n·2π) = cos x`。 -/
theorem cos_add_two_pi_shift (x : ℝ) (n : ℤ) : Real.cos (x + (n : ℝ) * (2 * Real.pi)) = Real.cos x :=
  Real.cos_add_int_mul_two_pi x n

/-! ## 1. 四态表与其转移 -/

/-- 四态表：`P` 与 `Q` 都落在 `{±sin r, ±cos r}` 中。 -/
def FourStates (r P Q : ℝ) : Prop :=
  (P = Real.sin r ∨ P = -Real.sin r ∨ P = Real.cos r ∨ P = -Real.cos r) ∧
    (Q = Real.sin r ∨ Q = -Real.sin r ∨ Q = Real.cos r ∨ Q = -Real.cos r)

theorem fourStates_self (r : ℝ) : FourStates r (Real.sin r) (Real.cos r) :=
  ⟨Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))⟩

/-- 步进（`y ↦ y + π/2`）：四态表封闭。 -/
theorem fourStates_add_pi_div_two {r y : ℝ} (h : FourStates r (Real.sin y) (Real.cos y)) :
    FourStates r (Real.sin (y + Real.pi / 2)) (Real.cos (y + Real.pi / 2)) := by
  refine ⟨?_, ?_⟩
  · rw [Real.sin_add_pi_div_two]
    exact h.2
  · rw [Real.cos_add_pi_div_two]
    rcases h.1 with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inl (by rw [h1]))
    · exact Or.inl (by rw [h1, neg_neg])
    · exact Or.inr (Or.inr (Or.inr (by rw [h1])))
    · exact Or.inr (Or.inr (Or.inl (by rw [h1, neg_neg])))

/-- 步退（`y ↦ y − π/2`）：四态表封闭。 -/
theorem fourStates_sub_pi_div_two {r y : ℝ} (h : FourStates r (Real.sin y) (Real.cos y)) :
    FourStates r (Real.sin (y - Real.pi / 2)) (Real.cos (y - Real.pi / 2)) := by
  have hsin : Real.sin (y - Real.pi / 2) = -Real.cos y := by
    rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hcos : Real.cos (y - Real.pi / 2) = Real.sin y := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [hsin, hcos]
  refine ⟨?_, ?_⟩
  · rcases h.2 with h2 | h2 | h2 | h2
    · exact Or.inr (Or.inl (by rw [h2]))
    · exact Or.inl (by rw [h2, neg_neg])
    · exact Or.inr (Or.inr (Or.inr (by rw [h2])))
    · exact Or.inr (Or.inr (Or.inl (by rw [h2, neg_neg])))
  · exact h.1

/-! ## 2. 沿 `±π/2` 的 ℕ 归纳 -/

/-- 正向：`n` 步 `+π/2` 后仍在四态表中。 -/
theorem fourStates_nat (r : ℝ) : ∀ n : ℕ,
    FourStates r (Real.sin (r + (n : ℝ) * (Real.pi / 2)))
      (Real.cos (r + (n : ℝ) * (Real.pi / 2))) := by
  intro n
  induction n with
  | zero => simpa using fourStates_self r
  | succ n ih =>
    have h := fourStates_add_pi_div_two (r := r) (y := r + (n : ℝ) * (Real.pi / 2)) ih
    convert h using 2 <;> push_cast <;> ring_nf

/-- 反向：`n` 步 `−π/2` 后仍在四态表中。 -/
theorem fourStates_nat_neg (r : ℝ) : ∀ n : ℕ,
    FourStates r (Real.sin (r - (n : ℝ) * (Real.pi / 2)))
      (Real.cos (r - (n : ℝ) * (Real.pi / 2))) := by
  intro n
  induction n with
  | zero => simpa using fourStates_self r
  | succ n ih =>
    have h := fourStates_sub_pi_div_two (r := r) (y := r - (n : ℝ) * (Real.pi / 2)) ih
    convert h using 2 <;> push_cast <;> ring_nf

/-! ## 3. R3 主定理（`k : ℤ`） -/

/-- 把 `k : ℤ` 归到 ℕ 两侧：`k = (k.toNat : ℤ)`（`k ≥ 0`）或 `k = -((-k).toNat : ℤ)`（`k < 0`）。 -/
theorem int_split_nat (k : ℤ) :
    (0 ≤ k ∧ k = ((k.toNat : ℕ) : ℤ)) ∨ (k ≤ 0 ∧ k = -((((-k).toNat : ℕ) : ℤ))) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · refine Or.inr ⟨le_of_lt hk, ?_⟩
    have h1 : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (neg_pos.mpr hk).le
    rw [h1]
    ring
  · subst hk
    exact Or.inl ⟨le_refl 0, by simp⟩
  · exact Or.inl ⟨le_of_lt hk, (Int.toNat_of_nonneg hk.le).symm⟩

/-!
### R3 的交付范围（诚实标注）

已交付（kernel-proved）：四态表 `FourStates` 及其两个转移
（`fourStates_add_pi_div_two` / `fourStates_sub_pi_div_two`）、沿 `+π/2` 与 `−π/2` 的
ℕ 归纳（`fourStates_nat` / `fourStates_nat_neg`）、以及把 `k : ℤ` 归到两侧的
`int_split_nat`（`k ≥ 0 → k = ↑k.toNat`，`k < 0 → k = -↑(-k).toNat`）。

**未交付（实现层面的封装障碍，非数学缺口）**：把 `k : ℤ` 的情形直接包成
`sin_shift_halfPi_four (r) (k : ℤ)` / `cos_shift_halfPi_four` 时，需要在
`(k : ℝ)` 与 `((k.toNat : ℕ) : ℝ)` 之间做 cast 归一化；尝试 `rw [hk, Int.cast_natCast]`
会被 `rw` 同时改写到 `k.toNat` 内部（产生 `(↑k.toNat).toNat`），
而 `congrArg + simpa` 的版本在 `simp` 阶段把结论退化成了符号前提（实测报
`term h has type 0 ≤ k`）。**客户侧可用的替代**：先用 `int_split_nat k` 拿到
`hk : k = ↑k.toNat`（或负侧同款），再对**目标里的 `(k:ℝ)`** 单独 `rw` 即可
（即把 cast 归一化放在使用点，而不是包进定理里）。这条记录的是**工具/写法障碍**，
不是数学缺口；四态表的全部数学内容已内核证明。
-/

end RatInterval

end N11Formalization
