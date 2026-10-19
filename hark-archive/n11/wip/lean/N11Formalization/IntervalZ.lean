import N11Formalization.Interval.Phase

/-!
# R3 的 `k : ℤ` 封装（**解除 interval-core 报的 cast 归一化写法障碍**）

interval-core 在 `Interval/Phase.lean` 里已 kernel 证明四态表沿 `±π/2` 的 ℕ 归纳与
`int_split_nat`，但把 `k : ℤ` 直接包成 `sin_shift_halfPi_four` 时被 **cast 归一化**卡住：
`rw [hk, Int.cast_natCast]` 会连带改写到 `k.toNat` 内部（产生 `(↑k.toNat).toNat`），
而 `congrArg + simpa` 的版本在 `simp` 阶段把结论退化成符号前提。

**这与数学无关，是重写策略问题**：把 cast 归一化**只在 ℝ 层**做（用 `congrArg` 造出
`(k : ℝ) = (k.toNat : ℝ)`，而不是去改 `k` 本身），就完全避开了 `k.toNat` 内部被改写。

**真实等级**：kernel-proved，无条件，零 sorry、零自定义 axiom。
-/

namespace N11Formalization
namespace RatInterval

/-- **cast 归一化（非负侧）**：`k = (k.toNat : ℤ)` ⇒ `(k : ℝ) = (k.toNat : ℝ)`。
关键：用 `congrArg (· : ℤ → ℝ)` 在 ℝ 层取等式，再 `rw [Int.cast_natCast]`，
**既不去改写 `k` 本身，也不用 `simp`**（`simp` 会把 `↑k.toNat` 归一成 `max ↑k 0`，从而把结论退化成 `0 ≤ k`）。 -/
theorem int_cast_toNat {k : ℤ} (hk : k = ((k.toNat : ℕ) : ℤ)) : (k : ℝ) = (k.toNat : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) hk
  rw [Int.cast_natCast] at h
  exact h

/-- **cast 归一化（负侧）**：`k = -((-k).toNat : ℤ)` ⇒ `(k : ℝ) = -((-k).toNat : ℝ)`。 -/
theorem int_cast_negToNat {k : ℤ} (hk : k = -((((-k).toNat : ℕ) : ℤ))) :
    (k : ℝ) = -((-k).toNat : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) hk
  rw [Int.cast_neg, Int.cast_natCast] at h
  exact h

/-- **R3 的 `k : ℤ` 封装（sin/cos 版本）**：对任意整数 `k`，`(sin, cos)` 都落在四态表中。 -/
theorem sin_cos_shift_halfPi_four (r : ℝ) (k : ℤ) :
    FourStates r (Real.sin (r + (k : ℝ) * (Real.pi / 2)))
      (Real.cos (r + (k : ℝ) * (Real.pi / 2))) := by
  rcases int_split_nat k with ⟨_, hkeq⟩ | ⟨_, hkeq⟩
  · rw [int_cast_toNat hkeq]
    exact fourStates_nat r k.toNat
  · rw [int_cast_negToNat hkeq]
    convert fourStates_nat_neg r (-k).toNat using 2 <;> ring

/-- **R4 可直接用的「四可能」读数（sin）**：`k` 平移后的 `sin` 必等于 `±sin r` 或 `±cos r`。 -/
theorem sin_shift_halfPi_mem (r : ℝ) (k : ℤ) :
    Real.sin (r + (k : ℝ) * (Real.pi / 2)) = Real.sin r
      ∨ Real.sin (r + (k : ℝ) * (Real.pi / 2)) = -Real.sin r
      ∨ Real.sin (r + (k : ℝ) * (Real.pi / 2)) = Real.cos r
      ∨ Real.sin (r + (k : ℝ) * (Real.pi / 2)) = -Real.cos r :=
  (sin_cos_shift_halfPi_four r k).1

/-- **R4 可直接用的「四可能」读数（cos）**。 -/
theorem cos_shift_halfPi_mem (r : ℝ) (k : ℤ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = Real.sin r
      ∨ Real.cos (r + (k : ℝ) * (Real.pi / 2)) = -Real.sin r
      ∨ Real.cos (r + (k : ℝ) * (Real.pi / 2)) = Real.cos r
      ∨ Real.cos (r + (k : ℝ) * (Real.pi / 2)) = -Real.cos r :=
  (sin_cos_shift_halfPi_four r k).2

end RatInterval
end N11Formalization
