import Mathlib
import N11Formalization.Interval.Core

/-!
# sin/cos 的**高阶有理端点**，走一条不需要阶乘算术的均匀归纳

**目标**（替代 interval-core 的 route (3)）：给出显式有理多项式端点 `sinLoN/sinHiN`，
其包络宽度在 `|q| ≤ 0.3843` 上远低于 `9.956e-10`。

**关键简化**：不证 sharp Taylor 余项 `|x|^(n+1)/(n+1)!`，而证**更弱但够用**的一对界

* `A(m) : |Real.sin x − sinT m x| ≤ |x|^(2m+1)`
* `B(m) : |Real.cos x − cosT m x| ≤ |x|^(2m)`

（`sinT m`/`cosT m` 是前 `m` 个奇/偶次 Taylor 项）。这一对界由**一条对 `m` 的均匀归纳**给出：

* `A(0)`：`|Real.sin x| ≤ |x|`，即 mathlib 的 `Real.abs_sin_le_abs`；
* `A(m) → B(m+1)`：对 `g := cos − cosT (m+1)` 用 MVT，`g' = −(sin − sinT m)`，故 `|g'| ≤ |y|^(2m+1)`；
* `B(m+1) → A(m+1)`：对 `h := sin − sinT (m+1)` 用 MVT，`h' = cos − cosT (m+1)`，故 `|h'| ≤ |y|^(2m+2)`。

**代价**：比 sharp Taylor 弱 `(2m+1)!` 倍。**但 `m = 13` 时 `|x|^27 = 6.1e-12`** 对 `|x| ≤ 0.3843`
已低于阈值 `9.956e-10` 约 **80 倍**；`m = 14` 给 `|x|^29 = 9.0e-13`（约 1100 倍余量）。
故**无需**任何阶乘算术——这比 interval-core 的 route (3) 省掉"阶乘整理"整块。

**真实等级**：kernel-proved，零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Finset

/-- `sin` 的前 `m` 个奇次 Taylor 项。 -/
noncomputable def sinT (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℝ)

/-- `cos` 的前 `m` 个偶次 Taylor 项。 -/
noncomputable def cosT (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * x ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ)

@[simp] theorem sinT_zero (x : ℝ) : sinT 0 x = 0 := by simp [sinT]
@[simp] theorem cosT_zero (x : ℝ) : cosT 0 x = 0 := by simp [cosT]

theorem cosT_succ_zero (m : ℕ) : cosT (m + 1) 0 = 1 := by
  rw [cosT, Finset.sum_range_succ']
  simp

theorem sinT_succ_zero (m : ℕ) : sinT (m + 1) 0 = 0 := by
  rw [sinT, Finset.sum_range_succ']
  simp

/-! ## 逐项导数 -/

theorem hasDerivAt_sinTerm (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℝ))
      ((-1 : ℝ) ^ k * x ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ)) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1))
      (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k + 1 - 1)) x := hasDerivAt_pow (2 * k + 1) x
  rw [show 2 * k + 1 - 1 = 2 * k from by omega] at hpow
  have hmul : HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k + 1))
      ((-1 : ℝ) ^ k * (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k))) x :=
    HasDerivAt.const_mul ((-1 : ℝ) ^ k) hpow
  have hdiv := hmul.div_const (((Nat.factorial (2 * k + 1) : ℕ) : ℝ))
  refine hdiv.congr_deriv ?_
  have hf : ((2 * k + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) + 1 := by push_cast; ring
  have hfact : ((Nat.factorial (2 * k + 1) : ℕ) : ℝ)
      = (((2 * k : ℕ) : ℝ) + 1) * ((Nat.factorial (2 * k) : ℕ) : ℝ) := by
    rw [show Nat.factorial (2 * k + 1) = (2 * k + 1) * Nat.factorial (2 * k) from
      Nat.factorial_succ (2 * k)]
    push_cast
    ring
  have hne : (((2 * k : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  have hne2 : ((Nat.factorial (2 * k) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k)
  rw [hfact, hf]
  field_simp

theorem hasDerivAt_cosTerm (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ))
      ((-1 : ℝ) ^ k * (((2 * k : ℕ) : ℝ) * x ^ (2 * k - 1)) / ((Nat.factorial (2 * k) : ℕ) : ℝ)) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ (2 * k))
      (((2 * k : ℕ) : ℝ) * x ^ (2 * k - 1)) x := hasDerivAt_pow (2 * k) x
  exact (HasDerivAt.const_mul ((-1 : ℝ) ^ k) hpow).div_const _

/-! ## 部分和的导数 -/

theorem hasDerivAt_sinT (m : ℕ) (x : ℝ) : HasDerivAt (fun y => sinT m y) (cosT m x) x := by
  have h := HasDerivAt.sum (u := Finset.range m) (A := fun k y =>
      (-1 : ℝ) ^ k * y ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℝ))
      (A' := fun k => (-1 : ℝ) ^ k * x ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ))
      (fun k _ => hasDerivAt_sinTerm k x)
  have hfun : (∑ k ∈ Finset.range m, fun y : ℝ =>
      (-1 : ℝ) ^ k * y ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℝ))
      = fun y => sinT m y := by
    funext y
    simp only [sinT, Finset.sum_apply]
  have hd : (∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * x ^ (2 * k) /
      ((Nat.factorial (2 * k) : ℕ) : ℝ)) = cosT m x := rfl
  rw [hfun, hd] at h
  exact h

/-- `(cosT (m+1))' = −sinT m`（`k = 0` 项导数为 0，余下令 `j = k-1`）。 -/
theorem hasDerivAt_cosT_succ (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y => cosT (m + 1) y) (-(sinT m x)) x := by
  have h := HasDerivAt.sum (u := Finset.range (m + 1)) (A := fun k y =>
      (-1 : ℝ) ^ k * y ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ))
      (A' := fun k => (-1 : ℝ) ^ k * (((2 * k : ℕ) : ℝ) * x ^ (2 * k - 1)) /
        ((Nat.factorial (2 * k) : ℕ) : ℝ))
      (fun k _ => hasDerivAt_cosTerm k x)
  have hfun : (∑ k ∈ Finset.range (m + 1), fun y : ℝ =>
      (-1 : ℝ) ^ k * y ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ))
      = fun y => cosT (m + 1) y := by
    funext y
    simp only [cosT, Finset.sum_apply]
  rw [hfun] at h
  refine h.congr_deriv ?_
  rw [sinT, Finset.sum_range_succ']
  simp only [Nat.cast_zero, pow_zero, one_mul, Nat.mul_zero, zero_mul, zero_div, add_zero]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [h0]
  have hcast : ((2 * (k + 1) : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by push_cast; ring
  have hfact : ((Nat.factorial (2 * (k + 1)) : ℕ) : ℝ)
      = (2 * ((k : ℝ) + 1)) * ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) := by
    have : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [this, Nat.factorial_succ]
    push_cast
    ring
  rw [hcast, hfact, pow_succ]
  have hne : (2 * ((k : ℝ) + 1)) ≠ 0 := by positivity
  have hne2 : ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
  field_simp

/-! ## MVT 一步的通用包装 -/

/-- 若 `g` 在 `Icc (min 0 x) (max 0 x)` 上可微且 `‖g'‖ ≤ C`，则 `‖g x − g 0‖ ≤ C·|x|`。 -/
theorem norm_sub_zero_le_of_deriv_bound {g : ℝ → ℝ} {x C : ℝ}
    (hdiff : ∀ y ∈ Set.Icc (min 0 x) (max 0 x), DifferentiableAt ℝ g y)
    (hderiv : ∀ y ∈ Set.Icc (min 0 x) (max 0 x), ‖deriv g y‖ ≤ C) :
    ‖g x - g 0‖ ≤ C * |x| := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (min 0 x) (max 0 x) := by
    constructor
    · exact min_le_left _ _
    · exact le_max_left _ _
  have hmemx : x ∈ Set.Icc (min 0 x) (max 0 x) := by
    constructor
    · exact min_le_right _ _
    · exact le_max_right _ _
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.Icc (min 0 x) (max 0 x))
    (x := (0 : ℝ)) (y := x) hdiff hderiv (convex_Icc _ _) hmem0 hmemx
  rwa [sub_zero, Real.norm_eq_abs] at h

theorem abs_le_abs_of_mem_uIcc {x y : ℝ} (hy : y ∈ Set.Icc (min 0 x) (max 0 x)) :
    |y| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [min_eq_left hx, max_eq_right hx] at hy
    rw [abs_of_nonneg hx, abs_of_nonneg hy.1]
    exact hy.2
  · rw [min_eq_right hx, max_eq_left hx] at hy
    rw [abs_of_nonpos hx, abs_of_nonpos hy.2]
    linarith [hy.1]

/-! ## 主归纳：`A(m) ∧ B(m)` 对**每个** `x` 成立 -/

/-- **主定理**：对每个 `m` 与每个实数 `x`，
`|sin x − sinT m x| ≤ |x|^(2m+1)` 且 `|cos x − cosT m x| ≤ |x|^(2m)`。 -/
theorem sin_cos_remainder (m : ℕ) :
    (∀ x : ℝ, |Real.sin x - sinT m x| ≤ |x| ^ (2 * m + 1)) ∧
      (∀ x : ℝ, |Real.cos x - cosT m x| ≤ |x| ^ (2 * m)) := by
  induction m with
  | zero =>
    refine ⟨fun x => ?_, fun x => ?_⟩
    · simpa using Real.abs_sin_le_abs (x := x)
    · simpa using Real.abs_cos_le_one (x := x)
  | succ m ih =>
    obtain ⟨hA, hB⟩ := ih
    have hB' : ∀ x : ℝ, |Real.cos x - cosT (m + 1) x| ≤ |x| ^ (2 * (m + 1)) := by
      intro x
      have h := norm_sub_zero_le_of_deriv_bound (g := fun y => Real.cos y - cosT (m + 1) y)
        (x := x) (C := |x| ^ (2 * m + 1)) ?_ ?_
      · have hg0 : Real.cos 0 - cosT (m + 1) 0 = 0 := by simp [cosT_succ_zero]
        rw [hg0, sub_zero] at h
        calc |Real.cos x - cosT (m + 1) x| = ‖Real.cos x - cosT (m + 1) x‖ := by rw [Real.norm_eq_abs]
          _ ≤ |x| ^ (2 * m + 1) * |x| := h
          _ = |x| ^ (2 * (m + 1)) := by
              rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by omega, pow_succ]
              ring
      · intro y _
        exact Real.differentiableAt_cos.sub (hasDerivAt_cosT_succ m y).differentiableAt
      · intro y hy
        have hyabs : |y| ≤ |x| := abs_le_abs_of_mem_uIcc hy
        have hder : deriv (fun y : ℝ => Real.cos y - cosT (m + 1) y) y
            = -(Real.sin y - sinT m y) := by
          have hHas := (Real.hasDerivAt_cos y).sub (hasDerivAt_cosT_succ m y)
          rw [show (fun y : ℝ => Real.cos y - cosT (m + 1) y)
              = (Real.cos - fun y => cosT (m + 1) y) from rfl, hHas.deriv]
          ring
        rw [hder, norm_neg, ← Real.norm_eq_abs]
        exact le_trans (hA y) (pow_le_pow_left₀ (abs_nonneg y) hyabs _)
    have hA' : ∀ x : ℝ, |Real.sin x - sinT (m + 1) x| ≤ |x| ^ (2 * (m + 1) + 1) := by
      intro x
      have h := norm_sub_zero_le_of_deriv_bound (g := fun y => Real.sin y - sinT (m + 1) y)
        (x := x) (C := |x| ^ (2 * (m + 1))) ?_ ?_
      · have hg0 : Real.sin 0 - sinT (m + 1) 0 = 0 := by simp [sinT_succ_zero]
        rw [hg0, sub_zero] at h
        calc |Real.sin x - sinT (m + 1) x| = ‖Real.sin x - sinT (m + 1) x‖ := by rw [Real.norm_eq_abs]
          _ ≤ |x| ^ (2 * (m + 1)) * |x| := h
          _ = |x| ^ (2 * (m + 1) + 1) := by
              rw [pow_succ]
      · intro y _
        exact Real.differentiableAt_sin.sub (hasDerivAt_sinT (m + 1) y).differentiableAt
      · intro y hy
        have hyabs : |y| ≤ |x| := abs_le_abs_of_mem_uIcc hy
        have hder : deriv (fun y : ℝ => Real.sin y - sinT (m + 1) y) y
            = Real.cos y - cosT (m + 1) y := by
          have hHas := (Real.hasDerivAt_sin y).sub (hasDerivAt_sinT (m + 1) y)
          rw [show (fun y : ℝ => Real.sin y - sinT (m + 1) y)
              = (Real.sin - fun y => sinT (m + 1) y) from rfl, hHas.deriv]
        rw [hder, ← Real.norm_eq_abs]
        exact le_trans (hB' y) (pow_le_pow_left₀ (abs_nonneg y) hyabs _)
    exact ⟨hA', hB'⟩

/-! ## ℚ 版端点与包含性（`Fm` 的直接输入） -/

/-- `ℚ` 版的 `sin` Taylor 部分和（前 `m` 个奇次项）。 -/
def sinTQ (m : ℕ) (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range m, (-1 : ℚ) ^ k * q ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℚ)

/-- `ℚ` 版部分和与 `ℝ` 版一致。 -/
theorem sinTQ_cast (m : ℕ) (q : ℚ) : ((sinTQ m q : ℚ) : ℝ) = sinT m (q : ℝ) := by
  rw [sinTQ, sinT]
  push_cast
  rfl

/-- 阶数 `29`（奇数），即 `m = 14` 个奇次项。 -/
def sinOrd : ℕ := 14

/-- **`sin` 的有理下端点**（纯幂余项；**阶乘版见 `IntervalsHighLag.lean`**）：`sinTQ 14 q − |q|^29`。 -/
def sinLoN (q : ℚ) : ℚ := sinTQ 14 q - |q| ^ 29

/-- **`sin` 的有理上端点**：`sinTQ 14 q + |q|^29`。 -/
def sinHiN (q : ℚ) : ℚ := sinTQ 14 q + |q| ^ 29

theorem sinHiN_sub_sinLoN (q : ℚ) : sinHiN q - sinLoN q = 2 * |q| ^ 29 := by
  simp only [sinHiN, sinLoN]; ring

/-- **包含性（下）**：`sinLoN q ≤ sin q`，**对每个有理数 `q` 成立**。 -/
theorem sinLoN_le_sin (q : ℚ) : ((sinLoN q : ℚ) : ℝ) ≤ Real.sin (q : ℝ) := by
  have h := (sin_cos_remainder 14).1 (q : ℝ)
  have h1 : -(|(q : ℝ)| ^ (2 * 14 + 1)) ≤ Real.sin (q : ℝ) - sinT 14 (q : ℝ) := (abs_le.mp h).1
  have h2 : ((sinLoN q : ℚ) : ℝ) = sinT 14 (q : ℝ) - |(q : ℝ)| ^ 29 := by
    simp only [sinLoN, Rat.cast_sub, Rat.cast_pow, Rat.cast_abs, sinTQ_cast]
  rw [h2]
  have h3 : (|(q : ℝ)| ^ (2 * 14 + 1) : ℝ) = |(q : ℝ)| ^ 29 := by norm_num
  linarith [h1, h3]

/-- **包含性（上）**：`sin q ≤ sinHiN q`，**对每个有理数 `q` 成立**。 -/
theorem sin_le_sinHiN (q : ℚ) : Real.sin (q : ℝ) ≤ ((sinHiN q : ℚ) : ℝ) := by
  have h := (sin_cos_remainder 14).1 (q : ℝ)
  have h1 : Real.sin (q : ℝ) - sinT 14 (q : ℝ) ≤ |(q : ℝ)| ^ (2 * 14 + 1) := (abs_le.mp h).2
  have h2 : ((sinHiN q : ℚ) : ℝ) = sinT 14 (q : ℝ) + |(q : ℝ)| ^ 29 := by
    simp only [sinHiN, Rat.cast_add, Rat.cast_pow, Rat.cast_abs, sinTQ_cast]
  rw [h2]
  have h3 : (|(q : ℝ)| ^ (2 * 14 + 1) : ℝ) = |(q : ℝ)| ^ 29 := by norm_num
  linarith [h1, h3]

/-! ## 宽度读数（内核判定）：远低于 `Fm` 的阈值 `9.956e-10` -/

/-- `sin` 高阶端点在 **`q = 0.3843`**（证书盒心的最大角值）处的宽度 **低于阈值 `9.956e-10`**。 -/
theorem sinHiN_sub_sinLoN_at_3843_lt_threshold :
    ((sinHiN (3843 / 10000) - sinLoN (3843 / 10000) : ℚ) : ℝ) < 9956 / 10 ^ 13 := by
  rw [sinHiN_sub_sinLoN]
  norm_num

/-- 同款：`q = 3720/10000`。 -/
theorem sinHiN_sub_sinLoN_at_3720_lt_threshold :
    ((sinHiN (3720 / 10000) - sinLoN (3720 / 10000) : ℚ) : ℝ) < 9956 / 10 ^ 13 := by
  rw [sinHiN_sub_sinLoN]
  norm_num

/-! ## `cos` 的高阶有理端点（`residual` 的 `rhoK`/`ringCenter` 需要） -/

/-- `ℚ` 版的 `cos` Taylor 部分和（前 `m` 个偶次项）。 -/
def cosTQ (m : ℕ) (q : ℚ) : ℚ :=
  ∑ k ∈ Finset.range m, (-1 : ℚ) ^ k * q ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℚ)

/-- `ℚ` 版部分和与 `ℝ` 版一致。 -/
theorem cosTQ_cast (m : ℕ) (q : ℚ) : ((cosTQ m q : ℚ) : ℝ) = cosT m (q : ℝ) := by
  rw [cosTQ, cosT]
  push_cast
  rfl

/-- **`cos` 的有理下端点**（纯幂余项；**阶乘版见 `IntervalsHighLag.lean`**）：`cosTQ 14 q − |q|^28`。 -/
def cosLoN (q : ℚ) : ℚ := cosTQ 14 q - |q| ^ 28

/-- **`cos` 的有理上端点**：`cosTQ 14 q + |q|^28`。 -/
def cosHiN (q : ℚ) : ℚ := cosTQ 14 q + |q| ^ 28

theorem cosHiN_sub_cosLoN (q : ℚ) : cosHiN q - cosLoN q = 2 * |q| ^ 28 := by
  simp only [cosHiN, cosLoN]; ring

/-- **包含性（下）**：`cosLoN q ≤ cos q`，**对每个有理数 `q` 成立**。 -/
theorem cosLoN_le_cos (q : ℚ) : ((cosLoN q : ℚ) : ℝ) ≤ Real.cos (q : ℝ) := by
  have h := (sin_cos_remainder 14).2 (q : ℝ)
  have h1 : -(|(q : ℝ)| ^ (2 * 14)) ≤ Real.cos (q : ℝ) - cosT 14 (q : ℝ) := (abs_le.mp h).1
  have h2 : ((cosLoN q : ℚ) : ℝ) = cosT 14 (q : ℝ) - |(q : ℝ)| ^ 28 := by
    simp only [cosLoN, Rat.cast_sub, Rat.cast_pow, Rat.cast_abs, cosTQ_cast]
  rw [h2]
  have h3 : (|(q : ℝ)| ^ (2 * 14) : ℝ) = |(q : ℝ)| ^ 28 := by norm_num
  linarith [h1, h3]

/-- **包含性（上）**：`cos q ≤ cosHiN q`，**对每个有理数 `q` 成立**。 -/
theorem cos_le_cosHiN (q : ℚ) : Real.cos (q : ℝ) ≤ ((cosHiN q : ℚ) : ℝ) := by
  have h := (sin_cos_remainder 14).2 (q : ℝ)
  have h1 : Real.cos (q : ℝ) - cosT 14 (q : ℝ) ≤ |(q : ℝ)| ^ (2 * 14) := (abs_le.mp h).2
  have h2 : ((cosHiN q : ℚ) : ℝ) = cosT 14 (q : ℝ) + |(q : ℝ)| ^ 28 := by
    simp only [cosHiN, Rat.cast_add, Rat.cast_pow, Rat.cast_abs, cosTQ_cast]
  rw [h2]
  have h3 : (|(q : ℝ)| ^ (2 * 14) : ℝ) = |(q : ℝ)| ^ 28 := by norm_num
  linarith [h1, h3]

/-- `cos` 端点在 `q = 0.3843` 处的宽度**低于 `Fm` 阈值**。 -/
theorem cosHiN_sub_cosLoN_at_3843_lt_threshold :
    ((cosHiN (3843 / 10000) - cosLoN (3843 / 10000) : ℚ) : ℝ) < 9956 / 10 ^ 13 := by
  rw [cosHiN_sub_cosLoN]
  norm_num

/-! ## 窗口算子的高阶版（单调性拼装；**保留 `[-1,1]` 保守回退**） -/

/-- 高阶 `sin` 区间算子。窗口 `[-1,1]` 内 `sin` 单调递增，故取 `⟨sinLoN lo, sinHiN hi⟩`；否则回退 `[-1,1]`。 -/
def sinIHigh (A : RatInterval) : RatInterval :=
  if -1 ≤ A.lo ∧ A.hi ≤ 1 then ⟨sinLoN A.lo, sinHiN A.hi⟩ else RatInterval.intv (-1) 1

/-- 高阶 `cos` 区间算子。窗口 `[0,2]` 内 `cos` 单调递减，故取 `⟨cosLoN A.hi, cosHiN A.lo⟩`；否则回退 `[-1,1]`。 -/
def cosIHigh (A : RatInterval) : RatInterval :=
  if 0 ≤ A.lo ∧ A.hi ≤ 2 then ⟨cosLoN A.hi, cosHiN A.lo⟩ else RatInterval.intv (-1) 1

open MeasureTheory intervalIntegral

/-! ## 积分管道（Lagrange 余项的装配基础）

**动机（R16 纠正 C1029）**：`sin_cos_remainder` 的界是纯幂 `|x|^(2m+1)`，**缺阶乘**，
而 `Fm` 的相位归约后三角参数达 `|q| ≈ 0.77`，在那里 `0.77^28 ≈ 1.5e-3` 吃光余量
（`fm-eval` 的 `whatif.py` 实测：`fact29` ⇒ `1.50e-3` ✗；`lagrange` ⇒ `1.06e-19` ✓）。
**MVT 路线给不出阶乘**：`|g x − g 0| ≤ sup|g'|·|x|` 每步丢一个 `2m`，级联后恰好丢掉整条 `(2m+1)!`。
本节的**积分恒等式**是换到 Lagrange 形的管道。

**真实等级**：kernel-proved，零 sorry、零自定义 axiom。 -/

theorem continuous_sinT (m : ℕ) : Continuous (sinT m) := by
  rw [show sinT m = fun x : ℝ => ∑ k ∈ Finset.range m,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) from rfl]
  exact continuous_finsetSum _ fun k _ => (continuous_const.mul (continuous_pow _)).div_const _

theorem continuous_cosT (m : ℕ) : Continuous (cosT m) := by
  rw [show cosT m = fun x : ℝ => ∑ k ∈ Finset.range m,
      (-1 : ℝ) ^ k * x ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ) from rfl]
  exact continuous_finsetSum _ fun k _ => (continuous_const.mul (continuous_pow _)).div_const _

/-- **`sin` 侧余项的积分恒等式**：`sin x − sinT (m+1) x = ∫_0^x (cos t − cosT (m+1) t) dt`。 -/
theorem sin_sub_sinT_eq_integral (m : ℕ) (x : ℝ) :
    Real.sin x - sinT (m + 1) x = ∫ t in (0 : ℝ)..x, (Real.cos t - cosT (m + 1) t) := by
  have hder : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.sin t - sinT (m + 1) t)
        (Real.cos t - cosT (m + 1) t) t := by
    intro t _
    have h := (Real.hasDerivAt_sin t).sub (hasDerivAt_sinT (m + 1) t)
    rwa [show (Real.sin - fun y : ℝ => sinT (m + 1) y)
      = (fun t : ℝ => Real.sin t - sinT (m + 1) t) from rfl] at h
  have hint : IntervalIntegrable (fun t : ℝ => Real.cos t - cosT (m + 1) t) volume (0 : ℝ) x :=
    (Real.continuous_cos.sub (continuous_cosT (m + 1))).intervalIntegrable _ _
  have h := integral_eq_sub_of_hasDerivAt hder hint
  have h0 : Real.sin 0 - sinT (m + 1) 0 = 0 := by
    simp [sinT_succ_zero]
  rw [h, h0, sub_zero]

/-- **`cos` 侧余项的积分恒等式**：`cos x − cosT (m+1) x = ∫_0^x −(sin t − sinT m t) dt`。 -/
theorem cos_sub_cosT_eq_integral (m : ℕ) (x : ℝ) :
    Real.cos x - cosT (m + 1) x = ∫ t in (0 : ℝ)..x, (-(Real.sin t - sinT m t)) := by
  have hder : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.cos t - cosT (m + 1) t) (-(Real.sin t - sinT m t)) t := by
    intro t _
    have h' : HasDerivAt (fun y : ℝ => Real.cos y - cosT (m + 1) y)
        (-Real.sin t - (-(sinT m t))) t := by
      have h := (Real.hasDerivAt_cos t).sub (hasDerivAt_cosT_succ m t)
      rwa [show (Real.cos - fun y : ℝ => cosT (m + 1) y)
        = (fun t : ℝ => Real.cos t - cosT (m + 1) t) from rfl] at h
    have heq : (-Real.sin t - (-(sinT m t))) = -(Real.sin t - sinT m t) := by ring
    rwa [heq] at h'
  have hint : IntervalIntegrable (fun t : ℝ => (-(Real.sin t - sinT m t))) volume (0 : ℝ) x :=
    ((Real.continuous_sin.sub (continuous_sinT m)).neg).intervalIntegrable _ _
  have h := integral_eq_sub_of_hasDerivAt hder hint
  have h0 : Real.cos 0 - cosT (m + 1) 0 = 0 := by
    simp [cosT_succ_zero]
  rw [h, h0, sub_zero]

/-! ## Lagrange 余项装配（把 C1029 的缺口补上） -/

/-- `∫_0^x t^N / D = x^(N+1) / ((N:ℝ)+1) / D`（`x ≥ 0`）。 -/
theorem integral_pow_div (N : ℕ) {D x : ℝ} (_hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..x, t ^ N / D = x ^ (N + 1) / (((N : ℕ) : ℝ) + 1) / D := by
  have h : (fun t : ℝ => t ^ N / D) = fun t : ℝ => D⁻¹ * t ^ N := by
    funext t; rw [div_eq_inv_mul]
  rw [h, intervalIntegral.integral_const_mul, integral_pow]
  have h0 : (0 : ℝ) ^ (N + 1) = 0 := zero_pow (Nat.succ_ne_zero N)
  rw [h0, sub_zero, div_eq_inv_mul]
  ring

/-- **Lagrange 余项**（`x ≥ 0`）：`|sin x − sinT m x| ≤ x^(2m+1)/(2m+1)!` 且
`|cos x − cosT m x| ≤ x^(2m)/(2m)!`。

这是 C1029 修法的落地：界从**纯幂** `|x|^(2m+1)` 换成**带阶乘**的 Lagrange 形，
从而 `Fm` 在 `|q| ≈ 0.77` 处可用（`fm-eval` 的 `whatif.py` `lagrange` 行 ⇒ `1.06e-19`）。 -/
theorem sin_cos_remainder_lagrange (m : ℕ) :
    (∀ x : ℝ, 0 ≤ x → |Real.sin x - sinT m x| ≤
      x ^ (2 * m + 1) / ((Nat.factorial (2 * m + 1) : ℕ) : ℝ)) ∧
    (∀ x : ℝ, 0 ≤ x → |Real.cos x - cosT m x| ≤
      x ^ (2 * m) / ((Nat.factorial (2 * m) : ℕ) : ℝ)) := by
  induction m with
  | zero =>
    constructor
    · intro x hx
      have h := Real.abs_sin_le_abs (x := x)
      rw [abs_of_nonneg hx] at h
      simpa using h
    · intro x hx
      simpa using Real.abs_cos_le_one (x := x)
  | succ m ih =>
    obtain ⟨hA, hB⟩ := ih
    have hB' : ∀ x : ℝ, 0 ≤ x → |Real.cos x - cosT (m + 1) x| ≤
        x ^ (2 * (m + 1)) / ((Nat.factorial (2 * (m + 1)) : ℕ) : ℝ) := by
      intro x hx
      set D : ℝ := ((Nat.factorial (2 * m + 1) : ℕ) : ℝ) with hD
      have hDne : D ≠ 0 := by
        rw [hD]; exact_mod_cast Nat.factorial_ne_zero (2 * m + 1)
      rw [cos_sub_cosT_eq_integral m x]
      have h1 : |∫ t in (0 : ℝ)..x, (-(Real.sin t - sinT m t))| ≤
          ∫ t in (0 : ℝ)..x, |-(Real.sin t - sinT m t)| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (f := fun t : ℝ => (-(Real.sin t - sinT m t)))
            (a := (0 : ℝ)) (b := x) hx
      have h2 : (∫ t in (0 : ℝ)..x, |-(Real.sin t - sinT m t)|) ≤
          ∫ t in (0 : ℝ)..x, t ^ (2 * m + 1) / D := by
        refine integral_mono_on hx ?_ ?_ ?_
        · exact ((Real.continuous_sin.sub (continuous_sinT m)).neg.abs).intervalIntegrable _ _
        · exact ((continuous_pow _).div_const _).intervalIntegrable _ _
        · intro t ht
          rw [abs_neg]
          exact hA t ht.1
      refine le_trans h1 (le_trans h2 ?_)
      rw [integral_pow_div (2 * m + 1) hx]
      have hfac : ((Nat.factorial (2 * (m + 1)) : ℕ) : ℝ)
          = (((2 * m + 1 : ℕ) : ℝ) + 1) * D := by
        have h2m : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        rw [h2m, Nat.factorial_succ, hD]; push_cast; ring
      have hexp : (2 * (m + 1) : ℕ) = 2 * m + 1 + 1 := by omega
      rw [hfac, hexp]
      have hne : (((2 * m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      rw [div_div]
    have hA' : ∀ x : ℝ, 0 ≤ x → |Real.sin x - sinT (m + 1) x| ≤
        x ^ (2 * (m + 1) + 1) / ((Nat.factorial (2 * (m + 1) + 1) : ℕ) : ℝ) := by
      intro x hx
      set D : ℝ := ((Nat.factorial (2 * (m + 1)) : ℕ) : ℝ) with hD
      have hDne : D ≠ 0 := by
        rw [hD]; exact_mod_cast Nat.factorial_ne_zero (2 * (m + 1))
      rw [sin_sub_sinT_eq_integral m x]
      have h1 : |∫ t in (0 : ℝ)..x, (Real.cos t - cosT (m + 1) t)| ≤
          ∫ t in (0 : ℝ)..x, |Real.cos t - cosT (m + 1) t| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (f := fun t : ℝ => (Real.cos t - cosT (m + 1) t))
            (a := (0 : ℝ)) (b := x) hx
      have h2 : (∫ t in (0 : ℝ)..x, |Real.cos t - cosT (m + 1) t|) ≤
          ∫ t in (0 : ℝ)..x, t ^ (2 * (m + 1)) / D := by
        refine integral_mono_on hx ?_ ?_ ?_
        · exact ((Real.continuous_cos.sub (continuous_cosT (m + 1))).abs).intervalIntegrable _ _
        · exact ((continuous_pow _).div_const _).intervalIntegrable _ _
        · intro t ht
          exact hB' t ht.1
      refine le_trans h1 (le_trans h2 ?_)
      rw [integral_pow_div (2 * (m + 1)) hx]
      have hfac : ((Nat.factorial (2 * (m + 1) + 1) : ℕ) : ℝ)
          = (((2 * (m + 1) : ℕ) : ℝ) + 1) * D := by
        rw [Nat.factorial_succ, hD]; push_cast; ring
      rw [hfac]
      have hne : (((2 * (m + 1) : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      rw [div_div]
    exact ⟨hA', hB'⟩

end N11Formalization
