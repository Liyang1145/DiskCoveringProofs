import N11Formalization.IntervalsHigh

/-!
# **阶乘版（Lagrange）三角端点**

**动机**：`IntervalsHigh.lean` 里的 `sinLoN/sinHiN/cosLoN/cosHiN` 余项是**纯幂** `|q|^29`/`|q|^28`，
而 `Fm` 的相位归约后三角参数达 `|q| ≈ 0.77`，在那里 `0.77^28 ≈ 1.5e-3` 吃光余量
（`fm-eval` 的 `whatif.py`：`fact29` ⇒ `1.50e-3` ✗ vs 阈值 `9.956e-10`）。
**缺的是阶乘而不是阶数**。

本文件给出余项**带阶乘**的版本（`sinLoNLag/sinHiNLag/cosLoNLag/cosHiNLag`），
由 `IntervalsHigh.sin_cos_remainder_lagrange`（R18，积分路线）供界：
`|sin x − sinT m x| ≤ |x|^(2m+1)/(2m+1)!`、`|cos x − cosT m x| ≤ |x|^(2m)/(2m)!`。

**`Fm` 相关的量级**：窗口取 `|q| ≤ 1` 时宽度上界 = `2/29! ≈ 5.0e-31`（对比 `fact29` 的 `2`）。

**真实等级**：kernel-proved，**无符号限制**（用奇偶性把 `x < 0` 归约到 `x > 0`），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

/-- `sinT` 是奇函数。 -/
theorem sinT_neg (m : ℕ) (x : ℝ) : sinT m (-x) = -sinT m x := by
  simp only [sinT]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(show Odd (2 * k + 1) from ⟨k, by ring⟩).neg_pow]
  ring

/-- `cosT` 是偶函数。 -/
theorem cosT_neg (m : ℕ) (x : ℝ) : cosT m (-x) = cosT m x := by
  simp only [cosT]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(show Even (2 * k) from ⟨k, by ring⟩).neg_pow]

/-- **`sin` 余项的绝对值形界（无符号限制）**：`|sin x − sinT m x| ≤ |x|^(2m+1)/(2m+1)!`。 -/
theorem sin_bound_abs (m : ℕ) (x : ℝ) :
    |Real.sin x - sinT m x| ≤ |x| ^ (2 * m + 1) / ((Nat.factorial (2 * m + 1) : ℕ) : ℝ) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact (sin_cos_remainder_lagrange m).1 x hx
  · have hx' : (0 : ℝ) ≤ -x := by linarith
    have h := (sin_cos_remainder_lagrange m).1 (-x) hx'
    have h1 : Real.sin (-x) - sinT m (-x) = -(Real.sin x - sinT m x) := by
      rw [Real.sin_neg, sinT_neg]; ring
    rw [h1, abs_neg] at h
    rw [abs_of_nonpos hx]
    exact h

/-- **`cos` 余项的绝对值形界（无符号限制）**：`|cos x − cosT m x| ≤ |x|^(2m)/(2m)!`。 -/
theorem cos_bound_abs (m : ℕ) (x : ℝ) :
    |Real.cos x - cosT m x| ≤ |x| ^ (2 * m) / ((Nat.factorial (2 * m) : ℕ) : ℝ) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact (sin_cos_remainder_lagrange m).2 x hx
  · have hx' : (0 : ℝ) ≤ -x := by linarith
    have h := (sin_cos_remainder_lagrange m).2 (-x) hx'
    have h1 : Real.cos (-x) - cosT m (-x) = Real.cos x - cosT m x := by
      rw [Real.cos_neg, cosT_neg]
    rw [h1] at h
    rw [abs_of_nonpos hx]
    exact h

/-- **`sin` 的阶乘版有理下端点**：`sinTQ 14 q − |q|^29/29!`。 -/
def sinLoNLag (q : ℚ) : ℚ := sinTQ 14 q - |q| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ)

/-- **`sin` 的阶乘版有理上端点**：`sinTQ 14 q + |q|^29/29!`。 -/
def sinHiNLag (q : ℚ) : ℚ := sinTQ 14 q + |q| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ)

/-- **`cos` 的阶乘版有理下端点**：`cosTQ 14 q − |q|^28/28!`。 -/
def cosLoNLag (q : ℚ) : ℚ := cosTQ 14 q - |q| ^ 28 / ((Nat.factorial 28 : ℕ) : ℚ)

/-- **`cos` 的阶乘版有理上端点**：`cosTQ 14 q + |q|^28/28!`。 -/
def cosHiNLag (q : ℚ) : ℚ := cosTQ 14 q + |q| ^ 28 / ((Nat.factorial 28 : ℕ) : ℚ)

theorem sinHiNLag_sub_sinLoNLag (q : ℚ) :
    sinHiNLag q - sinLoNLag q = 2 * (|q| ^ 29 / ((Nat.factorial 29 : ℕ) : ℚ)) := by
  simp only [sinHiNLag, sinLoNLag]; ring

theorem cosHiNLag_sub_cosLoNLag (q : ℚ) :
    cosHiNLag q - cosLoNLag q = 2 * (|q| ^ 28 / ((Nat.factorial 28 : ℕ) : ℚ)) := by
  simp only [cosHiNLag, cosLoNLag]; ring

/-- **包含性（下）**：`sinLoNLag q ≤ sin q`，**对每个有理数 `q` 成立**。 -/
theorem sinLoNLag_le_sin (q : ℚ) : ((sinLoNLag q : ℚ) : ℝ) ≤ Real.sin (q : ℝ) := by
  have h := sin_bound_abs 14 (q : ℝ)
  have h3 : (|(q : ℝ)| ^ (2 * 14 + 1) : ℝ) = |(q : ℝ)| ^ 29 := by norm_num
  rw [h3] at h
  have h1 : -(|(q : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ)) ≤
      Real.sin (q : ℝ) - sinT 14 (q : ℝ) := (abs_le.mp h).1
  have h2 : ((sinLoNLag q : ℚ) : ℝ) = sinT 14 (q : ℝ) - |(q : ℝ)| ^ 29 /
      ((Nat.factorial 29 : ℕ) : ℝ) := by
    simp only [sinLoNLag]
    push_cast
    rw [sinTQ_cast]
  rw [h2]
  linarith [h1]

/-- **包含性（上）**：`sin q ≤ sinHiNLag q`。 -/
theorem sin_le_sinHiNLag (q : ℚ) : Real.sin (q : ℝ) ≤ ((sinHiNLag q : ℚ) : ℝ) := by
  have h := sin_bound_abs 14 (q : ℝ)
  have h3 : (|(q : ℝ)| ^ (2 * 14 + 1) : ℝ) = |(q : ℝ)| ^ 29 := by norm_num
  rw [h3] at h
  have h1 : Real.sin (q : ℝ) - sinT 14 (q : ℝ) ≤
      |(q : ℝ)| ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) := (abs_le.mp h).2
  have h2 : ((sinHiNLag q : ℚ) : ℝ) = sinT 14 (q : ℝ) + |(q : ℝ)| ^ 29 /
      ((Nat.factorial 29 : ℕ) : ℝ) := by
    simp only [sinHiNLag]
    push_cast
    rw [sinTQ_cast]
  rw [h2]
  linarith [h1]

/-- **包含性（下）**：`cosLoNLag q ≤ cos q`，**对每个有理数 `q` 成立**。 -/
theorem cosLoNLag_le_cos (q : ℚ) : ((cosLoNLag q : ℚ) : ℝ) ≤ Real.cos (q : ℝ) := by
  have h := cos_bound_abs 14 (q : ℝ)
  have h3 : (|(q : ℝ)| ^ (2 * 14) : ℝ) = |(q : ℝ)| ^ 28 := by norm_num
  rw [h3] at h
  have h1 : -(|(q : ℝ)| ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ)) ≤
      Real.cos (q : ℝ) - cosT 14 (q : ℝ) := (abs_le.mp h).1
  have h2 : ((cosLoNLag q : ℚ) : ℝ) = cosT 14 (q : ℝ) - |(q : ℝ)| ^ 28 /
      ((Nat.factorial 28 : ℕ) : ℝ) := by
    simp only [cosLoNLag]
    push_cast
    rw [cosTQ_cast]
  rw [h2]
  linarith [h1]

/-- **包含性（上）**：`cos q ≤ cosHiNLag q`。 -/
theorem cos_le_cosHiNLag (q : ℚ) : Real.cos (q : ℝ) ≤ ((cosHiNLag q : ℚ) : ℝ) := by
  have h := cos_bound_abs 14 (q : ℝ)
  have h3 : (|(q : ℝ)| ^ (2 * 14) : ℝ) = |(q : ℝ)| ^ 28 := by norm_num
  rw [h3] at h
  have h1 : Real.cos (q : ℝ) - cosT 14 (q : ℝ) ≤
      |(q : ℝ)| ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := (abs_le.mp h).2
  have h2 : ((cosHiNLag q : ℚ) : ℝ) = cosT 14 (q : ℝ) + |(q : ℝ)| ^ 28 /
      ((Nat.factorial 28 : ℕ) : ℝ) := by
    simp only [cosHiNLag]
    push_cast
    rw [cosTQ_cast]
  rw [h2]
  linarith [h1]

/-! ## 窗口算子（阶乘版）与**关键读数** -/

/-- 阶乘版 `sin` 区间算子（窗口 `[-1,1]` 内 `sin` 单调递增）。 -/
def sinIHighLag (A : RatInterval) : RatInterval :=
  if -1 ≤ A.lo ∧ A.hi ≤ 1 then ⟨sinLoNLag A.lo, sinHiNLag A.hi⟩ else RatInterval.intv (-1) 1

/-- 阶乘版 `cos` 区间算子（窗口 `[0,2]` 内 `cos` 单调递减）。 -/
def cosIHighLag (A : RatInterval) : RatInterval :=
  if 0 ≤ A.lo ∧ A.hi ≤ 2 then ⟨cosLoNLag A.hi, cosHiNLag A.lo⟩ else RatInterval.intv (-1) 1

/-- **`sin` 窗口算子的可靠性**（`sin` 在 `[-1,1]` 上单调递增，`[-1,1] ⊆ [-(π/2), π/2]`）。 -/
theorem sinIHighLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    (sinIHighLag A).Mem (Real.sin x) := by
  by_cases h : -1 ≤ A.lo ∧ A.hi ≤ 1
  · rw [sinIHighLag, if_pos h]
    have hlo : (A.lo : ℝ) ≤ x := hA.1
    have hhi : x ≤ (A.hi : ℝ) := hA.2
    have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    have h1R : (-1 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
    have h2R : (A.hi : ℝ) ≤ 1 := by exact_mod_cast h.2
    have hml : (A.lo : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [h1R, hpi], by linarith [h2R, hpi]⟩
    have hmx : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hml.1, hlo], by linarith [h2R, hpi, hhi]⟩
    have hmh : (A.hi : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [h1R, hpi, hlo], by linarith [h2R, hpi]⟩
    exact ⟨le_trans (sinLoNLag_le_sin A.lo)
        (Real.monotoneOn_sin hml hmx hlo),
      le_trans (Real.monotoneOn_sin hmx hmh hhi) (sin_le_sinHiNLag A.hi)⟩
  · rw [sinIHighLag, if_neg h]
    have hlo' : ((RatInterval.intv (-1) 1).lo : ℝ) = (-1 : ℝ) := by
      simp only [RatInterval.intv]; norm_num
    have hhi' : ((RatInterval.intv (-1) 1).hi : ℝ) = (1 : ℝ) := by
      simp only [RatInterval.intv]; norm_num
    exact ⟨by rw [hlo']; exact Real.neg_one_le_sin x, by rw [hhi']; exact Real.sin_le_one x⟩

/-- **`cos` 窗口算子的可靠性**（`cos` 在 `[0,2]` 上单调递减，`[0,2] ⊆ [0,π]`）。 -/
theorem cosIHighLag_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    (cosIHighLag A).Mem (Real.cos x) := by
  by_cases h : 0 ≤ A.lo ∧ A.hi ≤ 2
  · rw [cosIHighLag, if_pos h]
    have hlo : (A.lo : ℝ) ≤ x := hA.1
    have hhi : x ≤ (A.hi : ℝ) := hA.2
    have hpi : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h1R : (0 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
    have h2R : (A.hi : ℝ) ≤ 2 := by exact_mod_cast h.2
    have hml : (A.lo : ℝ) ∈ Set.Icc 0 Real.pi := ⟨h1R, by linarith [h2R, hpi]⟩
    have hmx : x ∈ Set.Icc 0 Real.pi := ⟨by linarith [h1R, hlo], by linarith [h2R, hpi, hhi]⟩
    have hmh : (A.hi : ℝ) ∈ Set.Icc 0 Real.pi := ⟨by linarith [h1R, hlo], by linarith [h2R, hpi]⟩
    refine ⟨?_, ?_⟩
    · -- cosLoNLag A.hi ≤ cos x：cos 递减 ⇒ cos A.hi ≤ cos x
      exact le_trans (cosLoNLag_le_cos A.hi)
        (Real.strictAntiOn_cos.antitoneOn hmx hmh hhi)
    · -- cos x ≤ cosHiNLag A.lo：cos 递减 ⇒ cos x ≤ cos A.lo
      exact le_trans (Real.strictAntiOn_cos.antitoneOn hml hmx hlo) (cos_le_cosHiNLag A.lo)
  · rw [cosIHighLag, if_neg h]
    have hlo' : ((RatInterval.intv (-1) 1).lo : ℝ) = (-1 : ℝ) := by
      simp only [RatInterval.intv]; norm_num
    have hhi' : ((RatInterval.intv (-1) 1).hi : ℝ) = (1 : ℝ) := by
      simp only [RatInterval.intv]; norm_num
    exact ⟨by rw [hlo']; exact Real.neg_one_le_cos x, by rw [hhi']; exact Real.cos_le_one x⟩

/-- **关键读数**：窗口 `[-1,1]` 上宽度上界 `2/29!`，**远低于 `Fm` 阈值 `9.956e-10`**。 -/
theorem sinHiNLag_sub_sinLoNLag_at_one :
    ((sinHiNLag 1 - sinLoNLag 1 : ℚ) : ℝ) < 9956 / 10 ^ 13 := by
  rw [sinHiNLag_sub_sinLoNLag]
  norm_num

/-- 同款：`q = 3843/10000`（证书盒心最大角值）。 -/
theorem sinHiNLag_sub_sinLoNLag_at_3843 :
    ((sinHiNLag (3843 / 10000) - sinLoNLag (3843 / 10000) : ℚ) : ℝ) < 9956 / 10 ^ 13 := by
  rw [sinHiNLag_sub_sinLoNLag]
  norm_num

/-- 同款（cos）：`q = 1`。 -/
theorem cosHiNLag_sub_cosLoNLag_at_one :
    ((cosHiNLag 1 - cosLoNLag 1 : ℚ) : ℝ) < 9956 / 10 ^ 13 := by
  rw [cosHiNLag_sub_cosLoNLag]
  norm_num

end N11Formalization
