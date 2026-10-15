/-
  N11Formalization.Interval.Sqrt
  ==============================

  `Real.sqrt` 的有理端点（精确、外向）与包含性。

  构造：对 `q : ℚ`，写 `q = p/d`（`p = |q.num|`，`d = q.den > 0`）；由 `q = (p·d)/d²` 得
  `√q = √(p·d)/d`，于是取
    * `sqrtLo q = ⌊√(p·d)⌋ / d ≤ √q`（整数依据：`Nat.sqrt_le`）
    * `sqrtHi q = (⌊√(p·d)⌋+1) / d ≥ √q`（整数依据：`Nat.sqrt_lt`）
  外向方向由 `Real.le_sqrt` / `Real.sqrt_le_left` 给出，全程只用整数/有理算术，
  不经过任何宿主浮点（无 `Float`）。

  `q ≤ 0` 时两支都退化为 `0`；此时 `√q = 0`（`Real.sqrt_eq_zero_of_nonpos`）。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval` 当证明。
-/
import Mathlib
import N11Formalization.Interval.Core

/-! ### 审计口径（本工程纪律，lead 裁定 · 记入件头）

**编译失败的件里可能残留 `sorryAx` 占位 ⇒ 对"红的件"跑公理审计没有意义；公理画像只有在 `ERROR=0` 时才可读。**

另：本文件的严格件（如 `sqrtLo_pos`）**不得**用非严格引理去凑严格结论；
严格件必须展开定义或走真正给出严格性的引理。

共享 `lean/` 目录下**禁止并发 `lake`**：见 `failed to read file …olean[.private]` ⇒ 环境噪声，串行重跑即可，不去"修"不存在的代码错。
-/

namespace N11Formalization

namespace RatInterval

/-! ## 1. 正有理数的 num/den 分解 -/

/-- 对 `q > 0`：`|q.num| = q.num`（作为 ℚ）。 -/
theorem natAbs_num_cast {q : ℚ} (hq : 0 < q) : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
  have h : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hq))
  calc ((q.num.natAbs : ℕ) : ℚ) = ((q.num.natAbs : ℤ) : ℚ) := (Int.cast_natCast _).symm
    _ = (q.num : ℚ) := by rw [h]

/-- 对 `q > 0`：`q = p/d`，其中 `p = |q.num|`、`d = q.den`。 -/
theorem num_den_decomp {q : ℚ} (hq : 0 < q) :
    ((q.num.natAbs : ℕ) : ℚ) / ((q.den : ℕ) : ℚ) = q := by
  rw [natAbs_num_cast hq, Rat.num_div_den]

/-! ## 2. 端点公式在 `p/d` 形式下的规格（整数不等式内核） -/

/-- 上界规格：`√(p/d) ≤ (⌊√(p·d)⌋+1)/d`。 -/
theorem sqrtHi_pos_spec {p d : ℕ} (hd : 0 < d) :
    Real.sqrt ((((p : ℚ) / (d : ℚ)) : ℚ) : ℝ) ≤
      ((((Nat.sqrt (p * d) : ℚ) + 1) / ((d : ℚ)) : ℚ) : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsnn : (0 : ℝ) ≤ ((((Nat.sqrt (p * d) : ℚ) + 1) / ((d : ℚ)) : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ ((Nat.sqrt (p * d) : ℚ) + 1) / ((d : ℚ)) := by
      apply div_nonneg <;> positivity
    exact_mod_cast this
  rw [Real.sqrt_le_left hsnn]
  push_cast
  have hnat : p * d ≤ (Nat.sqrt (p * d) + 1) * (Nat.sqrt (p * d) + 1) :=
    le_of_lt ((Nat.sqrt_lt).mp (Nat.lt_succ_self _))
  have hpd : (p : ℝ) * (d : ℝ) ≤
      ((Nat.sqrt (p * d) : ℝ) + 1) * ((Nat.sqrt (p * d) : ℝ) + 1) := by
    exact_mod_cast hnat
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  field_simp
  nlinarith [hpd]

/-- 下界规格：`⌊√(p·d)⌋/d ≤ √(p/d)`。 -/
theorem sqrtLo_pos_spec {p d : ℕ} (hd : 0 < d) :
    ((((Nat.sqrt (p * d) : ℚ)) / ((d : ℚ)) : ℚ) : ℝ) ≤
      Real.sqrt ((((p : ℚ) / (d : ℚ)) : ℚ) : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have htnn : (0 : ℝ) ≤ (((Nat.sqrt (p * d) : ℚ)) / ((d : ℚ)) : ℚ) := by
    have : (0 : ℚ) ≤ (Nat.sqrt (p * d) : ℚ) / ((d : ℚ)) := by
      apply div_nonneg <;> positivity
    exact_mod_cast this
  have hqnn : (0 : ℝ) ≤ ((((p : ℚ) / (d : ℚ)) : ℚ) : ℝ) := by
    push_cast
    exact div_nonneg (by positivity) (le_of_lt hdpos)
  rw [Real.le_sqrt htnn hqnn]
  push_cast
  have hnat : Nat.sqrt (p * d) * Nat.sqrt (p * d) ≤ p * d := Nat.sqrt_le _
  have hpd : (Nat.sqrt (p * d) : ℝ) * (Nat.sqrt (p * d) : ℝ) ≤ (p : ℝ) * (d : ℝ) := by
    exact_mod_cast hnat
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  field_simp
  nlinarith [hpd]

/-! ## 3. sqrtLo / sqrtHi 定义与规格 -/

/-- 有理**上界** `sqrtHi q ≥ √q`（且 `0 ≤ sqrtHi q`）。 -/
def sqrtHi (q : ℚ) : ℚ :=
  if q ≤ 0 then 0 else ((Nat.sqrt (q.num.natAbs * q.den) : ℚ) + 1) / ((q.den : ℕ) : ℚ)

/-- 有理**下界** `sqrtLo q ≤ √q`（且 `0 ≤ sqrtLo q`）。 -/
def sqrtLo (q : ℚ) : ℚ :=
  if q ≤ 0 then 0 else (Nat.sqrt (q.num.natAbs * q.den) : ℚ) / ((q.den : ℕ) : ℚ)

theorem sqrtHi_nonneg (q : ℚ) : 0 ≤ sqrtHi q := by
  rw [sqrtHi]
  by_cases h : q ≤ 0
  · rw [if_pos h]
  · rw [if_neg h]
    apply div_nonneg <;> positivity

theorem sqrtLo_nonneg (q : ℚ) : 0 ≤ sqrtLo q := by
  rw [sqrtLo]
  by_cases h : q ≤ 0
  · rw [if_pos h]
  · rw [if_neg h]
    apply div_nonneg <;> positivity

/-- 规格（上界）：`√q ≤ sqrtHi q`。 -/
theorem sqrt_le_sqrtHi (q : ℚ) : Real.sqrt (q : ℝ) ≤ ((sqrtHi q : ℚ) : ℝ) := by
  rw [sqrtHi]
  by_cases h : q ≤ 0
  · rw [if_pos h, Rat.cast_zero]
    exact le_of_eq (Real.sqrt_eq_zero_of_nonpos (by exact_mod_cast h))
  · rw [if_neg h]
    have hq : 0 < q := not_le.mp h
    have key := sqrtHi_pos_spec (p := q.num.natAbs) (d := q.den) q.den_pos
    rwa [num_den_decomp hq] at key

/-- 规格（下界）：`sqrtLo q ≤ √q`。 -/
theorem sqrtLo_le_sqrt (q : ℚ) : ((sqrtLo q : ℚ) : ℝ) ≤ Real.sqrt (q : ℝ) := by
  rw [sqrtLo]
  by_cases h : q ≤ 0
  · rw [if_pos h, Rat.cast_zero]
    exact Real.sqrt_nonneg _
  · rw [if_neg h]
    have hq : 0 < q := not_le.mp h
    have key := sqrtLo_pos_spec (p := q.num.natAbs) (d := q.den) q.den_pos
    rwa [num_den_decomp hq] at key

/-- 端点比较：`sqrtLo ≤ sqrtHi`（`Valid` 保持性用）。 -/
theorem sqrtLo_le_sqrtHi (q : ℚ) : sqrtLo q ≤ sqrtHi q := by
  rw [sqrtLo, sqrtHi]
  by_cases h : q ≤ 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have hd : (0 : ℚ) ≤ ((q.den : ℕ) : ℚ) := by positivity
    exact div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (by norm_num : (0 : ℚ) ≤ 1)) hd

/-! ### 端点的有理规格（平方形式）

`sqrtLo/sqrtHi` 的「有理版本」规格：`sqrtLo q` 平方不超过 `q`，`sqrtHi q` 平方不小于 `q`。
两者都比实数规格更直接，便于下游只需平方不等式的场景（也是 `Real.le_sqrt` 用到的内核事实）。 -/

/-- 有理规格（`p/d` 形式）：`(⌊√(p·d)⌋+1)/d` 的平方 ≥ `p/d`。 -/
theorem sqrtHi_sq_spec {p d : ℕ} (hd : 0 < d) :
    ((p : ℚ) / (d : ℚ)) ≤
      (((Nat.sqrt (p * d) : ℚ) + 1) / ((d : ℚ))) * (((Nat.sqrt (p * d) : ℚ) + 1) / ((d : ℚ))) := by
  have hd' : (0 : ℚ) < ((d : ℚ)) := by exact_mod_cast hd
  have hnat : p * d ≤ (Nat.sqrt (p * d) + 1) * (Nat.sqrt (p * d) + 1) :=
    le_of_lt ((Nat.sqrt_lt).mp (Nat.lt_succ_self _))
  have hnat' : ((p : ℚ) * ((d : ℚ))) ≤
      ((Nat.sqrt (p * d) : ℚ) + 1) * ((Nat.sqrt (p * d) : ℚ) + 1) := by
    exact_mod_cast hnat
  have hdne : ((d : ℚ)) ≠ 0 := ne_of_gt hd'
  field_simp
  nlinarith [hnat']

/-- 有理规格（`p/d` 形式）：`⌊√(p·d)⌋/d` 的平方 ≤ `p/d`。 -/
theorem sqrtLo_sq_spec {p d : ℕ} (hd : 0 < d) :
    ((Nat.sqrt (p * d) : ℚ) / ((d : ℚ))) * ((Nat.sqrt (p * d) : ℚ) / ((d : ℚ))) ≤
      ((p : ℚ) / (d : ℚ)) := by
  have hd' : (0 : ℚ) < ((d : ℚ)) := by exact_mod_cast hd
  have hnat : Nat.sqrt (p * d) * Nat.sqrt (p * d) ≤ p * d := Nat.sqrt_le _
  have hnat' : ((Nat.sqrt (p * d) : ℚ)) * ((Nat.sqrt (p * d) : ℚ)) ≤ ((p : ℚ) * ((d : ℚ))) := by
    exact_mod_cast hnat
  have hdne : ((d : ℚ)) ≠ 0 := ne_of_gt hd'
  field_simp
  nlinarith [hnat']

/-- 规格（上界的平方形式）：`q ≤ (sqrtHi q)²`（对**所有** `q : ℚ` 成立）。 -/
theorem le_sqrtHi_sq (q : ℚ) : q ≤ sqrtHi q * sqrtHi q := by
  rw [sqrtHi]
  by_cases h : q ≤ 0
  · rw [if_pos h]
    nlinarith
  · rw [if_neg h]
    have hq : 0 < q := not_le.mp h
    have key := sqrtHi_sq_spec (p := q.num.natAbs) (d := q.den) q.den_pos
    rwa [num_den_decomp hq] at key

/-- 规格（下界的平方形式）：`0 ≤ q ⟹ (sqrtLo q)² ≤ q`。 -/
theorem sqrtLo_sq_le (q : ℚ) (hq : 0 ≤ q) : sqrtLo q * sqrtLo q ≤ q := by
  rw [sqrtLo]
  by_cases h : q ≤ 0
  · rw [if_pos h]
    nlinarith
  · rw [if_neg h]
    have hq' : 0 < q := not_le.mp h
    have key := sqrtLo_sq_spec (p := q.num.natAbs) (d := q.den) q.den_pos
    rwa [num_den_decomp hq'] at key

/-! ## 4. 区间层面的 sqrt -/

/-- 区间平方根：`A.sqrt = [sqrtLo A.lo, sqrtHi A.hi]`。 -/
def sqrt (A : RatInterval) : RatInterval := ⟨sqrtLo A.lo, sqrtHi A.hi⟩

/-- 包含性：`x ∈ A ⟹ √x ∈ A.sqrt`。
注意**不需要** `0 ≤ x` 或 `0 ≤ A.lo`：`Real.sqrt` 的单调性在整个 ℝ 上成立，
而两条规格对所有有理端点都成立（`lo ≤ 0` 时 `sqrtLo lo = 0 ≤ √x`）。 -/
theorem sqrt_mem (hA : Mem A x) : Mem A.sqrt (Real.sqrt x) := by
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((sqrtLo A.lo : ℚ) : ℝ) ≤ Real.sqrt x
    exact le_trans (sqrtLo_le_sqrt A.lo) (Real.sqrt_le_sqrt (mem_lo_le hA))
  · show Real.sqrt x ≤ ((sqrtHi A.hi : ℚ) : ℝ)
    exact le_trans (Real.sqrt_le_sqrt (mem_le_hi hA)) (sqrt_le_sqrtHi A.hi)

/-- `Valid` 保持性。 -/
theorem sqrt_valid (hA : Valid A) : Valid A.sqrt := by
  show sqrtLo A.lo ≤ sqrtHi A.hi
  have h : ((sqrtLo A.lo : ℚ) : ℝ) ≤ ((sqrtHi A.hi : ℚ) : ℝ) :=
    le_trans (sqrtLo_le_sqrt A.lo)
      (le_trans (Real.sqrt_le_sqrt (by exact_mod_cast hA)) (sqrt_le_sqrtHi A.hi))
  exact Rat.cast_le.mp h

/-! ## 5. 读数（公式端点方向 / 具体值的 kernel 检验） -/

/-- 整点 `q = 4`（`num = 4, den = 1`）：`⌊√4⌋ = 2`，故 `sqrtLo 4 = 2`、`sqrtHi 4 = 3`。 -/
theorem read_sqrtLo_four : sqrtLo 4 = 2 := by
  rw [sqrtLo, if_neg (by norm_num : ¬ ((4 : ℚ) ≤ 0)), Rat.num_ofNat, Rat.den_ofNat]
  norm_num

theorem read_sqrtHi_four : sqrtHi 4 = 3 := by
  rw [sqrtHi, if_neg (by norm_num : ¬ ((4 : ℚ) ≤ 0)), Rat.num_ofNat, Rat.den_ofNat]
  norm_num

/-- `q = 1/4`（`num = 1, den = 4`）：`⌊√4⌋ = 2`，故 `sqrtLo (1/4) = 1/2`、`sqrtHi (1/4) = 3/4`。 -/
theorem read_sqrtLo_quarter : sqrtLo (1 / 4) = 1 / 2 := by
  rw [sqrtLo, if_neg (by norm_num : ¬ (((1 / 4 : ℚ)) ≤ 0))]
  norm_num

theorem read_sqrtHi_quarter : sqrtHi (1 / 4) = 3 / 4 := by
  rw [sqrtHi, if_neg (by norm_num : ¬ (((1 / 4 : ℚ)) ≤ 0))]
  norm_num

/-- 区间读数：`[1,4]` 的平方根区间包含 `√4`。 -/
theorem read_sqrt_mem : Mem (sqrt (intv 1 4)) (Real.sqrt 4) := by
  refine sqrt_mem (A := intv 1 4) (x := (4 : ℝ)) ?_
  norm_num [intv, Mem, toSet]

/-- 平方形式规格的读数（同时是变异对照 `mutant_sqrt_spec` 的正向孪生）：
`q = 2` 时 `2 ≤ (sqrtHi 2)²` 成立，而 `2 ≤ (sqrtLo 2)²` 为假。 -/
theorem read_sqrtHi_sq_two : (2 : ℚ) ≤ sqrtHi 2 * sqrtHi 2 := by
  norm_num [sqrtHi, Rat.num_ofNat, Rat.den_ofNat]

theorem read_sqrtLo_sq_two : sqrtLo 2 * sqrtLo 2 ≤ 2 := by
  norm_num [sqrtLo, Rat.num_ofNat, Rat.den_ofNat]

/-- **严格下界原语**：`0 < q ⟹ 0 < sqrtLo q`（与 `sqrtLo_nonneg` 同族，但**严格**）。
消费方（F1 球级 `dUxIv`/`dUyIv` 吃 `h0`/`h1`）需要 `(2·sqrt I).lo > 0` 的**严格**性，
非严格的 `sqrtLo_nonneg` 不够用。

口径（本工程）：**不得用非严格引理凑严格结论**；本证明走 `sqrtLo` 的定义：
`q > 0` 时 `sqrtLo q = ⌊√(p·d)⌋/d`，其中 `p = |q.num| ≥ 1`、`d = q.den ≥ 1`
⟹ `p·d ≥ 1` ⟹ `⌊√(p·d)⌋ ≥ ⌊√1⌋ = 1` ⟹ `sqrtLo q ≥ 1/d > 0`。 -/
theorem sqrtLo_pos {q : ℚ} (hq : 0 < q) : 0 < sqrtLo q := by
  rw [sqrtLo, if_neg (not_le.mpr hq)]
  apply div_pos
  · have hnum : 0 < q.num := Rat.num_pos.mpr hq
    have h1 : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum)
    have hprod : 0 < q.num.natAbs * q.den := Nat.mul_pos h1 q.den_pos
    have hge : 1 ≤ Nat.sqrt (q.num.natAbs * q.den) := by
      calc (1 : ℕ) = Nat.sqrt 1 := Nat.sqrt_one.symm
        _ ≤ Nat.sqrt (q.num.natAbs * q.den) := Nat.sqrt_le_sqrt hprod
    have : (0 : ℚ) < (Nat.sqrt (q.num.natAbs * q.den) : ℚ) := by exact_mod_cast hge
    exact this
  · have : (0 : ℚ) < ((q.den : ℕ) : ℚ) := by exact_mod_cast q.den_pos
    exact this

end RatInterval

end N11Formalization

