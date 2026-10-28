/-
  N11Formalization.Interval.Core
  ==============================

  可信区间算术内核 —— 基础类型 + ℝ 侧语义 + 四则运算的**包含性 soundness**。

  设计口径（对应 GUIDE §5「对每个算子证明包含性 / 形式化向外舍入和区间包含语义」）：

  * 端点是**精确有理数** `ℚ`，不经过宿主浮点（`Float`/`Float32`）。
  * 语义在 **ℝ 侧**：`RatInterval.toSet` / `Mem` 把区间解释成实数集合，
    最终证书要断言的实数不等式可以直接由 `Mem` 承接。
  * 每个算子给两条东西：
      (a) `*_mem`：包含性（soundness）；
      (b) `*_valid`：`Valid`（合法区间）的保持性（能证的都证）。
  * `mul` 的四端点用 `min`/`max` 嵌套；`Readings` 段用**具体实例**做端点的
    向外检验（防止 min/max 写反）。

  纪律：本文件不含 `sorry`、自定义 `axiom`、`native_decide`、`#eval`。
  数值验证用 `norm_num`；不用 `decide`（Lean 4.33.1 下 `Rat` 的 `Decidable`
  实例在内核里不归约，见 DEAD.md B1）。
-/
import Mathlib

namespace N11Formalization

/-! ## 0. ℝ 侧辅助引理（乘法端点的 min/max 界）

下面两条是 `mul` 的全部数学内容：矩形上双线性函数 `x*y` 的取值落在
「四角乘积」的 min/max 之间。它们先只讲实数，`RatInterval` 层只需展开展开定义。 -/

/-- 实数上界：`x ∈ [a,b]`、`y ∈ [c,d]` ⟹ `x*y ≤ max(max(ac,ad),max(bc,bd))`。 -/
theorem mul_le_max4 {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  -- 第一步：固定 x 时 `y ↦ x*y` 线性，故 `x*y ≤ max (x*c) (x*d)`
  have step1 : x * y ≤ max (x * c) (x * d) := by
    by_cases hx : (0 : ℝ) ≤ x
    · exact le_trans (mul_le_mul_of_nonneg_left hd hx) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left hc (le_of_lt (not_le.mp hx))) (le_max_left _ _)
  -- 第二步：`x*c`、`x*d` 各自按 c、d 的符号落回四角
  have step2 : x * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    by_cases hc' : (0 : ℝ) ≤ c
    · exact le_trans (mul_le_mul_of_nonneg_right hb hc')
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (mul_le_mul_of_nonpos_right ha (le_of_lt (not_le.mp hc')))
        (le_trans (le_max_left _ _) (le_max_left _ _))
  have step3 : x * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    by_cases hd' : (0 : ℝ) ≤ d
    · exact le_trans (mul_le_mul_of_nonneg_right hb hd')
        (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (mul_le_mul_of_nonpos_right ha (le_of_lt (not_le.mp hd')))
        (le_trans (le_max_right _ _) (le_max_left _ _))
  exact le_trans step1 (max_le step2 step3)

/-- 实数下界：`x ∈ [a,b]`、`y ∈ [c,d]` ⟹ `min(min(ac,ad),min(bc,bd)) ≤ x*y`。 -/
theorem min4_le_mul {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have step1 : min (x * c) (x * d) ≤ x * y := by
    by_cases hx : (0 : ℝ) ≤ x
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hc hx)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hd (le_of_lt (not_le.mp hx)))
  have step2 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * c := by
    by_cases hc' : (0 : ℝ) ≤ c
    · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
        (mul_le_mul_of_nonneg_right ha hc')
    · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
        (mul_le_mul_of_nonpos_right hb (le_of_lt (not_le.mp hc')))
  have step3 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * d := by
    by_cases hd' : (0 : ℝ) ≤ d
    · exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _))
        (mul_le_mul_of_nonneg_right ha hd')
    · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
        (mul_le_mul_of_nonpos_right hb (le_of_lt (not_le.mp hd')))
  exact le_trans (le_min step2 step3) step1

/-! ## 1. 区间类型与 ℝ 侧语义 -/

/-- 精确有理闭区间 `[lo, hi]`（端点均为精确有理数）。 -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace RatInterval

variable {A B C : RatInterval} {x y : ℝ}

/-- 合法区间：`lo ≤ hi`。 -/
def Valid (I : RatInterval) : Prop := I.lo ≤ I.hi

/-- 实数语义：区间所表示的实数集合 `{x | lo ≤ x ≤ hi}`。 -/
def toSet (I : RatInterval) : Set ℝ := {x | (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)}

/-- 成员关系（ℝ 侧语义）。 -/
def Mem (I : RatInterval) (x : ℝ) : Prop := x ∈ I.toSet

theorem mem_iff {I : RatInterval} {x : ℝ} : Mem I x ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) :=
  Iff.rfl

theorem mem_lo_le (h : Mem I x) : (I.lo : ℝ) ≤ x := (mem_iff.mp h).1

theorem mem_le_hi (h : Mem I x) : x ≤ (I.hi : ℝ) := (mem_iff.mp h).2

/-- 合法性的实数读法。 -/
theorem Valid.lo_le_hi (h : Valid I) : (I.lo : ℝ) ≤ (I.hi : ℝ) := by
  exact_mod_cast h

/-- 反方向：只要区间在 ℝ 侧非空（有成员），它就是合法区间。
（下游拿到一个「包含某个实数的区间」时，不必再单独携带 `Valid` 前提。） -/
theorem valid_of_mem (h : Mem I x) : Valid I :=
  Rat.cast_le.mp (le_trans (mem_lo_le h) (mem_le_hi h))

/-- 退化为一个有理点的区间。 -/
def ofRat (q : ℚ) : RatInterval := ⟨q, q⟩

theorem ofRat_mem (q : ℚ) : Mem (ofRat q) (q : ℝ) := ⟨le_refl _, le_refl _⟩

/-- 「I 包含 J」（参数顺序：先宽区间后窄区间）。 -/
def Contains (I J : RatInterval) : Prop := I.lo ≤ J.lo ∧ J.hi ≤ I.hi

/-- 相容性：把窄区间的成员搬到宽区间（证书链里「盒收窄/放宽」要用的接口）。 -/
theorem mem_of_contains (h : Contains I J) (hx : Mem J x) : Mem I x :=
  mem_iff.mpr
    ⟨le_trans (Rat.cast_le.mpr h.1) (mem_lo_le hx), le_trans (mem_le_hi hx) (Rat.cast_le.mpr h.2)⟩

theorem contains_refl (I : RatInterval) : Contains I I := ⟨le_refl _, le_refl _⟩

theorem Contains.trans (h₁ : Contains I J) (h₂ : Contains J C) : Contains I C :=
  ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩

/-! ## 2. 四则运算（外向端点 + 包含性） -/

/-- 加法：端点相加（精确，无舍入）。 -/
def add (A B : RatInterval) : RatInterval := ⟨A.lo + B.lo, A.hi + B.hi⟩

theorem add_mem (hA : Mem A x) (hB : Mem B y) : Mem (A.add B) (x + y) := by
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((A.lo + B.lo : ℚ) : ℝ) ≤ x + y
    push_cast
    linarith [mem_lo_le hA, mem_lo_le hB]
  · show x + y ≤ ((A.hi + B.hi : ℚ) : ℝ)
    push_cast
    linarith [mem_le_hi hA, mem_le_hi hB]

theorem add_valid (hA : Valid A) (hB : Valid B) : Valid (A.add B) :=
  add_le_add hA hB

/-- 取负：端点取负后交换。 -/
def neg (A : RatInterval) : RatInterval := ⟨-A.hi, -A.lo⟩

theorem neg_mem (hA : Mem A x) : Mem A.neg (-x) := by
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((-A.hi : ℚ) : ℝ) ≤ -x
    push_cast
    linarith [mem_le_hi hA]
  · show -x ≤ ((-A.lo : ℚ) : ℝ)
    push_cast
    linarith [mem_lo_le hA]

theorem neg_valid (hA : Valid A) : Valid A.neg :=
  neg_le_neg hA

/-- 减法：`A - B = A + (-B)` 的端点形式。 -/
def sub (A B : RatInterval) : RatInterval := ⟨A.lo - B.hi, A.hi - B.lo⟩

theorem sub_mem (hA : Mem A x) (hB : Mem B y) : Mem (A.sub B) (x - y) := by
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((A.lo - B.hi : ℚ) : ℝ) ≤ x - y
    push_cast
    linarith [mem_lo_le hA, mem_le_hi hB]
  · show x - y ≤ ((A.hi - B.lo : ℚ) : ℝ)
    push_cast
    linarith [mem_le_hi hA, mem_lo_le hB]

theorem sub_valid (hA : Valid A) (hB : Valid B) : Valid (A.sub B) :=
  sub_le_sub hA hB

/-- 乘法：四角乘积的 min/max（区间乘法的外向端点）。 -/
def mul (A B : RatInterval) : RatInterval :=
  ⟨min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)),
   max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))⟩

theorem mul_mem (hA : Mem A x) (hB : Mem B y) : Mem (A.mul B) (x * y) := by
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((min (min (A.lo * B.lo) (A.lo * B.hi))
        (min (A.hi * B.lo) (A.hi * B.hi)) : ℚ) : ℝ) ≤ x * y
    simp only [Rat.cast_min, Rat.cast_mul]
    exact min4_le_mul (mem_lo_le hA) (mem_le_hi hA) (mem_lo_le hB) (mem_le_hi hB)
  · show x * y ≤ ((max (max (A.lo * B.lo) (A.lo * B.hi))
        (max (A.hi * B.lo) (A.hi * B.hi)) : ℚ) : ℝ)
    simp only [Rat.cast_max, Rat.cast_mul]
    exact mul_le_max4 (mem_lo_le hA) (mem_le_hi hA) (mem_lo_le hB) (mem_le_hi hB)

/-- `mul` 的合法性**无条件**成立（min ≤ max）。 -/
theorem mul_valid (A B : RatInterval) : Valid (A.mul B) := by
  show min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi))
      ≤ max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))
  exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))

/-- 倒数：要求 `0 ∉ B`（即 `B.hi < 0 ∨ 0 < B.lo`）。
`y ↦ y⁻¹` 在正区间与负区间上都单调递减，故端点同样是「交换后取倒数」。 -/
def inv (B : RatInterval) (_h : B.hi < 0 ∨ 0 < B.lo) : RatInterval := ⟨B.hi⁻¹, B.lo⁻¹⟩

theorem inv_mem (hB : Mem B y) (h : B.hi < 0 ∨ 0 < B.lo) : Mem (B.inv h) y⁻¹ := by
  have hypos : 0 < y ∨ y < 0 := by
    rcases h with h | h
    · exact Or.inr (lt_of_le_of_lt (mem_le_hi hB) (by exact_mod_cast h))
    · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast h) (mem_lo_le hB))
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show (((B.hi⁻¹ : ℚ)) : ℝ) ≤ y⁻¹
    push_cast
    rcases hypos with hy | hy
    · -- 0 < y：hi ≥ y > 0，用正侧反序律
      exact (inv_le_inv₀ (lt_of_lt_of_le hy (mem_le_hi hB)) hy).mpr (mem_le_hi hB)
    · -- y < 0：必须走 hi < 0 支
      rcases h with hh | hh
      · exact (inv_le_inv_of_neg (by exact_mod_cast hh) hy).mpr (mem_le_hi hB)
      · exact absurd (lt_trans hy (lt_of_lt_of_le (by exact_mod_cast hh) (mem_lo_le hB)))
          (lt_irrefl y)
  · show y⁻¹ ≤ (((B.lo⁻¹ : ℚ)) : ℝ)
    push_cast
    rcases hypos with hy | hy
    · -- 0 < y：必须走 0 < lo 支
      rcases h with hh | hh
      · have hlt : (B.hi : ℝ) < 0 := by exact_mod_cast hh
        exact absurd (lt_of_lt_of_le hy (mem_le_hi hB)) (not_lt.mpr hlt.le)
      · exact (inv_le_inv₀ hy (by exact_mod_cast hh)).mpr (mem_lo_le hB)
    · -- y < 0：由 lo ≤ y < 0 直接得到 lo < 0，用负侧反序律
      exact (inv_le_inv_of_neg hy (lt_of_le_of_lt (mem_lo_le hB) hy)).mpr (mem_lo_le hB)

theorem inv_valid (hB : Valid B) (h : B.hi < 0 ∨ 0 < B.lo) : Valid (B.inv h) := by
  have hreal : ((B.hi⁻¹ : ℚ) : ℝ) ≤ ((B.lo⁻¹ : ℚ) : ℝ) := by
    push_cast
    rcases h with h | h
    · -- hi < 0：hi⁻¹ ≤ lo⁻¹（负侧反序）
      exact (inv_le_inv_of_neg (by exact_mod_cast h)
        (by exact_mod_cast lt_of_le_of_lt hB h)).mpr (Valid.lo_le_hi hB)
    · -- 0 < lo：hi⁻¹ ≤ lo⁻¹（正侧反序）
      exact (inv_le_inv₀ (by exact_mod_cast lt_of_lt_of_le h hB)
        (by exact_mod_cast h)).mpr (Valid.lo_le_hi hB)
  exact Rat.cast_le.mp hreal

/-- 除法：`A / B = A * B⁻¹`（`B` 不含 0）。 -/
def div (A B : RatInterval) (h : B.hi < 0 ∨ 0 < B.lo) : RatInterval := A.mul (B.inv h)

theorem div_mem (hA : Mem A x) (hB : Mem B y) (h : B.hi < 0 ∨ 0 < B.lo) :
    Mem (A.div B h) (x / y) := by
  rw [div_eq_mul_inv x y]
  exact mul_mem hA (inv_mem hB h)

theorem div_valid (_hA : Valid A) (_hB : Valid B) (h : B.hi < 0 ∨ 0 < B.lo) :
    Valid (A.div B h) :=
  mul_valid A (B.inv h)

/-! ## 3. 具体实例读数（抗 min/max 写反的向外检验）

`mul` 的四端点用 min/max 写，方向写错时**一般**不会立刻有编译错误。
下面把混合符号盒的真实乘积点逐个喂给 `mul_mem`：若 min/max 写反，
这些命题为假、`mul_mem` 的证明不可能通过。因此
「`mul_mem` 编译通过 + 下列实例」构成对端点方向的 kernel 级检验。 -/

/-- 具体区间（读数的书写便利）。 -/
def intv (a b : ℚ) : RatInterval := ⟨a, b⟩

/-- 有理点落进区间的通用构造。 -/
theorem intv_mem {a b q : ℚ} (h1 : a ≤ q) (h2 : q ≤ b) : Mem (intv a b) (q : ℝ) := by
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show (a : ℝ) ≤ (q : ℝ)
    exact_mod_cast h1
  · show (q : ℝ) ≤ (b : ℝ)
    exact_mod_cast h2

theorem read_add : Mem (add (intv 1 2) (intv 3 4)) ((2 : ℝ) + 4) := by
  refine add_mem (A := intv 1 2) (B := intv 3 4) (x := (2 : ℝ)) (y := (4 : ℝ)) ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

theorem read_neg : Mem (neg (intv (-3) 5)) (-(5 : ℝ)) := by
  refine neg_mem (A := intv (-3) 5) (x := (5 : ℝ)) ?_
  norm_num [intv, Mem, toSet]

theorem read_sub : Mem (sub (intv 1 2) (intv 3 4)) ((2 : ℝ) - 4) := by
  refine sub_mem (A := intv 1 2) (B := intv 3 4) (x := (2 : ℝ)) (y := (4 : ℝ)) ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

/-- 混合符号盒 `[-1,2] * [-3,4]`：四角乘积 `3, -4, -6, 8`，故区间应为 `[-6,8]`。 -/
theorem read_mul_pp : Mem (mul (intv (-1) 2) (intv (-3) 4)) ((2 : ℝ) * 4) := by
  refine mul_mem (A := intv (-1) 2) (B := intv (-3) 4) (x := (2 : ℝ)) (y := (4 : ℝ)) ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

theorem read_mul_pn : Mem (mul (intv (-1) 2) (intv (-3) 4)) ((-1 : ℝ) * 4) := by
  refine mul_mem (A := intv (-1) 2) (B := intv (-3) 4) (x := (-1 : ℝ)) (y := (4 : ℝ)) ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

theorem read_mul_np : Mem (mul (intv (-1) 2) (intv (-3) 4)) ((2 : ℝ) * (-3)) := by
  refine mul_mem (A := intv (-1) 2) (B := intv (-3) 4) (x := (2 : ℝ)) (y := (-3 : ℝ)) ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

theorem read_mul_nn : Mem (mul (intv (-1) 2) (intv (-3) 4)) ((-1 : ℝ) * (-3)) := by
  refine mul_mem (A := intv (-1) 2) (B := intv (-3) 4) (x := (-1 : ℝ)) (y := (-3 : ℝ)) ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

/-- 正盒读数：`[1,2] * [3,4] = [3,8]`。 -/
theorem read_mul_pos : Mem (mul (intv 1 2) (intv 3 4)) ((2 : ℝ) * 4) := by
  refine mul_mem (A := intv 1 2) (B := intv 3 4) (x := (2 : ℝ)) (y := (4 : ℝ)) ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

/-- 负盒读数：`[-2,-1] * [-4,-3] = [3,8]`。 -/
theorem read_mul_neg : Mem (mul (intv (-2) (-1)) (intv (-4) (-3))) ((-2 : ℝ) * (-4)) := by
  refine mul_mem (A := intv (-2) (-1)) (B := intv (-4) (-3)) (x := (-2 : ℝ)) (y := (-4 : ℝ))
    ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

/-- 正区间倒数：`[3,4]⁻¹ = [1/4, 1/3]`。 -/
theorem read_inv_pos : Mem (inv (intv 3 4) (Or.inr (by norm_num : (0 : ℚ) < 3))) (4 : ℝ)⁻¹ := by
  refine inv_mem (B := intv 3 4) (y := (4 : ℝ)) ?_ ?_
  norm_num [intv, Mem, toSet]

/-- 负区间倒数：`[-4,-3]⁻¹ = [-1/3, -1/4]`（端点仍是交换取倒数）。 -/
theorem read_inv_neg : Mem (inv (intv (-4) (-3)) (Or.inl (by norm_num : (-3 : ℚ) < 0)))
    (-3 : ℝ)⁻¹ := by
  refine inv_mem (B := intv (-4) (-3)) (y := (-3 : ℝ)) ?_ ?_
  norm_num [intv, Mem, toSet]

theorem read_div : Mem (div (intv 1 2) (intv 3 4) (Or.inr (by norm_num : (0 : ℚ) < 3)))
    ((2 : ℝ) / 4) := by
  refine div_mem (A := intv 1 2) (B := intv 3 4) (x := (2 : ℝ)) (y := (4 : ℝ)) ?_ ?_ ?_
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

/-! ## 4. 自然数幂 -/

/-- 自然数幂：`A^n = [lo^n, hi^n]`。 -/
def pow (A : RatInterval) (n : ℕ) : RatInterval := ⟨A.lo ^ n, A.hi ^ n⟩

theorem pow_mem (h : 0 ≤ A.lo) (hA : Mem A x) (n : ℕ) : Mem (A.pow n) (x ^ n) := by
  have hx : (0 : ℝ) ≤ x := le_trans (by exact_mod_cast h) (mem_lo_le hA)
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show ((A.lo ^ n : ℚ) : ℝ) ≤ x ^ n
    push_cast
    exact pow_le_pow_left₀ (by exact_mod_cast h) (mem_lo_le hA) n
  · show x ^ n ≤ ((A.hi ^ n : ℚ) : ℝ)
    push_cast
    exact pow_le_pow_left₀ hx (mem_le_hi hA) n

theorem pow_valid (h : 0 ≤ A.lo) (hA : Valid A) (n : ℕ) : Valid (A.pow n) :=
  pow_le_pow_left₀ h hA n

theorem read_pow : Mem (pow (intv 1 2) 3) ((2 : ℝ) ^ 3) := by
  refine pow_mem (A := intv 1 2) (x := (2 : ℝ)) ?_ ?_ 3
  · norm_num [intv, Mem, toSet]
  · norm_num [intv, Mem, toSet]

/-! ### 端点等值读数（直接检验 min/max 方向）

以下等式把「四角乘积的 min/max」算到底，方向写反/端点写错立刻失败。 -/

theorem read_endpoints_add : add (intv 1 2) (intv 3 4) = intv 4 6 := by
  norm_num [intv, add]

theorem read_endpoints_neg : neg (intv (-3) 5) = intv (-5) 3 := by
  norm_num [intv, neg]

theorem read_endpoints_sub : sub (intv 1 2) (intv 3 4) = intv (-3) (-1) := by
  norm_num [intv, sub]

theorem read_endpoints_mul_pos : mul (intv 1 2) (intv 3 4) = intv 3 8 := by
  norm_num [intv, mul]

theorem read_endpoints_mul_neg : mul (intv (-2) (-1)) (intv (-4) (-3)) = intv 3 8 := by
  norm_num [intv, mul]

/-- 混合符号盒：四角乘积 `3, -4, -6, 8` ⟹ `[-6, 8]`。 -/
theorem read_endpoints_mul_mixed : mul (intv (-1) 2) (intv (-3) 4) = intv (-6) 8 := by
  norm_num [intv, mul]

/-- 跨零盒：`[-1,1] * [-1,1] = [-1,1]`。 -/
theorem read_endpoints_mul_centered : mul (intv (-1) 1) (intv (-1) 1) = intv (-1) 1 := by
  norm_num [intv, mul]

theorem read_endpoints_inv_pos :
    inv (intv 3 4) (Or.inr (by norm_num : (0 : ℚ) < 3)) = intv (1 / 4) (1 / 3) := by
  norm_num [intv, inv]

theorem read_endpoints_inv_neg :
    inv (intv (-4) (-3)) (Or.inl (by norm_num : (-3 : ℚ) < 0)) = intv (-(1 / 3)) (-(1 / 4)) := by
  norm_num [intv, inv]

theorem read_endpoints_div :
    div (intv 1 2) (intv 3 4) (Or.inr (by norm_num : (0 : ℚ) < 3)) = intv (1 / 4) (2 / 3) := by
  norm_num [intv, div, mul, inv]

theorem read_endpoints_pow : pow (intv 1 2) 3 = intv 1 8 := by
  norm_num [intv, pow]

end RatInterval

end N11Formalization
