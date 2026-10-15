/-
  N11Formalization.Interval.Trig
  ==============================

  M5（sin/cos 的**有理外向界**）：把 `Real.sin_bound` / `Real.cos_bound`（显式有理余项）
  与 `Real.pi_gt_d20` / `Real.pi_lt_d20`（20 位 π 有理界）组装成区间算子。

  覆盖范围（诚实标注，勿高估）：
  * π 与 π/2 的精确有理夹逼；
  * **点级**规格：`|q| ≤ 1` 时 `sinLo q ≤ sin q ≤ sinHi q`、`cosLo q ≤ cos q ≤ cosHi q`
    （端点精确有理；余项 `|q|⁵/100`、`|q|⁴·(5/96)` 是精确有理数）；
  * **区间级** `sinI` / `cosI`：`A ⊆ [-1,1]` 时用单调性给外向界，窗口外**保守回退** `[-1,1]`
    （不猜），故 `sinI_mem` / `cosI_mem` **无条件**成立，可直接经 `IExpr.app1` 注册；
  * **未覆盖**：任意有理输入的**范围约化**（把 `q` 约到 `k·(π/2) + r`，`|r| ≤ 1`）。
    精确待办与路线见 `INTERVAL-GAPS.md` §3/§5-M5。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Core
import N11Formalization.Interval.Eval

namespace N11Formalization

namespace RatInterval

/-! ## 1. π 与 π/2 的有理夹逼 -/

/-- `π` 的下界（20 位，来自 `Real.pi_gt_d20`）。 -/
def piLo : ℚ := 314159265358979323846 / 10 ^ 20

/-- `π` 的上界（20 位，来自 `Real.pi_lt_d20`）。 -/
def piHi : ℚ := 314159265358979323847 / 10 ^ 20

theorem piLo_lt_pi : ((piLo : ℚ) : ℝ) < Real.pi := by
  have h := Real.pi_gt_d20
  have h' : ((piLo : ℚ) : ℝ) = 3.14159265358979323846 := by norm_num [piLo]
  rw [h']
  exact h

theorem pi_lt_piHi : Real.pi < ((piHi : ℚ) : ℝ) := by
  have h := Real.pi_lt_d20
  have h' : ((piHi : ℚ) : ℝ) = 3.14159265358979323847 := by norm_num [piHi]
  rw [h']
  exact h

theorem pi_div_two_lo_lt : (((piLo / 2 : ℚ)) : ℝ) < Real.pi / 2 := by
  have h := piLo_lt_pi
  have h' : (((piLo / 2 : ℚ)) : ℝ) = ((piLo : ℚ) : ℝ) / 2 := by push_cast; ring
  rw [h']
  linarith

theorem pi_div_two_lt_hi : Real.pi / 2 < (((piHi / 2 : ℚ)) : ℝ) := by
  have h := pi_lt_piHi
  have h' : (((piHi / 2 : ℚ)) : ℝ) = ((piHi : ℚ) : ℝ) / 2 := by push_cast; ring
  rw [h']
  linarith

/-- `1 < π/2`：窗口 `[-1,1]` 落在 `[-π/2, π/2]` 内的全部依据。 -/
theorem one_lt_pi_div_two : (1 : ℝ) < Real.pi / 2 := by
  have h := Real.pi_gt_three
  linarith

theorem one_le_pi_div_two : (1 : ℝ) ≤ Real.pi / 2 := le_of_lt one_lt_pi_div_two

theorem neg_pi_div_two_le_neg_one : -(Real.pi / 2) ≤ (-1 : ℝ) := by
  linarith [one_le_pi_div_two]

/-! ## 2. 点级规格（`|q| ≤ 1`） -/

/-- `sin` 的有理下端点 `q − q³/6 − |q|⁵/100`。 -/
def sinLo (q : ℚ) : ℚ := q - q ^ 3 / 6 - |q| ^ 5 / 100

/-- `sin` 的有理上端点 `q − q³/6 + |q|⁵/100`。 -/
def sinHi (q : ℚ) : ℚ := q - q ^ 3 / 6 + |q| ^ 5 / 100

/-- `cos` 的有理下端点 `1 − q²/2 − |q|⁴·(5/96)`。 -/
def cosLo (q : ℚ) : ℚ := 1 - q ^ 2 / 2 - |q| ^ 4 * (5 / 96)

/-- `cos` 的有理上端点 `1 − q²/2 + |q|⁴·(5/96)`。 -/
def cosHi (q : ℚ) : ℚ := 1 - q ^ 2 / 2 + |q| ^ 4 * (5 / 96)

theorem cosHi_zero : cosHi 0 = 1 := by norm_num [cosHi]

/-- `q ≥ 0 ∧ q ≤ 1 ⟹ |q| ≤ 1`（读数用的小引理）。 -/
theorem abs_le_one_of_bounds {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : |(q : ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (by exact_mod_cast h0)]
  exact_mod_cast h1

theorem sinLo_le_sin {q : ℚ} (hq : |(q : ℝ)| ≤ 1) : ((sinLo q : ℚ) : ℝ) ≤ Real.sin (q : ℝ) := by
  have hb := Real.sin_bound (x := (q : ℝ)) hq
  have h1 : -(|(q : ℝ)| ^ 5 / 100) ≤ Real.sin (q : ℝ) - ((q : ℝ) - (q : ℝ) ^ 3 / 6) :=
    (abs_le.mp hb).1
  show (((q - q ^ 3 / 6 - |q| ^ 5 / 100 : ℚ)) : ℝ) ≤ Real.sin (q : ℝ)
  push_cast
  linarith

theorem sin_le_sinHi {q : ℚ} (hq : |(q : ℝ)| ≤ 1) : Real.sin (q : ℝ) ≤ ((sinHi q : ℚ) : ℝ) := by
  have hb := Real.sin_bound (x := (q : ℝ)) hq
  have h1 : Real.sin (q : ℝ) - ((q : ℝ) - (q : ℝ) ^ 3 / 6) ≤ |(q : ℝ)| ^ 5 / 100 :=
    (abs_le.mp hb).2
  show Real.sin (q : ℝ) ≤ (((q - q ^ 3 / 6 + |q| ^ 5 / 100 : ℚ)) : ℝ)
  push_cast
  linarith

theorem cosLo_le_cos {q : ℚ} (hq : |(q : ℝ)| ≤ 1) : ((cosLo q : ℚ) : ℝ) ≤ Real.cos (q : ℝ) := by
  have hb := Real.cos_bound (x := (q : ℝ)) hq
  have h1 : -(|(q : ℝ)| ^ 4 * (5 / 96)) ≤ Real.cos (q : ℝ) - (1 - (q : ℝ) ^ 2 / 2) :=
    (abs_le.mp hb).1
  show (((1 - q ^ 2 / 2 - |q| ^ 4 * (5 / 96) : ℚ)) : ℝ) ≤ Real.cos (q : ℝ)
  push_cast
  linarith

theorem cos_le_cosHi {q : ℚ} (hq : |(q : ℝ)| ≤ 1) : Real.cos (q : ℝ) ≤ ((cosHi q : ℚ) : ℝ) := by
  have hb := Real.cos_bound (x := (q : ℝ)) hq
  have h1 : Real.cos (q : ℝ) - (1 - (q : ℝ) ^ 2 / 2) ≤ |(q : ℝ)| ^ 4 * (5 / 96) :=
    (abs_le.mp hb).2
  show Real.cos (q : ℝ) ≤ (((1 - q ^ 2 / 2 + |q| ^ 4 * (5 / 96) : ℚ)) : ℝ)
  push_cast
  linarith

/-! ## 3. 整体界（回退支用） -/

theorem neg_one_le_sin (x : ℝ) : -1 ≤ Real.sin x := by
  have h := Real.sin_le_one (-x)
  rw [Real.sin_neg] at h
  linarith

theorem sin_le_one' (x : ℝ) : Real.sin x ≤ 1 := Real.sin_le_one x

theorem neg_one_le_cos (x : ℝ) : -1 ≤ Real.cos x := (abs_le.mp (Real.abs_cos_le_one x)).1

theorem cos_le_one' (x : ℝ) : Real.cos x ≤ 1 := (abs_le.mp (Real.abs_cos_le_one x)).2

/-! ## 4. 单调性/包络辅助 -/

/-- `[0,1]` 上 `cos` 递减（用 `cos t = -sin (t − π/2)` 化归到 `sin` 在 `[-π/2, π/2]` 上的单调性）。 -/
theorem cos_le_cos_of_le_on_unit {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x ≤ y) :
    Real.cos y ≤ Real.cos x := by
  have hcos : ∀ t : ℝ, Real.cos t = -Real.sin (t - Real.pi / 2) := by
    intro t
    have h := Real.cos_add_pi_div_two (t - Real.pi / 2)
    rw [show t - Real.pi / 2 + Real.pi / 2 = t by ring] at h
    exact h
  rw [hcos y, hcos x]
  have hsin : Real.sin (x - Real.pi / 2) ≤ Real.sin (y - Real.pi / 2) := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two (x := x - Real.pi / 2) (y := y - Real.pi / 2)
      ?_ ?_ (by linarith)
    · linarith [one_le_pi_div_two]
    · linarith [one_le_pi_div_two]
  linarith

/-- 区间内点的绝对值被两端点绝对值之最大值控制。 -/
theorem abs_le_max_abs_endpoints {lo hi x : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    |x| ≤ max |lo| |hi| := by
  have hM : lo ≤ max |lo| |hi| := le_trans (le_abs_self lo) (le_max_left _ _)
  have hM' : hi ≤ max |lo| |hi| := le_trans (le_abs_self hi) (le_max_right _ _)
  have hMl : -max |lo| |hi| ≤ lo := le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le lo)
  have hMr : -max |lo| |hi| ≤ hi := le_trans (neg_le_neg (le_max_right _ _)) (neg_abs_le hi)
  rw [abs_le]
  constructor <;> linarith

/-! ## 5. 区间级算子（窗口内给界 + 窗口外保守回退） -/

/-- `sin` 的区间算子：`A ⊆ [-1,1]` 用端点公式，否则回退 `[-1,1]`。 -/
def sinI (A : RatInterval) : RatInterval :=
  if -1 ≤ A.lo ∧ A.hi ≤ 1 then ⟨sinLo A.lo, sinHi A.hi⟩ else intv (-1) 1

/-- `cos` 的区间算子：窗口内下界取 `|·|` 最大端点处的 `cosLo`，上界取 `1`；否则回退 `[-1,1]`。 -/
def cosI (A : RatInterval) : RatInterval :=
  if -1 ≤ A.lo ∧ A.hi ≤ 1 then ⟨cosLo (max |A.lo| |A.hi|), cosHi 0⟩ else intv (-1) 1

theorem sinI_mem {A : RatInterval} {x : ℝ} (hA : Mem A x) : Mem (sinI A) (Real.sin x) := by
  by_cases h : -1 ≤ A.lo ∧ A.hi ≤ 1
  · rw [sinI, if_pos h]
    have hV : A.lo ≤ A.hi := valid_of_mem hA
    have hV' : (A.lo : ℝ) ≤ (A.hi : ℝ) := by exact_mod_cast hV
    have hlo : (-1 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
    have hhi : (A.hi : ℝ) ≤ 1 := by exact_mod_cast h.2
    have hlo' : -(Real.pi / 2) ≤ (A.lo : ℝ) := le_trans neg_pi_div_two_le_neg_one hlo
    have hhi' : (A.hi : ℝ) ≤ Real.pi / 2 := le_trans hhi one_le_pi_div_two
    have habs_lo : |((A.lo : ℚ) : ℝ)| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have habs_hi : |((A.hi : ℚ) : ℝ)| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((sinLo A.lo : ℚ) : ℝ) ≤ Real.sin x
      have hmono : Real.sin (A.lo : ℝ) ≤ Real.sin x :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (x := (A.lo : ℝ)) (y := x) hlo'
          (by linarith [mem_le_hi hA, hhi']) (mem_lo_le hA)
      exact le_trans (sinLo_le_sin habs_lo) hmono
    · show Real.sin x ≤ ((sinHi A.hi : ℚ) : ℝ)
      have hmono : Real.sin x ≤ Real.sin (A.hi : ℝ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (x := x) (y := (A.hi : ℝ))
          (by linarith [mem_lo_le hA, hlo']) hhi' (mem_le_hi hA)
      exact le_trans hmono (sin_le_sinHi habs_hi)
  · rw [sinI, if_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.sin x
      push_cast
      exact neg_one_le_sin x
    · show Real.sin x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact sin_le_one' x

theorem cosI_mem {A : RatInterval} {x : ℝ} (hA : Mem A x) : Mem (cosI A) (Real.cos x) := by
  by_cases h : -1 ≤ A.lo ∧ A.hi ≤ 1
  · rw [cosI, if_pos h]
    have hV : A.lo ≤ A.hi := valid_of_mem hA
    have hV' : (A.lo : ℝ) ≤ (A.hi : ℝ) := by exact_mod_cast hV
    have hlo : (-1 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
    have hhi : (A.hi : ℝ) ≤ 1 := by exact_mod_cast h.2
    have hcast : (((max |A.lo| |A.hi| : ℚ)) : ℝ) = max |((A.lo : ℚ) : ℝ)| |((A.hi : ℚ) : ℝ)| := by
      push_cast
      rfl
    have hM1 : (((max |A.lo| |A.hi| : ℚ)) : ℝ) ≤ 1 := by
      rw [hcast]
      refine max_le ?_ ?_ <;> rw [abs_le] <;> exact ⟨by linarith, by linarith⟩
    have hMmem : |x| ≤ (((max |A.lo| |A.hi| : ℚ)) : ℝ) := by
      rw [hcast]
      exact abs_le_max_abs_endpoints (mem_lo_le hA) (mem_le_hi hA)
    have hcosabs : Real.cos |x| = Real.cos x := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, Real.cos_neg]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((cosLo (max |A.lo| |A.hi|) : ℚ) : ℝ) ≤ Real.cos x
      have hq : |(((max |A.lo| |A.hi| : ℚ)) : ℝ)| ≤ 1 := by
        have hq0 : (0 : ℝ) ≤ (((max |A.lo| |A.hi| : ℚ)) : ℝ) := by
          rw [hcast]
          exact le_trans (abs_nonneg ((A.lo : ℚ) : ℝ)) (le_max_left _ _)
        rw [abs_of_nonneg hq0]
        exact hM1
      have hspec := cosLo_le_cos (q := max |A.lo| |A.hi|) hq
      have hdec : Real.cos (((max |A.lo| |A.hi| : ℚ)) : ℝ) ≤ Real.cos |x| :=
        cos_le_cos_of_le_on_unit (abs_nonneg x) hM1 hMmem
      rw [← hcosabs]
      exact le_trans hspec hdec
    · show Real.cos x ≤ ((cosHi 0 : ℚ) : ℝ)
      rw [cosHi_zero, Rat.cast_one]
      exact cos_le_one' x
  · rw [cosI, if_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.cos x
      push_cast
      exact neg_one_le_cos x
    · show Real.cos x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact cos_le_one' x

/-! ## 6. 与 `IExpr.app1` 的接口与读数 -/

/-- 注册示范：`sinI` 作为通用一元节点挂进 `IExpr`（其包含性证明就是 `sinI_mem`）。 -/
theorem sin_as_app1 {n : ℕ} (A : Fin n → RatInterval) (a : IExpr n) :
    (IExpr.app1 sinI Real.sin (fun I y h => sinI_mem (A := I) (x := y) h) a).eval A
      = (a.eval A).map sinI := rfl

theorem cos_as_app1 {n : ℕ} (A : Fin n → RatInterval) (a : IExpr n) :
    (IExpr.app1 cosI Real.cos (fun I y h => cosI_mem (A := I) (x := y) h) a).eval A
      = (a.eval A).map cosI := rfl

/-- 读数：`sin` 在 `q = 1/2` 的点级界（两端都是精确有理数）。 -/
theorem read_sin_bounds_half :
    ((sinLo (1 / 2) : ℚ) : ℝ) ≤ Real.sin ((1 / 2 : ℚ) : ℝ) ∧
      Real.sin ((1 / 2 : ℚ) : ℝ) ≤ ((sinHi (1 / 2) : ℚ) : ℝ) :=
  ⟨sinLo_le_sin (q := 1 / 2) (abs_le_one_of_bounds (by norm_num) (by norm_num)),
   sin_le_sinHi (q := 1 / 2) (abs_le_one_of_bounds (by norm_num) (by norm_num))⟩

/-- 读数：`cos` 在 `q = 1/2` 的点级界。 -/
theorem read_cos_bounds_half :
    ((cosLo (1 / 2) : ℚ) : ℝ) ≤ Real.cos ((1 / 2 : ℚ) : ℝ) ∧
      Real.cos ((1 / 2 : ℚ) : ℝ) ≤ ((cosHi (1 / 2) : ℚ) : ℝ) :=
  ⟨cosLo_le_cos (q := 1 / 2) (abs_le_one_of_bounds (by norm_num) (by norm_num)),
   cos_le_cosHi (q := 1 / 2) (abs_le_one_of_bounds (by norm_num) (by norm_num))⟩

/-- 读数：窗口内 `sinI` 取端点公式。 -/
theorem read_sinI_interval : sinI (intv (1 / 4) (1 / 2)) = ⟨sinLo (1 / 4), sinHi (1 / 2)⟩ := by
  have h : -1 ≤ (intv (1 / 4) (1 / 2)).lo ∧ (intv (1 / 4) (1 / 2)).hi ≤ 1 := by
    constructor
    · show (-1 : ℚ) ≤ 1 / 4; norm_num
    · show (1 : ℚ) / 2 ≤ 1; norm_num
  rw [sinI, if_pos h]
  rfl

/-- 读数：窗口内 `cosI` 的下界取 `|·|` 最大端点（此处 `[1/4,1/2]`，最大绝对值在 `1/2`）。 -/
theorem read_cosI_interval : cosI (intv (1 / 4) (1 / 2)) = ⟨cosLo (1 / 2), cosHi 0⟩ := by
  have h : -1 ≤ (intv (1 / 4) (1 / 2)).lo ∧ (intv (1 / 4) (1 / 2)).hi ≤ 1 := by
    constructor
    · show (-1 : ℚ) ≤ 1 / 4; norm_num
    · show (1 : ℚ) / 2 ≤ 1; norm_num
  rw [cosI, if_pos h]
  simp only [intv]
  congr 1
  norm_num

/-- 读数：窗口外保守回退（`[3,4] ⊄ [-1,1]`）——不猜，退到 `[-1,1]`。 -/
theorem read_sinI_fallback : sinI (intv 3 4) = intv (-1) 1 := by
  have h : ¬ (-1 ≤ (intv 3 4).lo ∧ (intv 3 4).hi ≤ 1) := by
    intro hc
    have hhi : ((intv 3 4).hi : ℚ) = 4 := rfl
    linarith [hc.2]
  rw [sinI, if_neg h]

theorem read_cosI_fallback : cosI (intv 3 4) = intv (-1) 1 := by
  have h : ¬ (-1 ≤ (intv 3 4).lo ∧ (intv 3 4).hi ≤ 1) := by
    intro hc
    have hhi : ((intv 3 4).hi : ℚ) = 4 := rfl
    linarith [hc.2]
  rw [cosI, if_neg h]

/-
  读数（已删除）：对 `sinI_mem` / `cosI_mem` 的**具体点实例化**
  （`Mem (sinI (intv 1/2 1/2)) (sin (1/2))`）在 Lean 4.33.1 下触发 `isDefEq` 心跳耗尽
  （`sinI` 的 `if` 需要在 defeq 检查中展开，叠加 `Mem`→`toSet` 展开），
  即使把局部预算提到 800k 仍超时。因其内容已被 `read_sinI_interval`（窗口支公式）、
  `read_sinI_fallback`（回退支）、`read_sin_bounds_half`（点级规格）与
  `sin_as_app1`（注册）覆盖，故**不作为交付读数**，如实记在这里
  （实现限制，不是数学缺口：一般定理 `sinI_mem` 本身已内核证明）。
-/

end RatInterval

end N11Formalization
