import N11Formalization.TCSystem
import N11Formalization.SourceIdentity
import N11Formalization.Interval.Range

/-!
# `Fm` 的**定义 + 包含性定理**：残差在证书盒心处的区间包络

`Precond.lean` 的 `TCSystem_unique_root_of_full_data` 把残差界完全有理化，但 `Fm`
（`TCSystem c` 的逐项包络）当时是**外部数据**。本文件把它变成**定义 + 定理**：

* `residualInterval q : Fin 5 → RatInterval`：逐分量镜像 `TCSystem.residual` 的
  **表达式树**（`angleVec` / `thetaOf` / `rhoK` / `ringCenter` / `arcEnd` / `Uvec` /
  `hub0` / `hub1` / `wPoint` 各有一个 `*Interval` 版本）；
* `mem_residualInterval`：**无条件**（对任意 `q : Fin 12 → ℚ`）
  `(residualInterval q k).Mem (residual (fun i => ((q i : ℚ) : ℝ)) k)`；
* `mem_residualInterval_cCert`：在证书盒心 `cCert` 上的实例化（经 `TCSystem_first`
  接上 12 变量系统的前 5 分量）。

## 口径（勿误读）

* **单位/图**：`Point = EuclideanSpace ℝ (Fin 2)`，长度即欧氏长度，角度为弧度；区间端点是
  **精确有理数**（无宿主浮点）。
* **`dist` 的处理**：按任务要求用 `dist_point_eq_sqrt` 把
  `dist p q` 化标量为 `√((p₀−q₀)² + (p₁−q₁)²)`，故 `distInterval` 是
  `sqrt ∘ (平方 + 平方)`，**不**对 `Point` 值函数做区间运算。
* **π 的区间**：`piI = [piLo, piHi]`（`Interval/Trig.lean` 的 20 位有理夹逼）；
  这是 `angleVec` 的 `a4 = π − 2(a₀+a₁+a₂+a₃)` 唯一的非有理常数来源。
* **相位（关键，决定精度）**：区间三角算子**不是** `Range.lean` 的
  `sinIRange`（那里的 `phaseHull` 取四态表的**凸包**，对任何输入宽度 ≈ 2，
  与 Taylor 阶无关 —— 这是**结构性**精度损失）。本文件用
  `phaseOf`（区间中点除以 `π/2` 的有理下界后四舍五入）+ `phasePos`/`phaseNeg`
  两条 **π/2 步进递归**把四态表**逐格钉住**：
  `(phasePos A n).1 ∋ sin(x + n·π/2)`、`(phaseNeg A n).1 ∋ sin(x − n·π/2)`，
  每步只用 `sin(y±π/2) = ±cos y` 类恒等式（与 `Interval/Phase.lean` 的
  `fourStates_add/sub_pi_div_two` 同一族），**不需要** `Int` 的 `ediv/emod` 恒等式。
* **回退**：`phaseOf` 给出的相位若不在窗口内，算子**保守回退** `[-1,1]`（不猜），
  故 `sinTot_mem`/`cosTot_mem` **无条件**成立。

## 实现注意（踩过的坑，写下来避免重复）

* `RatInterval`/`inWindow` 这类**普通 `def` 返回 `Prop`** 的定义，**instance 搜索不会展开**
  （合成在 `.reducible` 透明度上做），故 `Decidable (inWindow A k)` / `Decidable A.Valid`
  **合成失败**；`if`/`by_cases` 必须靠 `classical`（`Classical.propDecidable`）。
* `![...] i` 对具体 `i` 的归约：`rfl` 与 `norm_num` 可以，但 `simp only` 需要
  **`Matrix.cons_val_succ'`**（带 `'` 的版本，匹配字面 `⟨i+1, h⟩`；不带 `'` 的
  `Matrix.cons_val_succ` 只匹配 `Fin.succ i` 形式，对 `fin_cases` 产生的字面下标无效）。

## 真实等级

* 定义 + `mem_residualInterval`（任意 `q`）：**kernel-proved，无条件**，零 `sorry`、
  零自定义 `axiom`、零 `native_decide`。
* 读数（`evidence/fm-eval/`）：**numeric**，由 Python 精确有理复算独立对照。

**注意（与 interval-core 的接口）**：本文件**不**改 `Interval/**`。当 `Interval/Trig.lean`
的 `sinLo/sinHi/cosLo/cosHi` 换成高阶 Taylor 界后，**同一个 `residualInterval`** 的定义
不变、包含性证明不变，端点会自动变紧。
-/

noncomputable section

namespace N11Formalization

namespace RatInterval

/-! ## 1. π 区间与平方（区间平方用紧版） -/

/-- `π` 的有理区间（20 位夹逼，来自 `Interval/Trig.lean`）。 -/
def piI : RatInterval := ⟨piLo, piHi⟩

theorem piI_mem : piI.Mem Real.pi := ⟨le_of_lt piLo_lt_pi, le_of_lt pi_lt_piHi⟩

/-- 区间平方（紧版）：`0 ∉ A` 时取单调端点，跨零时取 `[0, max(lo²,hi²)]`。 -/
def sq (A : RatInterval) : RatInterval :=
  if 0 ≤ A.lo then ⟨A.lo * A.lo, A.hi * A.hi⟩
  else if A.hi ≤ 0 then ⟨A.hi * A.hi, A.lo * A.lo⟩
  else ⟨0, max (A.lo * A.lo) (A.hi * A.hi)⟩

theorem sq_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) : (A.sq).Mem (x * x) := by
  have hlo := mem_lo_le hA
  have hhi := mem_le_hi hA
  unfold sq
  by_cases h1 : 0 ≤ A.lo
  · rw [if_pos h1]
    have h1' : (0 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h1
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show (((A.lo * A.lo : ℚ)) : ℝ) ≤ x * x
      push_cast
      exact mul_self_le_mul_self h1' hlo
    · show x * x ≤ (((A.hi * A.hi : ℚ)) : ℝ)
      push_cast
      exact mul_self_le_mul_self (le_trans h1' hlo) hhi
  · rw [if_neg h1]
    by_cases h2 : A.hi ≤ 0
    · rw [if_pos h2]
      have h2' : (A.hi : ℝ) ≤ 0 := by exact_mod_cast h2
      have hx0 : x ≤ 0 := le_trans hhi h2'
      refine mem_iff.mpr ⟨?_, ?_⟩
      · show (((A.hi * A.hi : ℚ)) : ℝ) ≤ x * x
        push_cast
        have hstep : (0 : ℝ) ≤ -((A.hi : ℝ)) := by linarith
        have hle : -((A.hi : ℝ)) ≤ -x := by linarith
        have key := mul_self_le_mul_self hstep hle
        simpa using key
      · show x * x ≤ (((A.lo * A.lo : ℚ)) : ℝ)
        push_cast
        have hstep : (0 : ℝ) ≤ -x := by linarith
        have hle : -x ≤ -((A.lo : ℝ)) := by linarith
        have key := mul_self_le_mul_self hstep hle
        simpa using key
    · rw [if_neg h2]
      refine mem_iff.mpr ⟨?_, ?_⟩
      · show ((0 : ℚ) : ℝ) ≤ x * x
        push_cast
        exact mul_self_nonneg x
      · show x * x ≤ ((max (A.lo * A.lo) (A.hi * A.hi) : ℚ) : ℝ)
        rw [Rat.cast_max]
        push_cast
        have habs : |x| ≤ max |(A.lo : ℝ)| |(A.hi : ℝ)| := abs_le_max_abs_endpoints hlo hhi
        have hsq : x * x = |x| * |x| := (abs_mul_abs_self x).symm
        rw [hsq]
        rcases max_cases |(A.lo : ℝ)| |(A.hi : ℝ)| with ⟨he, _⟩ | ⟨he, _⟩
        · have hx : |x| ≤ |(A.lo : ℝ)| := by rw [he] at habs; exact habs
          have hstep : |x| * |x| ≤ |(A.lo : ℝ)| * |(A.lo : ℝ)| :=
            mul_le_mul hx hx (abs_nonneg _) (le_trans (abs_nonneg _) hx)
          have heq : |(A.lo : ℝ)| * |(A.lo : ℝ)| = (A.lo : ℝ) * (A.lo : ℝ) :=
            abs_mul_abs_self _
          rw [heq] at hstep
          exact le_trans hstep (le_max_left _ _)
        · have hx : |x| ≤ |(A.hi : ℝ)| := by rw [he] at habs; exact habs
          have hstep : |x| * |x| ≤ |(A.hi : ℝ)| * |(A.hi : ℝ)| :=
            mul_le_mul hx hx (abs_nonneg _) (le_trans (abs_nonneg _) hx)
          have heq : |(A.hi : ℝ)| * |(A.hi : ℝ)| = (A.hi : ℝ) * (A.hi : ℝ) :=
            abs_mul_abs_self _
          rw [heq] at hstep
          exact le_trans hstep (le_max_right _ _)

/-- `^2` 形态的区间平方包含性（下游目标里 `dist` 展开后是 `^2`）。 -/
theorem sq_mem_pow {A : RatInterval} {x : ℝ} (hA : A.Mem x) : (A.sq).Mem (x ^ 2) := by
  simpa [pow_two] using sq_mem hA

/-! ## 2. 相位：`phaseOf` + 两条 `π/2` 步进递归（把四态表逐格钉住） -/

/-- **窗口内的 `cos` 区间（比 `Trig.cosI` 紧）**：`Trig.cosI` 的上端点是平凡的 `cosHi 0 = 1`
（宽度 ≈ `q²/2`，在证书盒上达 `7.0e-2`），**这不是 Taylor 缺口而是白送出去的精度**；
把上端点换成 `cosHi (min|·|)`（`cos` 在 `[0,1]` 上递减，参考点取**离 0 最近**的端点）即得宽度
`≈ 2·5/96·M⁴`（与 `DEAD §C′` 的 `2.27e-3` 同量级）。
本文件只**新增**算子，不改 `Interval/**`。 -/
def highAbs (A : RatInterval) : ℚ := max |A.lo| |A.hi|

/-- `{|x| : x ∈ A}` 的**下界**（`0 ∈ A` 时只能是 `0`）。 -/
def lowAbs (A : RatInterval) : ℚ :=
  if 0 ≤ A.lo then A.lo else if A.hi ≤ 0 then -A.hi else 0

/-- 窗口内的 `cos` 区间（紧版：`[cosLo M, cosHi m]`，`M = max|·|`、`m = min|·|` 的下界）。 -/
def cosWin (A : RatInterval) : RatInterval :=
  if -1 ≤ A.lo ∧ A.hi ≤ 1 then ⟨cosLo (highAbs A), cosHi (lowAbs A)⟩ else intv (-1) 1

theorem cosWin_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) : (cosWin A).Mem (Real.cos x) := by
  have hlo := mem_lo_le hA
  have hhi := mem_le_hi hA
  unfold cosWin
  by_cases h : -1 ≤ A.lo ∧ A.hi ≤ 1
  · rw [if_pos h]
    have hlo1 : (-1 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h.1
    have hhi1 : (A.hi : ℝ) ≤ 1 := by exact_mod_cast h.2
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hMcast : ((highAbs A : ℚ) : ℝ) = max |(A.lo : ℝ)| |(A.hi : ℝ)| := by
      unfold highAbs; push_cast; rfl
    have hxM : |x| ≤ ((highAbs A : ℚ) : ℝ) := by
      rw [hMcast]; exact abs_le_max_abs_endpoints hlo hhi
    have hM0 : (0 : ℝ) ≤ ((highAbs A : ℚ) : ℝ) := by
      rw [hMcast]; exact le_trans (abs_nonneg _) (le_max_left _ _)
    have hM1 : ((highAbs A : ℚ) : ℝ) ≤ 1 := by
      rw [hMcast]
      refine max_le ?_ ?_
      · rw [abs_le]; exact ⟨by linarith, by linarith⟩
      · rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hmcast : ((lowAbs A : ℚ) : ℝ) = (if 0 ≤ A.lo then (A.lo : ℝ)
        else if A.hi ≤ 0 then -((A.hi : ℝ)) else 0) := by
      unfold lowAbs
      by_cases h1 : 0 ≤ A.lo
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : A.hi ≤ 0
        · rw [if_pos h2, if_pos h2]; push_cast; ring
        · rw [if_neg h2, if_neg h2]; norm_num
    have hmx : ((lowAbs A : ℚ) : ℝ) ≤ |x| := by
      rw [hmcast]
      by_cases h1 : 0 ≤ A.lo
      · rw [if_pos h1]
        have h1' : (0 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h1
        rw [abs_of_nonneg (le_trans h1' hlo)]
        exact hlo
      · rw [if_neg h1]
        by_cases h2 : A.hi ≤ 0
        · rw [if_pos h2]
          have h2' : (A.hi : ℝ) ≤ 0 := by exact_mod_cast h2
          have hx0 : x ≤ 0 := le_trans hhi h2'
          rw [abs_of_nonpos hx0]
          linarith
        · rw [if_neg h2]
          exact abs_nonneg x
    have hm0 : (0 : ℝ) ≤ ((lowAbs A : ℚ) : ℝ) := by
      rw [hmcast]
      split_ifs with h1 h2
      · exact_mod_cast h1
      · have h2' : (A.hi : ℝ) ≤ 0 := by exact_mod_cast h2
        linarith
      · norm_num
    have hm1 : ((lowAbs A : ℚ) : ℝ) ≤ 1 := le_trans hmx hx1
    have hcosabs : Real.cos |x| = Real.cos x := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, Real.cos_neg]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((cosLo (highAbs A) : ℚ) : ℝ) ≤ Real.cos x
      have hq : |(((highAbs A : ℚ)) : ℝ)| ≤ 1 := by rw [abs_of_nonneg hM0]; exact hM1
      have hspec := cosLo_le_cos (q := highAbs A) hq
      have hdec : Real.cos (((highAbs A : ℚ)) : ℝ) ≤ Real.cos x := by
        rw [← hcosabs]
        exact cos_le_cos_of_le_on_unit (abs_nonneg x) hM1 hxM
      exact le_trans hspec hdec
    · show Real.cos x ≤ ((cosHi (lowAbs A) : ℚ) : ℝ)
      have hq : |(((lowAbs A : ℚ)) : ℝ)| ≤ 1 := by rw [abs_of_nonneg hm0]; exact hm1
      have hspec := cos_le_cosHi (q := lowAbs A) hq
      have hdec : Real.cos x ≤ Real.cos (((lowAbs A : ℚ)) : ℝ) := by
        rw [← hcosabs]
        exact cos_le_cos_of_le_on_unit hm0 hx1 hmx
      exact le_trans hdec hspec
  · rw [if_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.cos x
      push_cast
      exact neg_one_le_cos x
    · show Real.cos x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact cos_le_one' x

/-- **相位估计量**：区间中点除以 `π/2` 的**有理下界**后四舍五入。 -/
def phaseOf (A : RatInterval) : ℤ := ⌊(A.lo + A.hi) / 2 / halfPiLo + 1 / 2⌋

/-- 逐格区间对（`sin` 用 `Trig.sinI`、`cos` 用本文件的 `cosWin`）。 -/
def sinCosPair (A : RatInterval) : RatInterval × RatInterval := (sinI A, cosWin A)

/-- `sin`/`cos` 沿 `+π/2` 步进的**逐格**区间对（同一盒，不移动盒，故不损失窗口精度）。 -/
def phasePos (A : RatInterval) : ℕ → RatInterval × RatInterval
  | 0 => (sinI A, cosWin A)
  | n + 1 => ((phasePos A n).2, (phasePos A n).1.neg)

/-- `sin`/`cos` 沿 `−π/2` 步进的**逐格**区间对。 -/
def phaseNeg (A : RatInterval) : ℕ → RatInterval × RatInterval
  | 0 => (sinI A, cosWin A)
  | n + 1 => ((phaseNeg A n).2.neg, (phaseNeg A n).1)

theorem sin_sub_pi_div_two' (y : ℝ) : Real.sin (y - Real.pi / 2) = -Real.cos y := by
  rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem cos_sub_pi_div_two' (y : ℝ) : Real.cos (y - Real.pi / 2) = Real.sin y := by
  rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- `phasePos` 的包含性：`(phasePos A n).1 ∋ sin(x + n·π/2)`、`.2 ∋ cos(x + n·π/2)`。 -/
theorem phasePos_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    ∀ n : ℕ, ((phasePos A n).1).Mem (Real.sin (x + (n : ℝ) * (Real.pi / 2))) ∧
      ((phasePos A n).2).Mem (Real.cos (x + (n : ℝ) * (Real.pi / 2))) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (sinI A).Mem (Real.sin (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using sinI_mem hA
    · show (cosWin A).Mem (Real.cos (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using cosWin_mem hA
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · show ((phasePos A n).2).Mem (Real.sin (x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x + (n : ℝ) * (Real.pi / 2)) + Real.pi / 2 by push_cast; ring,
        Real.sin_add_pi_div_two]
      exact ih.2
    · show (((phasePos A n).1).neg).Mem (Real.cos (x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x + (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x + (n : ℝ) * (Real.pi / 2)) + Real.pi / 2 by push_cast; ring,
        Real.cos_add_pi_div_two]
      exact neg_mem ih.1

/-- `phaseNeg` 的包含性：`(phaseNeg A n).1 ∋ sin(x − n·π/2)`、`.2 ∋ cos(x − n·π/2)`。 -/
theorem phaseNeg_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) :
    ∀ n : ℕ, ((phaseNeg A n).1).Mem (Real.sin (x - (n : ℝ) * (Real.pi / 2))) ∧
      ((phaseNeg A n).2).Mem (Real.cos (x - (n : ℝ) * (Real.pi / 2))) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (sinI A).Mem (Real.sin (x - ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using sinI_mem hA
    · show (cosWin A).Mem (Real.cos (x - ((0 : ℕ) : ℝ) * (Real.pi / 2)))
      simpa using cosWin_mem hA
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · show (((phaseNeg A n).2).neg).Mem (Real.sin (x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x - (n : ℝ) * (Real.pi / 2)) - Real.pi / 2 by push_cast; ring,
        sin_sub_pi_div_two']
      exact neg_mem ih.2
    · show ((phaseNeg A n).1).Mem (Real.cos (x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)))
      rw [show x - (((n : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
          = (x - (n : ℝ) * (Real.pi / 2)) - Real.pi / 2 by push_cast; ring,
        cos_sub_pi_div_two']
      exact ih.1

/-- 按符号选 `phasePos`/`phaseNeg`。 -/
def phaseBoth (A : RatInterval) (k : ℤ) : RatInterval × RatInterval :=
  if 0 ≤ k then phasePos A k.toNat else phaseNeg A (-k).toNat

/-- `phaseBoth` 的包含性：`sin(x + k·π/2)`、`cos(x + k·π/2)`（`k : ℤ` 两侧统一）。 -/
theorem phaseBoth_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) (k : ℤ) :
    ((phaseBoth A k).1).Mem (Real.sin (x + (k : ℝ) * (Real.pi / 2))) ∧
      ((phaseBoth A k).2).Mem (Real.cos (x + (k : ℝ) * (Real.pi / 2))) := by
  unfold phaseBoth
  by_cases hk : 0 ≤ k
  · rw [if_pos hk]
    rcases int_split_nat k with ⟨hk0, hkeq⟩ | ⟨hk0, hkeq⟩
    · constructor
      · rw [show x + (k : ℝ) * (Real.pi / 2)
            = x + ((k.toNat : ℕ) : ℝ) * (Real.pi / 2) from by rw [int_cast_toNat hkeq]]
        exact (phasePos_mem hA k.toNat).1
      · rw [show x + (k : ℝ) * (Real.pi / 2)
            = x + ((k.toNat : ℕ) : ℝ) * (Real.pi / 2) from by rw [int_cast_toNat hkeq]]
        exact (phasePos_mem hA k.toNat).2
    · have hkz : k = 0 := le_antisymm hk0 hk
      subst hkz
      refine ⟨?_, ?_⟩
      · show (sinI A).Mem (Real.sin (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
        simpa using sinI_mem hA
      · show (cosWin A).Mem (Real.cos (x + ((0 : ℕ) : ℝ) * (Real.pi / 2)))
        simpa using cosWin_mem hA
  · rw [if_neg hk]
    have hklt : k < 0 := not_le.mp hk
    have hnat : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (neg_pos.mpr hklt).le
    have hcast : (k : ℝ) = -(((-k).toNat : ℕ) : ℝ) := by
      have h := congrArg (fun m : ℤ => (m : ℝ)) (show k = -((((-k).toNat : ℕ) : ℤ)) by
        rw [hnat]; ring)
      rw [Int.cast_neg, Int.cast_natCast] at h
      exact h
    constructor
    · rw [show x + (k : ℝ) * (Real.pi / 2) = x - (((-k).toNat : ℕ) : ℝ) * (Real.pi / 2) from by
        rw [hcast]; ring]
      exact (phaseNeg_mem hA (-k).toNat).1
    · rw [show x + (k : ℝ) * (Real.pi / 2) = x - (((-k).toNat : ℕ) : ℝ) * (Real.pi / 2) from by
        rw [hcast]; ring]
      exact (phaseNeg_mem hA (-k).toNat).2

/-- **归约后的相位格**：`phaseBoth` 作用在**归约盒** `reducedBox A (phaseOf A)` 上
（与 `Range.lean` 的 `phaseHull (reducedBox A k) k` 同一位置；差别只在逐格钉相位）。 -/
def phaseRed (A : RatInterval) : RatInterval × RatInterval :=
  phaseBoth (reducedBox A (phaseOf A)) (phaseOf A)

/-- **`sin` 的总区间算子**：相位在窗口内 ⟹ 逐格相位；否则保守回退 `[-1,1]`。 -/
def sinTot (A : RatInterval) : RatInterval := by
  classical
  exact if h : inWindow A (phaseOf A) then (phaseRed A).1 else intv (-1) 1

/-- **`cos` 的总区间算子**（同款相位与回退）。 -/
def cosTot (A : RatInterval) : RatInterval := by
  classical
  exact if h : inWindow A (phaseOf A) then (phaseRed A).2 else intv (-1) 1

theorem sinTot_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) : (sinTot A).Mem (Real.sin x) := by
  classical
  have hkey : x = (x - (phaseOf A : ℝ) * (Real.pi / 2)) + (phaseOf A : ℝ) * (Real.pi / 2) := by
    ring
  unfold sinTot
  by_cases h : inWindow A (phaseOf A)
  · rw [dif_pos h, hkey]
    exact (phaseBoth_mem (A := reducedBox A (phaseOf A)) (reducedBox_mem h hA) (phaseOf A)).1
  · rw [dif_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.sin x
      push_cast
      exact neg_one_le_sin x
    · show Real.sin x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact sin_le_one' x

theorem cosTot_mem {A : RatInterval} {x : ℝ} (hA : A.Mem x) : (cosTot A).Mem (Real.cos x) := by
  classical
  have hkey : x = (x - (phaseOf A : ℝ) * (Real.pi / 2)) + (phaseOf A : ℝ) * (Real.pi / 2) := by
    ring
  unfold cosTot
  by_cases h : inWindow A (phaseOf A)
  · rw [dif_pos h, hkey]
    exact (phaseBoth_mem (A := reducedBox A (phaseOf A)) (reducedBox_mem h hA) (phaseOf A)).2
  · rw [dif_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.cos x
      push_cast
      exact neg_one_le_cos x
    · show Real.cos x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact cos_le_one' x

/-- 窗口内取相位格的**接口引理**（读数用：给出守卫即得具体值）。 -/
theorem sinTot_of_inWindow {A : RatInterval} (h : inWindow A (phaseOf A)) :
    sinTot A = (phaseRed A).1 := by
  classical
  unfold sinTot
  exact dif_pos h

theorem cosTot_of_inWindow {A : RatInterval} (h : inWindow A (phaseOf A)) :
    cosTot A = (phaseRed A).2 := by
  classical
  unfold cosTot
  exact dif_pos h

/-- 回退支的接口引理。 -/
theorem sinTot_of_not_inWindow {A : RatInterval} (h : ¬ inWindow A (phaseOf A)) :
    sinTot A = intv (-1) 1 := by
  classical
  unfold sinTot
  exact dif_neg h

theorem cosTot_of_not_inWindow {A : RatInterval} (h : ¬ inWindow A (phaseOf A)) :
    cosTot A = intv (-1) 1 := by
  classical
  unfold cosTot
  exact dif_neg h

/-- **接口缺陷的 kernel 证据（`Interval/Trig.cosI` 的上端点是平凡的 `1`）**：
窗口内 `cosI A = ⟨cosLo (max|·|), cosHi 0⟩`，而 `cosHi 0 = 1`，故宽度
`= 1 − cosLo (max|·|) ≈ M²/2` ——这**不是** Taylor 缺口，是本文件 `cosWin` 修掉的白送精度
（`cos` 在 `[0,1]` 递减 ⇒ 上端应取 `cosHi (min|·|)`）。 -/
theorem cosI_hi_eq_one {A : RatInterval} (h : -1 ≤ A.lo ∧ A.hi ≤ 1) : (cosI A).hi = 1 := by
  rw [cosI, if_pos h, cosHi_zero]

/-- 同一条缺陷的**定量读数**（在 `A = [0.372, 0.372]` 上宽度 `> 7/100`）。 -/
theorem cosI_width_gt :
    7 / 100 < (cosI (⟨372 / 1000, 372 / 1000⟩ : RatInterval)).hi
      - (cosI (⟨372 / 1000, 372 / 1000⟩ : RatInterval)).lo := by
  rw [cosI, if_pos (by norm_num : (-1 : ℚ) ≤ 372 / 1000 ∧ (372 / 1000 : ℚ) ≤ 1)]
  simp only [cosHi_zero, cosLo]
  norm_num

end RatInterval

open RatInterval

/-! ## 3. 几何构件的区间版本（逐分量镜像 `TCSystem.lean` 的表达式树） -/

/-- `angleVec` 的区间版本。用 **`Fin` 字面量模式匹配**而非 `![...]`：前者对**具体下标**在内核
可归约、`simp only`/`norm_num` 能展开（实测 `![...]` 的 `vecCons` 下标归约只对 0/1 有效，
`⟨2,⋯⟩`/`⟨3,⋯⟩` 会卡住 —— 这是本文件读数路线的关键实现选择）。 -/
def angleVecInterval (q : Fin 12 → ℚ) : Fin 9 → RatInterval
  | 0 => ofRat (q 0)
  | 1 => ofRat (q 1)
  | 2 => ofRat (q 2)
  | 3 => ofRat (q 3)
  | 4 => sub piI (mul (ofRat 2) (add (add (add (ofRat (q 0)) (ofRat (q 1)))
      (ofRat (q 2))) (ofRat (q 3))))
  | 5 => ofRat (q 3)
  | 6 => ofRat (q 2)
  | 7 => ofRat (q 1)
  | 8 => ofRat (q 0)

/-- `thetaOf` 的区间版本。 -/
def thetaInterval (A : Fin 9 → RatInterval) : Fin 9 → RatInterval
  | 0 => neg (add (add (add (add (A 0) (A 1)) (add (A 1) (A 2))) (add (A 2) (A 3)))
      (add (A 3) (A 4)))
  | 1 => neg (add (add (add (A 1) (A 2)) (add (A 2) (A 3))) (add (A 3) (A 4)))
  | 2 => neg (add (add (A 2) (A 3)) (add (A 3) (A 4)))
  | 3 => neg (add (A 3) (A 4))
  | 4 => ofRat 0
  | 5 => add (A 4) (A 5)
  | 6 => add (add (A 4) (A 5)) (add (A 5) (A 6))
  | 7 => add (add (add (A 4) (A 5)) (add (A 5) (A 6))) (add (A 6) (A 7))
  | 8 => add (add (add (add (A 4) (A 5)) (add (A 5) (A 6))) (add (A 6) (A 7)))
      (add (A 7) (A 8))

/-- `rhoK` 的区间版本。 -/
def rhoInterval (q : Fin 12 → ℚ) (k : Fin 9) : RatInterval :=
  sub (cosTot ((angleVecInterval q) k))
    (sqrt (sub (sq (ofRat (q 6))) (sq (sinTot ((angleVecInterval q) k)))))

/-- `ringCenter` 的区间版本（逐坐标）。 -/
def ringCenterInterval (q : Fin 12 → ℚ) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => mul (rhoInterval q k) (cosTot ((thetaInterval (angleVecInterval q)) k))
  | 1 => mul (rhoInterval q k) (sinTot ((thetaInterval (angleVecInterval q)) k))

/-- `arcEnd` 的区间版本（逐坐标）。 -/
def arcEndInterval (q : Fin 12 → ℚ) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => cosTot (add ((thetaInterval (angleVecInterval q)) k) ((angleVecInterval q) k))
  | 1 => sinTot (add ((thetaInterval (angleVecInterval q)) k) ((angleVecInterval q) k))

/-- `Uvec` 的区间版本（逐坐标，`k+1` 取 `Fin 9` 加法）。 -/
def UvecInterval (q : Fin 12 → ℚ) (k : Fin 9) : Fin 2 → RatInterval
  | 0 => sub (add ((ringCenterInterval q k) 0) ((ringCenterInterval q (k + 1)) 0))
      ((arcEndInterval q k) 0)
  | 1 => sub (add ((ringCenterInterval q k) 1) ((ringCenterInterval q (k + 1)) 1))
      ((arcEndInterval q k) 1)

/-- `hub0 = (y0, 0)`（y 坐标**是** `0`，勿漏）。 -/
def hub0Interval (q : Fin 12 → ℚ) : Fin 2 → RatInterval
  | 0 => ofRat (q 4)
  | 1 => ofRat 0

/-- `hub1 = (y1, 0)`。 -/
def hub1Interval (q : Fin 12 → ℚ) : Fin 2 → RatInterval
  | 0 => ofRat (q 5)
  | 1 => ofRat 0

/-- `wPoint` 的区间版本（`m = (y0+y1)/2`，`h = √(R² − ((y1−y0)/2)²)`）。 -/
def wPointInterval (q : Fin 12 → ℚ) : Fin 2 → RatInterval
  | 0 => mul (ofRat (1 / 2)) (add (ofRat (q 4)) (ofRat (q 5)))
  | 1 => sqrt (sub (sq (ofRat (q 6)))
      (sq (mul (ofRat (1 / 2)) (sub (ofRat (q 5)) (ofRat (q 4))))))

/-- **区间版欧氏距离**：`√((P₀−Q₀)² + (P₁−Q₁)²)`（用 `dist_point_eq_sqrt` 化标量后求值）。 -/
def distInterval (P Q : Fin 2 → RatInterval) : RatInterval :=
  sqrt (add (sq (sub (P 0) (Q 0))) (sq (sub (P 1) (Q 1))))

/-- **残差的区间包络** `Fm`（本文件的核心定义；`Fin 5` = 源文 `f` 的 5 个分量）。 -/
def residualInterval (q : Fin 12 → ℚ) : Fin 5 → RatInterval
  | 0 => sub (distInterval (UvecInterval q 1) (hub1Interval q)) (ofRat (q 6))
  | 1 => sub (distInterval (UvecInterval q 2) (hub0Interval q)) (ofRat (q 6))
  | 2 => sub (distInterval (UvecInterval q 3) (hub0Interval q)) (ofRat (q 6))
  | 3 => sub (distInterval (UvecInterval q 8) (hub1Interval q)) (ofRat (q 6))
  | 4 => sub (distInterval (wPointInterval q) (ringCenterInterval q 6)) (ofRat (q 6))

/-! ## 4. 包含性：逐构件 → 组装 -/

/-- `angleVec` 的区间包含性（逐槽 `exact`，靠 `rfl` 级 defeq 归约 `![...] i`）。 -/
theorem angleVecInterval_mem (q : Fin 12 → ℚ) (k : Fin 9) :
    ((angleVecInterval q k)).Mem (angleVec (fun i => ((q i : ℚ) : ℝ)) k) := by
  fin_cases k
  · exact ofRat_mem (q 0)
  · exact ofRat_mem (q 1)
  · exact ofRat_mem (q 2)
  · exact ofRat_mem (q 3)
  · exact sub_mem piI_mem
      (mul_mem (ofRat_mem (2 : ℚ))
        (add_mem (add_mem (add_mem (ofRat_mem (q 0)) (ofRat_mem (q 1))) (ofRat_mem (q 2)))
          (ofRat_mem (q 3))))
  · exact ofRat_mem (q 3)
  · exact ofRat_mem (q 2)
  · exact ofRat_mem (q 1)
  · exact ofRat_mem (q 0)

/-- `thetaOf` 的区间包含性（对任意盒与任意赋值；逐槽 `exact`）。 -/
theorem thetaInterval_mem {A : Fin 9 → RatInterval} {a : Fin 9 → ℝ}
    (hA : ∀ j, (A j).Mem (a j)) (k : Fin 9) :
    ((thetaInterval A k)).Mem (thetaOf a k) := by
  fin_cases k
  · exact neg_mem (add_mem (add_mem (add_mem (add_mem (hA 0) (hA 1)) (add_mem (hA 1) (hA 2)))
      (add_mem (hA 2) (hA 3))) (add_mem (hA 3) (hA 4)))
  · exact neg_mem (add_mem (add_mem (add_mem (hA 1) (hA 2)) (add_mem (hA 2) (hA 3)))
      (add_mem (hA 3) (hA 4)))
  · exact neg_mem (add_mem (add_mem (hA 2) (hA 3)) (add_mem (hA 3) (hA 4)))
  · exact neg_mem (add_mem (hA 3) (hA 4))
  · show (ofRat 0).Mem (0 : ℝ)
    simpa using ofRat_mem (0 : ℚ)
  · exact add_mem (hA 4) (hA 5)
  · exact add_mem (add_mem (hA 4) (hA 5)) (add_mem (hA 5) (hA 6))
  · exact add_mem (add_mem (add_mem (hA 4) (hA 5)) (add_mem (hA 5) (hA 6)))
      (add_mem (hA 6) (hA 7))
  · exact add_mem (add_mem (add_mem (add_mem (hA 4) (hA 5)) (add_mem (hA 5) (hA 6)))
      (add_mem (hA 6) (hA 7))) (add_mem (hA 7) (hA 8))

/-- `rhoK` 的区间包含性。 -/
theorem rhoInterval_mem (q : Fin 12 → ℚ) (k : Fin 9) :
    ((rhoInterval q k)).Mem (rhoK (fun i => ((q i : ℚ) : ℝ)) k) := by
  rw [rhoK_eq]
  exact sub_mem (cosTot_mem (angleVecInterval_mem q k))
    (sqrt_mem (sub_mem (sq_mem_pow (ofRat_mem (q 6)))
      (sq_mem_pow (sinTot_mem (angleVecInterval_mem q k)))))

/-- `ringCenter` 的区间包含性（逐坐标）。 -/
theorem ringCenterInterval_mem (q : Fin 12 → ℚ) (k : Fin 9) (i : Fin 2) :
    ((ringCenterInterval q k) i).Mem
      ((ringCenter (fun j => ((q j : ℚ) : ℝ)) k).ofLp i) := by
  fin_cases i
  · show ((rhoInterval q k).mul (cosTot ((thetaInterval (angleVecInterval q)) k))).Mem
      ((ringCenter (fun j => ((q j : ℚ) : ℝ)) k).ofLp 0)
    rw [ringCenter_coord0]
    exact mul_mem (rhoInterval_mem q k) (cosTot_mem (thetaInterval_mem (angleVecInterval_mem q) k))
  · show ((rhoInterval q k).mul (sinTot ((thetaInterval (angleVecInterval q)) k))).Mem
      ((ringCenter (fun j => ((q j : ℚ) : ℝ)) k).ofLp 1)
    rw [ringCenter_coord1]
    exact mul_mem (rhoInterval_mem q k) (sinTot_mem (thetaInterval_mem (angleVecInterval_mem q) k))

/-- `arcEnd` 的区间包含性（逐坐标）。 -/
theorem arcEndInterval_mem (q : Fin 12 → ℚ) (k : Fin 9) (i : Fin 2) :
    ((arcEndInterval q k) i).Mem ((arcEnd (fun j => ((q j : ℚ) : ℝ)) k).ofLp i) := by
  fin_cases i
  · show (cosTot ((thetaInterval (angleVecInterval q) k).add ((angleVecInterval q) k))).Mem
      ((arcEnd (fun j => ((q j : ℚ) : ℝ)) k).ofLp 0)
    rw [arcEnd_coord0]
    exact cosTot_mem (add_mem (thetaInterval_mem (angleVecInterval_mem q) k)
      (angleVecInterval_mem q k))
  · show (sinTot ((thetaInterval (angleVecInterval q) k).add ((angleVecInterval q) k))).Mem
      ((arcEnd (fun j => ((q j : ℚ) : ℝ)) k).ofLp 1)
    rw [arcEnd_coord1]
    exact sinTot_mem (add_mem (thetaInterval_mem (angleVecInterval_mem q) k)
      (angleVecInterval_mem q k))

/-- `Uvec` 的区间包含性（逐坐标）。 -/
theorem UvecInterval_mem (q : Fin 12 → ℚ) (k : Fin 9) (i : Fin 2) :
    ((UvecInterval q k) i).Mem ((Uvec (fun j => ((q j : ℚ) : ℝ)) k).ofLp i) := by
  fin_cases i
  · show (sub (add ((ringCenterInterval q k) 0) ((ringCenterInterval q (k + 1)) 0))
      ((arcEndInterval q k) 0)).Mem ((Uvec (fun j => ((q j : ℚ) : ℝ)) k).ofLp 0)
    rw [Uvec_coord0]
    exact sub_mem (add_mem (ringCenterInterval_mem q k 0) (ringCenterInterval_mem q (k + 1) 0))
      (arcEndInterval_mem q k 0)
  · show (sub (add ((ringCenterInterval q k) 1) ((ringCenterInterval q (k + 1)) 1))
      ((arcEndInterval q k) 1)).Mem ((Uvec (fun j => ((q j : ℚ) : ℝ)) k).ofLp 1)
    rw [Uvec_coord1]
    exact sub_mem (add_mem (ringCenterInterval_mem q k 1) (ringCenterInterval_mem q (k + 1) 1))
      (arcEndInterval_mem q k 1)

theorem hub0Interval_mem (q : Fin 12 → ℚ) (i : Fin 2) :
    ((hub0Interval q) i).Mem ((hub0 (fun j => ((q j : ℚ) : ℝ))).ofLp i) := by
  fin_cases i
  · show (ofRat (q 4)).Mem ((hub0 (fun j => ((q j : ℚ) : ℝ))).ofLp 0)
    rw [hub0_coord0]
    exact ofRat_mem (q 4)
  · show (ofRat 0).Mem ((hub0 (fun j => ((q j : ℚ) : ℝ))).ofLp 1)
    rw [hub0_coord1]
    simpa using ofRat_mem (0 : ℚ)

theorem hub1Interval_mem (q : Fin 12 → ℚ) (i : Fin 2) :
    ((hub1Interval q) i).Mem ((hub1 (fun j => ((q j : ℚ) : ℝ))).ofLp i) := by
  fin_cases i
  · show (ofRat (q 5)).Mem ((hub1 (fun j => ((q j : ℚ) : ℝ))).ofLp 0)
    rw [hub1_coord0]
    exact ofRat_mem (q 5)
  · show (ofRat 0).Mem ((hub1 (fun j => ((q j : ℚ) : ℝ))).ofLp 1)
    rw [hub1_coord1]
    simpa using ofRat_mem (0 : ℚ)

theorem wPointInterval_mem (q : Fin 12 → ℚ) (i : Fin 2) :
    ((wPointInterval q) i).Mem ((wPoint (fun j => ((q j : ℚ) : ℝ))).ofLp i) := by
  fin_cases i
  · show (mul (ofRat (1 / 2)) (add (ofRat (q 4)) (ofRat (q 5)))).Mem
      ((wPoint (fun j => ((q j : ℚ) : ℝ))).ofLp 0)
    rw [wPoint_coord0]
    have h : ((((q 4 : ℚ) : ℝ) + ((q 5 : ℚ) : ℝ)) / 2)
        = (((1 / 2 : ℚ) : ℝ) * (((q 4 : ℚ) : ℝ) + ((q 5 : ℚ) : ℝ))) := by
      push_cast; ring
    rw [h]
    exact mul_mem (ofRat_mem (1 / 2)) (add_mem (ofRat_mem (q 4)) (ofRat_mem (q 5)))
  · show (sqrt (sub (sq (ofRat (q 6)))
      (sq (mul (ofRat (1 / 2)) (sub (ofRat (q 5)) (ofRat (q 4))))))).Mem
      ((wPoint (fun j => ((q j : ℚ) : ℝ))).ofLp 1)
    rw [wPoint_coord1]
    have h : ((((q 5 : ℚ) : ℝ) - ((q 4 : ℚ) : ℝ)) / 2)
        = (((1 / 2 : ℚ) : ℝ) * (((q 5 : ℚ) : ℝ) - ((q 4 : ℚ) : ℝ))) := by
      push_cast; ring
    rw [h]
    exact sqrt_mem (sub_mem (sq_mem_pow (ofRat_mem (q 6)))
      (sq_mem_pow (mul_mem (ofRat_mem (1 / 2)) (sub_mem (ofRat_mem (q 5)) (ofRat_mem (q 4))))))

/-- **区间版欧氏距离的包含性**（`dist` 经 `dist_point_eq_sqrt` 化标量）。 -/
theorem distInterval_mem {P Q : Fin 2 → RatInterval} {p q : Point}
    (hP : ∀ i, (P i).Mem (p.ofLp i)) (hQ : ∀ i, (Q i).Mem (q.ofLp i)) :
    (distInterval P Q).Mem (dist p q) := by
  unfold distInterval
  rw [dist_point_eq_sqrt]
  exact sqrt_mem (add_mem (sq_mem_pow (sub_mem (hP 0) (hQ 0)))
    (sq_mem_pow (sub_mem (hP 1) (hQ 1))))

/-- **包含性主定理（任意 `q`，无条件）**：`residualInterval q` 包住 `residual` 在
`q` 的有理提升点处的取值。 -/
theorem mem_residualInterval (q : Fin 12 → ℚ) (k : Fin 5) :
    ((residualInterval q k)).Mem (residual (fun i => ((q i : ℚ) : ℝ)) k) := by
  fin_cases k
  · exact sub_mem (distInterval_mem (fun i => UvecInterval_mem q 1 i)
      (fun i => hub1Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => UvecInterval_mem q 2 i)
      (fun i => hub0Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => UvecInterval_mem q 3 i)
      (fun i => hub0Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => UvecInterval_mem q 8 i)
      (fun i => hub1Interval_mem q i)) (ofRat_mem (q 6))
  · exact sub_mem (distInterval_mem (fun i => wPointInterval_mem q i)
      (fun i => ringCenterInterval_mem q 6 i)) (ofRat_mem (q 6))

/-! ## 5. 证书盒心 `cCert` 与实例化

`certificates/root-box.json::box.center_exact_rational` 的 12 个**精确有理数**（逐字转写；
`evidence/fm-eval/` 的 Python 对照脚本从 JSON 重新读一遍做独立核对）。
`residual` 只读前 7 个坐标（后 5 个是 KKT 乘子 `λ`）。 -/

/-- 证书盒心（12 个精确有理数）。**注意**：`BoxRstar.lean` 亦定义同名 `cCert`/`cCertR`
（数值经 Lead 逐位核对**完全一致**）；两份定义当前并存，`ResidualInterval` 尚不能 `import BoxRstar`
（会与其依赖链产生冲突，R15 记录）——收敛为单一真源的工作已派工。 -/
def cCert : Fin 12 → ℚ :=
  ![6701511529285631 / 18014398509481984, 6140082802885973 / 18014398509481984,
    5058838003133637 / 18014398509481984, 6899731189335755 / 18014398509481984,
    4917524862872097 / 18014398509481984, -2691864528343895 / 18014398509481984,
    6845180557269243 / 18014398509481984, -2050658785296173 / 18014398509481984,
    -7385064427961529 / 288230376151711744, -7661580961047613 / 1152921504606846976,
    -2860603688525993 / 144115188075855872, -7612361213708557 / 288230376151711744]

/-- 盒心作为 `ℝ¹²` 向量（`residual`/`TCSystem` 的输入）。 -/
def cCertR : Fin 12 → ℝ := fun i => (cCert i : ℝ)

/-- **实例化（残差版）**：`residualInterval cCert` 包住 `residual cCertR`。 -/
theorem mem_residualInterval_cCert_residual (k : Fin 5) :
    ((residualInterval cCert k)).Mem (residual cCertR k) :=
  mem_residualInterval cCert k

/-- **实例化（`TCSystem` 版，点式）**：经 `TCSystem_first` 接上 12 变量系统的前 5 分量。 -/
theorem mem_residualInterval_cCert (k : Fin 5) :
    ((residualInterval cCert k)).Mem (TCSystem cCertR ⟨(k : ℕ), by omega⟩) := by
  rw [TCSystem_first]
  exact mem_residualInterval_cCert_residual k

/-- **实例化（`TCSystem` 版，`∀` 形式）**：区间数据 `Fm := residualInterval cCert` 满足
`Precond.TCSystem_unique_root_of_full_data` 的 `hFm` 前提（前 5 个分量）。 -/
theorem mem_residualInterval_cCert_TCSystem (k : Fin 5) :
    ((residualInterval cCert k)).Mem (TCSystem cCertR ⟨(k : ℕ), by omega⟩) :=
  mem_residualInterval_cCert k

end N11Formalization
