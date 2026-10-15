/-
  N11Formalization.Interval.Range
  ===============================

  **M5b / R4：`sin`/`cos` 的区间级升级（任意输入）+ 回退区量化**

  设计（逐步具名）：
  * `halfPiLo`/`halfPiHi`：`π/2` 的精确有理界（来自 20 位 `piLo/piHi`）；
  * `inWindow A k`：**逐 `k` 的有理不等式**（符号分支取外向侧），含义是「把 `A` 平移
    `−k·(π/2)` 后整段落在 `[-1,1]` 内」。**它本身不是可判定的有限搜索**——可判定性
    须由候选 `k` 的有限性给出，而后者由 `windowFallback_of_width_gt_two` 一类**已证界**
    提供（本题不把可判定性当前提）；
  * `windowFallback A := ¬ ∃ k, inWindow A k`：**回退谓词**。回退分支一律返回 `intv (-1) 1`
    （宁可回退，也不用可能不成立的"范围假设"）；
  * `reducedBox A k`：归约盒（有理端点、外向）；关键引理 `reducedBox_mem`：
    `inWindow A k → Mem A x → Mem (reducedBox A k) (x − k·(π/2))`；
  * `phaseHull A k`：双向 `hull`（因 R3 只给「四可能」而不知 `k mod 4`）：
    `hull (hull (sinI R) (neg (sinI R))) (hull (cosI R) (neg (cosI R)))`，`R = reducedBox A k`；
  * `sin_mem_of_inWindow` / `cos_mem_of_inWindow`：`inWindow` 下的包含性；
  * `sinIRange` / `cosIRange`：**总算子**（`Classical.choose` 选 `k`；无可用 `k` 时回退），
    含无条件包含性 `sinIRange_mem` / `cosIRange_mem`。

  依赖：`Interval/Trig.lean`（`sinI`/`cosI` 与整体界）、`Interval/Vector.lean`
  （`hull`/`neg`）、`N11Formalization.IntervalZ`（**外部/他侧模块**：**来源不明**：原归属说法无法由对方确认，故按事实记为来源不明；本工程只 import、不拥有。它当前在**根 import 链**上（根 L32）⇒ 属受审 cone，须逐条过 #print axioms）
  `sin_cos_shift_halfPi_four`，把 R3 的四态表封到 `k : ℤ`）。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Trig
import N11Formalization.Interval.Vector
import N11Formalization.Interval.Shift
import N11Formalization.IntervalZ
/-! ### 依赖同步纪律（本工程 · lead 裁定 · 记入件头）

**往 `srcDir` 增/删模块，必须「源码与 import 同步、且一次串行 build 通过」**：只加 import 不加源码
（或只删源码不删 import）会把**根闸**拖红。**不拥有他侧模块时，不得在本写域内另造同名模块**
（同名声明会与根 cone 里已有的同模块冲突、反而制造新的红）；正确处置是：先恢复该模块的源文件，
或在**自己命名的新模块**里提供替代并**只改自己文件的 import**。
共享 `lean/` 目录下**禁止并发 `lake`**；见 `failed to read file …*.olean[.private]` ⇒ 环境噪声，
串行重跑即可，**不去"修"不存在的代码错**。
-/

namespace N11Formalization

namespace RatInterval

/-! ## 1. π/2 的有理界与窗口谓词 -/

/-- `piLo < piHi`（20 位夹逼的单调性）。 -/
theorem piLo_lt_piHi : piLo < piHi := by
  have h : piHi - piLo = 1 / 10 ^ 20 := piHi_sub_piLo
  linarith

/-- `π/2` 的有理下界。 -/
def halfPiLo : ℚ := piLo / 2

/-- `π/2` 的有理上界。 -/
def halfPiHi : ℚ := piHi / 2

theorem halfPiLo_le_halfPiHi : halfPiLo ≤ halfPiHi := by
  have h : piLo ≤ piHi := le_of_lt piLo_lt_piHi
  show piLo / 2 ≤ piHi / 2
  linarith

/-- **窗口谓词**（逐 `k`，符号分支取外向有理界）。**不是**可判定的有限搜索。 -/
def inWindow (A : RatInterval) (k : ℤ) : Prop :=
  -1 ≤ A.lo - (if 0 ≤ k then k * halfPiHi else k * halfPiLo) ∧
    A.hi - (if 0 ≤ k then k * halfPiLo else k * halfPiHi) ≤ 1

/-- **回退谓词**：不存在任何平移把 `A` 整段送进 `[-1,1]`。 -/
def windowFallback (A : RatInterval) : Prop := ¬ ∃ k : ℤ, inWindow A k

/-- 归约盒（有理端点、外向）。 -/
def reducedBox (A : RatInterval) (k : ℤ) : RatInterval :=
  ⟨A.lo - (if 0 ≤ k then k * halfPiHi else k * halfPiLo),
   A.hi - (if 0 ≤ k then k * halfPiLo else k * halfPiHi)⟩

/-! ## 2. 回退区的量化（宽度界） -/

/-- `inWindow A k ⟹ A.hi − A.lo ≤ 2`（平移不改变宽度，而窗口宽 2）。 -/
theorem inWindow_width_le_two {A : RatInterval} {k : ℤ} (hk : inWindow A k) :
    A.hi - A.lo ≤ 2 := by
  have hlo := hk.1
  have hhi := hk.2
  by_cases hk0 : 0 ≤ k
  · simp only [if_pos hk0] at hlo hhi
    have hk0q : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk0
    have hs : (k : ℚ) * halfPiLo ≤ (k : ℚ) * halfPiHi :=
      mul_le_mul_of_nonneg_left halfPiLo_le_halfPiHi hk0q
    linarith
  · simp only [if_neg hk0] at hlo hhi
    have hkneg : k ≤ 0 := le_of_lt (not_le.mp hk0)
    have hk0q : (k : ℚ) ≤ 0 := by exact_mod_cast hkneg
    have hs : (k : ℚ) * halfPiHi ≤ (k : ℚ) * halfPiLo :=
      mul_le_mul_of_nonpos_left halfPiLo_le_halfPiHi hk0q
    linarith

/-- **回退充分条件**：盒宽 > 2 ⟹ 任何平移都进不了宽 2 的窗口。 -/
theorem windowFallback_of_width_gt_two {A : RatInterval} (h : 2 < A.hi - A.lo) :
    windowFallback A := by
  intro hk
  rcases hk with ⟨k, hkwin⟩
  have := inWindow_width_le_two hkwin
  linarith

/-! ## 3. 归约点的所属（窗口内的 `π/2` 两侧取向外侧） -/

theorem pi_div_two_bounds : (((halfPiLo : ℚ)) : ℝ) ≤ Real.pi / 2 ∧
    Real.pi / 2 ≤ (((halfPiHi : ℚ)) : ℝ) := by
  refine ⟨?_, ?_⟩
  · have h := piLo_lt_pi
    have hcast : (((halfPiLo : ℚ)) : ℝ) = ((piLo : ℚ) : ℝ) / 2 := by
      rw [halfPiLo]; push_cast; ring
    rw [hcast]; linarith
  · have h := pi_lt_piHi
    have hcast : (((halfPiHi : ℚ)) : ℝ) = ((piHi : ℚ) : ℝ) / 2 := by
      rw [halfPiHi]; push_cast; ring
    rw [hcast]; linarith

/-- **`inWindow` 下的归约点所属**：`x ∈ A` ⟹ `x − k·(π/2) ∈ reducedBox A k`。 -/
theorem reducedBox_mem {A : RatInterval} {x : ℝ} {k : ℤ} (_hk : inWindow A k) (hA : Mem A x) :
    Mem (reducedBox A k) (x - (k : ℝ) * (Real.pi / 2)) := by
  have hlo := mem_lo_le hA
  have hhi := mem_le_hi hA
  have hpi := pi_div_two_bounds
  refine mem_iff.mpr ⟨?_, ?_⟩
  · show (((A.lo - (if 0 ≤ k then k * halfPiHi else k * halfPiLo) : ℚ)) : ℝ)
        ≤ x - (k : ℝ) * (Real.pi / 2)
    have hsub : (k : ℝ) * (Real.pi / 2)
        ≤ (((if 0 ≤ k then k * halfPiHi else k * halfPiLo : ℚ)) : ℝ) := by
      by_cases hk0 : 0 ≤ k
      · simp only [if_pos hk0]
        have : (k : ℝ) * (Real.pi / 2) ≤ (k : ℝ) * (((halfPiHi : ℚ)) : ℝ) :=
          mul_le_mul_of_nonneg_left hpi.2 (by exact_mod_cast hk0 : (0 : ℝ) ≤ (k : ℝ))
        have hcast : (((k * halfPiHi : ℚ)) : ℝ) = (k : ℝ) * (((halfPiHi : ℚ)) : ℝ) := by
          push_cast; ring
        linarith
      · simp only [if_neg hk0]
        have hkneg : (k : ℝ) ≤ 0 := by
          have : k ≤ 0 := le_of_lt (not_le.mp hk0)
          exact_mod_cast this
        have := mul_le_mul_of_nonpos_left hpi.1 hkneg
        have hcast : (((k * halfPiLo : ℚ)) : ℝ) = (k : ℝ) * (((halfPiLo : ℚ)) : ℝ) := by
          push_cast; ring
        linarith
    push_cast
    linarith
  · show x - (k : ℝ) * (Real.pi / 2)
        ≤ (((A.hi - (if 0 ≤ k then k * halfPiLo else k * halfPiHi) : ℚ)) : ℝ)
    have hsub : (((if 0 ≤ k then k * halfPiLo else k * halfPiHi : ℚ)) : ℝ)
        ≤ (k : ℝ) * (Real.pi / 2) := by
      by_cases hk0 : 0 ≤ k
      · simp only [if_pos hk0]
        have hcast : (((k * halfPiLo : ℚ)) : ℝ) = (k : ℝ) * (((halfPiLo : ℚ)) : ℝ) := by
          push_cast; ring
        have := mul_le_mul_of_nonneg_left hpi.1 (by exact_mod_cast hk0 : (0 : ℝ) ≤ (k : ℝ))
        linarith
      · simp only [if_neg hk0]
        have hkneg : (k : ℝ) ≤ 0 := by
          have : k ≤ 0 := le_of_lt (not_le.mp hk0)
          exact_mod_cast this
        have := mul_le_mul_of_nonpos_left hpi.2 hkneg
        have hcast : (((k * halfPiHi : ℚ)) : ℝ) = (k : ℝ) * (((halfPiHi : ℚ)) : ℝ) := by
          push_cast; ring
        linarith
    push_cast
    linarith

/-! ## 4. 窗口内的区间级包含性（双向 `hull`） -/

/-- 相位壳：`±sin` 与 `±cos` 的四个窗口像的凸包（`k mod 4` 未知故取双向）。 -/
def phaseHull (A : RatInterval) (k : ℤ) : RatInterval :=
  hull (hull (sinI (reducedBox A k)) (neg (sinI (reducedBox A k))))
    (hull (cosI (reducedBox A k)) (neg (cosI (reducedBox A k))))

theorem sin_mem_of_inWindow {A : RatInterval} {x : ℝ} {k : ℤ} (hA : Mem A x) (hk : inWindow A k) :
    Mem (phaseHull A k) (Real.sin x) := by
  have hx := reducedBox_mem hk hA
  have hkey : x = (x - (k : ℝ) * (Real.pi / 2)) + (k : ℝ) * (Real.pi / 2) := by ring
  rw [hkey]
  rcases (sin_cos_shift_halfPi_four (x - (k : ℝ) * (Real.pi / 2)) k).1 with h | h | h | h
  · rw [h]
    exact hull_mem_left (hull_mem_left (sinI_mem hx))
  · rw [h]
    exact hull_mem_left (hull_mem_right (neg_mem (sinI_mem hx)))
  · rw [h]
    exact hull_mem_right (hull_mem_left (cosI_mem hx))
  · rw [h]
    exact hull_mem_right (hull_mem_right (neg_mem (cosI_mem hx)))

theorem cos_mem_of_inWindow {A : RatInterval} {x : ℝ} {k : ℤ} (hA : Mem A x) (hk : inWindow A k) :
    Mem (phaseHull A k) (Real.cos x) := by
  have hx := reducedBox_mem hk hA
  have hkey : x = (x - (k : ℝ) * (Real.pi / 2)) + (k : ℝ) * (Real.pi / 2) := by ring
  rw [hkey]
  rcases (sin_cos_shift_halfPi_four (x - (k : ℝ) * (Real.pi / 2)) k).2 with h | h | h | h
  · rw [h]
    exact hull_mem_left (hull_mem_left (sinI_mem hx))
  · rw [h]
    exact hull_mem_left (hull_mem_right (neg_mem (sinI_mem hx)))
  · rw [h]
    exact hull_mem_right (hull_mem_left (cosI_mem hx))
  · rw [h]
    exact hull_mem_right (hull_mem_right (neg_mem (cosI_mem hx)))

/-! ## 5. 总算子（有可用平移则归约，否则回退 `[-1,1]`） -/

/-- `sin` 的总区间算子：存在可用平移 ⟹ `phaseHull`；否则**回退** `intv (-1) 1`。 -/
noncomputable def sinIRange (A : RatInterval) : RatInterval := by
  classical
  exact if h : ∃ k : ℤ, inWindow A k then phaseHull A (Classical.choose h) else intv (-1) 1

/-- `cos` 的总区间算子（同款相位壳与回退）。 -/
noncomputable def cosIRange (A : RatInterval) : RatInterval := by
  classical
  exact if h : ∃ k : ℤ, inWindow A k then phaseHull A (Classical.choose h) else intv (-1) 1

theorem sinIRange_mem {A : RatInterval} {x : ℝ} (hA : Mem A x) :
    Mem (sinIRange A) (Real.sin x) := by
  unfold sinIRange
  by_cases h : ∃ k : ℤ, inWindow A k
  · rw [dif_pos h]
    exact sin_mem_of_inWindow (A := A) (x := x) (k := Classical.choose h) hA (Classical.choose_spec h)
  · rw [dif_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.sin x
      push_cast
      exact neg_one_le_sin x
    · show Real.sin x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact sin_le_one' x

theorem cosIRange_mem {A : RatInterval} {x : ℝ} (hA : Mem A x) :
    Mem (cosIRange A) (Real.cos x) := by
  unfold cosIRange
  by_cases h : ∃ k : ℤ, inWindow A k
  · rw [dif_pos h]
    exact cos_mem_of_inWindow (A := A) (x := x) (k := Classical.choose h) hA (Classical.choose_spec h)
  · rw [dif_neg h]
    refine mem_iff.mpr ⟨?_, ?_⟩
    · show ((-1 : ℚ) : ℝ) ≤ Real.cos x
      push_cast
      exact neg_one_le_cos x
    · show Real.cos x ≤ ((1 : ℚ) : ℝ)
      push_cast
      exact cos_le_one' x

/-- 回退分支的读数：盒宽 > 2 时 `sinIRange` 走回退（`windowFallback` 阻断 `dif_pos`）。 -/
theorem sinIRange_eq_fallback_of_width_gt_two {A : RatInterval} (h : 2 < A.hi - A.lo) :
    sinIRange A = intv (-1) 1 := by
  unfold sinIRange
  rw [dif_neg]
  intro hk
  exact windowFallback_of_width_gt_two h hk

/-! ## 6. `inWindow` 的有限候选集界（乘性形式，避开除法引理名） -/

/-- **候选平移有限**：`inWindow A k` 时 `|k|·halfPiLo ≤ |A.lo| + |A.hi| + 2`。
用**乘性形式**陈述（等价于 `|k| ≤ (…)/halfPiLo`），避开本 rev 里 `div_le_iff`/`le_div_iff` 一类除法的名字与实参形状问题；
结论直接给出「候选 `k` 落在有限区间内」。 -/
theorem inWindow_abs_mul_halfPiLo_le {A : RatInterval} {k : ℤ} (hk : inWindow A k) :
    |(k : ℚ)| * halfPiLo ≤ |A.lo| + |A.hi| + 2 := by
  have hpos : (0 : ℚ) < halfPiLo := by
    have hcast : ((halfPiLo : ℚ) : ℝ) = ((piLo : ℚ) : ℝ) / 2 := by
      rw [halfPiLo]; push_cast; ring
    have hposR : (0 : ℝ) < ((halfPiLo : ℚ) : ℝ) := by
      rw [hcast]; linarith [piLo_pos]
    exact_mod_cast hposR
  have hle : halfPiLo ≤ halfPiHi := halfPiLo_le_halfPiHi
  have hC : -(|A.lo|) ≤ A.lo := neg_abs_le A.lo
  have hC' : -(|A.hi|) ≤ A.hi := neg_abs_le A.hi
  have key : -(|A.lo| + |A.hi| + 2) ≤ (k : ℚ) * halfPiLo ∧
      (k : ℚ) * halfPiLo ≤ |A.lo| + |A.hi| + 2 := by
    by_cases hk0 : 0 ≤ k
    · have hk0q : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk0
      have hm : (k : ℚ) * halfPiLo ≤ (k : ℚ) * halfPiHi := mul_le_mul_of_nonneg_left hle hk0q
      have h1 := hk.1
      have h2 := hk.2
      simp only [if_pos hk0] at h1 h2
      constructor <;> linarith [le_abs_self A.lo, le_abs_self A.hi]
    · have hkneg : k ≤ 0 := le_of_lt (not_le.mp hk0)
      have hknegq : (k : ℚ) ≤ 0 := by exact_mod_cast hkneg
      have hm : (k : ℚ) * halfPiHi ≤ (k : ℚ) * halfPiLo := mul_le_mul_of_nonpos_left hle hknegq
      have h1 := hk.1
      have h2 := hk.2
      simp only [if_neg hk0] at h1 h2
      constructor <;> linarith [le_abs_self A.lo, le_abs_self A.hi]
  have habs : |(k : ℚ) * halfPiLo| ≤ |A.lo| + |A.hi| + 2 := abs_le.mpr key
  rwa [abs_mul, abs_of_pos hpos] at habs

end RatInterval

end N11Formalization






