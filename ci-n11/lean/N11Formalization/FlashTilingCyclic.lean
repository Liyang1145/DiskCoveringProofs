import Mathlib
import N11Formalization.FlashTilingFan

/-!
# FlashTilingCyclic —— 具体环（Fin 9 / Fin 5 / Fin 6）上的循环结构与子多边形凸性

flash-tiling 写域。给 `FlashTilingFan.fan_dart` 提供具体实例所需的四条结构事实
（`s (s' i) = i`、无不动点、无 2 环、无 3 环）与 `SumClosed`，以及两个子多边形
（H0 侧五边形 `qA`、H1 侧六边形 `qB`）的 `RingConvex`（后者由环的 `RingConvex` 加**闭合弦边**
条件导出，弦边条件作为可付前提）。

无 sorry / 自定义 axiom / native_decide。
-/

namespace N11Formalization.FlashTiling

open N11Formalization

/-- `Fin 9` 上的环形后继（= `i + 1`）。 -/
def succ9 (i : Fin 9) : Fin 9 := i + 1
/-- `Fin 9` 上的环形前驱（= `i - 1`）。 -/
def pred9 (i : Fin 9) : Fin 9 := i - 1
/-- `Fin 5` 上的环形后继。 -/
def succ5 (i : Fin 5) : Fin 5 := i + 1
/-- `Fin 5` 上的环形前驱。 -/
def pred5 (i : Fin 5) : Fin 5 := i - 1
/-- `Fin 6` 上的环形后继。 -/
def succ6 (i : Fin 6) : Fin 6 := i + 1
/-- `Fin 6` 上的环形前驱。 -/
def pred6 (i : Fin 6) : Fin 6 := i - 1

/-- `det2 u 0 = 0`（本文件自用；`det2` 定义在 `FlashTilingFan`）。 -/
theorem det2_zero_right (u : Point) : det2 u 0 = 0 := by
  simp only [det2]
  simp

theorem succ9_pred9 : ∀ i : Fin 9, succ9 (pred9 i) = i := by
  intro i; fin_cases i <;> decide
theorem pred9_succ9 : ∀ i : Fin 9, pred9 (succ9 i) = i := by
  intro i; fin_cases i <;> decide
theorem succ9_ne : ∀ i : Fin 9, succ9 i ≠ i := by
  intro i; fin_cases i <;> decide
theorem succ9_ne_pred9 : ∀ i : Fin 9, succ9 i ≠ pred9 i := by
  intro i; fin_cases i <;> decide
theorem succ9_succ9_ne : ∀ i : Fin 9, succ9 (succ9 i) ≠ i := by
  intro i; fin_cases i <;> decide

theorem succ5_pred5 : ∀ i : Fin 5, succ5 (pred5 i) = i := by
  intro i; fin_cases i <;> decide
theorem pred5_succ5 : ∀ i : Fin 5, pred5 (succ5 i) = i := by
  intro i; fin_cases i <;> decide
theorem succ5_ne : ∀ i : Fin 5, succ5 i ≠ i := by
  intro i; fin_cases i <;> decide
theorem succ5_ne_pred5 : ∀ i : Fin 5, succ5 i ≠ pred5 i := by
  intro i; fin_cases i <;> decide
theorem succ5_succ5_ne : ∀ i : Fin 5, succ5 (succ5 i) ≠ i := by
  intro i; fin_cases i <;> decide

theorem succ6_pred6 : ∀ i : Fin 6, succ6 (pred6 i) = i := by
  intro i; fin_cases i <;> decide
theorem pred6_succ6 : ∀ i : Fin 6, pred6 (succ6 i) = i := by
  intro i; fin_cases i <;> decide
theorem succ6_ne : ∀ i : Fin 6, succ6 i ≠ i := by
  intro i; fin_cases i <;> decide
theorem succ6_ne_pred6 : ∀ i : Fin 6, succ6 i ≠ pred6 i := by
  intro i; fin_cases i <;> decide
theorem succ6_succ6_ne : ∀ i : Fin 6, succ6 (succ6 i) ≠ i := by
  intro i; fin_cases i <;> decide

/-- 环路闭合（具体 n）：由 `finRotate` 是等价换元得到。 -/
theorem sumClosed9 (q : Fin 9 → Point) : SumClosed q succ9 := by
  simp only [SumClosed, succ9, Finset.sum_sub_distrib]
  have h : (∑ i : Fin 9, q (i + 1)) = ∑ i : Fin 9, q i := by
    refine Fintype.sum_equiv (finRotate 9) (fun i : Fin 9 => q (i + 1)) q ?_
    intro i
    rw [finRotate_apply]
  rw [h, sub_self]

theorem sumClosed5 (q : Fin 5 → Point) : SumClosed q succ5 := by
  simp only [SumClosed, succ5, Finset.sum_sub_distrib]
  have h : (∑ i : Fin 5, q (i + 1)) = ∑ i : Fin 5, q i := by
    refine Fintype.sum_equiv (finRotate 5) (fun i : Fin 5 => q (i + 1)) q ?_
    intro i
    rw [finRotate_apply]
  rw [h, sub_self]

theorem sumClosed6 (q : Fin 6 → Point) : SumClosed q succ6 := by
  simp only [SumClosed, succ6, Finset.sum_sub_distrib]
  have h : (∑ i : Fin 6, q (i + 1)) = ∑ i : Fin 6, q i := by
    refine Fintype.sum_equiv (finRotate 6) (fun i : Fin 6 => q (i + 1)) q ?_
    intro i
    rw [finRotate_apply]
  rw [h, sub_self]

/-- H0 侧五边形：`(C_2,C_3,C_4,C_5,C_6)`（raw 表 H0 fan 的链）。 -/
def qA (C : Fin 9 → Point) : Fin 5 → Point := ![C 2, C 3, C 4, C 5, C 6]

/-- H1 侧六边形：`(C_6,C_7,C_8,C_0,C_1,C_2)`（raw 表 H1 fan 的链）。 -/
def qB (C : Fin 9 → Point) : Fin 6 → Point := ![C 6, C 7, C 8, C 0, C 1, C 2]

/-- 五边形 `qA` 的严格凸性：4 条环边由环的 `RingConvex` 付，闭合弦边 `(C_6,C_2)` 由可付前提付
（只要求 A′ 弧上的 3 个顶点 `j = 3,4,5`；全称 7 点是**假前提**，会与 `ringConvex_qB` 的弦前提互相矛盾）。 -/
theorem ringConvex_qA (C : Fin 9 → Point) (h : RingConvex C succ9)
    (hchord : ∀ j : Fin 9, (j = 3 ∨ j = 4 ∨ j = 5) → 0 < orient (C 6) (C 2) (C j)) :
    RingConvex (qA C) succ5 := by
  intro i j hij hne
  fin_cases i
  · fin_cases j
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
    · exact h 2 4 (by decide) (by decide)
    · exact h 2 5 (by decide) (by decide)
    · exact h 2 6 (by decide) (by decide)
  · fin_cases j
    · exact h 3 2 (by decide) (by decide)
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
    · exact h 3 5 (by decide) (by decide)
    · exact h 3 6 (by decide) (by decide)
  · fin_cases j
    · exact h 4 2 (by decide) (by decide)
    · exact h 4 3 (by decide) (by decide)
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
    · exact h 4 6 (by decide) (by decide)
  · fin_cases j
    · exact h 5 2 (by decide) (by decide)
    · exact h 5 3 (by decide) (by decide)
    · exact h 5 4 (by decide) (by decide)
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
  · fin_cases j
    · exact absurd hne (by decide)
    · exact hchord 3 (by decide)
    · exact hchord 4 (by decide)
    · exact hchord 5 (by decide)
    · exact absurd hij (by decide)

/-- 六边形 `qB` 的严格凸性：5 条环边由环的 `RingConvex` 付，闭合弦边 `(C_2,C_6)` 由可付前提付
（只要求 B′ 弧上的 4 个顶点 `j = 7,8,0,1`）。 -/
theorem ringConvex_qB (C : Fin 9 → Point) (h : RingConvex C succ9)
    (hchord : ∀ j : Fin 9, (j = 7 ∨ j = 8 ∨ j = 0 ∨ j = 1) → 0 < orient (C 2) (C 6) (C j)) :
    RingConvex (qB C) succ6 := by
  intro i j hij hne
  fin_cases i
  · fin_cases j
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
    · exact h 6 8 (by decide) (by decide)
    · exact h 6 0 (by decide) (by decide)
    · exact h 6 1 (by decide) (by decide)
    · exact h 6 2 (by decide) (by decide)
  · fin_cases j
    · exact h 7 6 (by decide) (by decide)
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
    · exact h 7 0 (by decide) (by decide)
    · exact h 7 1 (by decide) (by decide)
    · exact h 7 2 (by decide) (by decide)
  · fin_cases j
    · exact h 8 6 (by decide) (by decide)
    · exact h 8 7 (by decide) (by decide)
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
    · exact h 8 1 (by decide) (by decide)
    · exact h 8 2 (by decide) (by decide)
  · fin_cases j
    · exact h 0 6 (by decide) (by decide)
    · exact h 0 7 (by decide) (by decide)
    · exact h 0 8 (by decide) (by decide)
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
    · exact h 0 2 (by decide) (by decide)
  · fin_cases j
    · exact h 1 6 (by decide) (by decide)
    · exact h 1 7 (by decide) (by decide)
    · exact h 1 8 (by decide) (by decide)
    · exact h 1 0 (by decide) (by decide)
    · exact absurd hij (by decide)
    · exact absurd hne (by decide)
  · fin_cases j
    · exact absurd hne (by decide)
    · exact hchord 7 (by decide)
    · exact hchord 8 (by decide)
    · exact hchord 0 (by decide)
    · exact hchord 1 (by decide)
    · exact absurd hij (by decide)

end N11Formalization.FlashTiling

#print axioms N11Formalization.FlashTiling.sumClosed9
#print axioms N11Formalization.FlashTiling.ringConvex_qA
#print axioms N11Formalization.FlashTiling.ringConvex_qB
