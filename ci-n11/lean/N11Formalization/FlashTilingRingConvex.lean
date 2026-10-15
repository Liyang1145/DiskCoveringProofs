import N11Formalization.FlashTilingSignsRing63
import N11Formalization.FlashTilingCyclic

/-!
# FlashTilingRingConvex —— 装配 `RingConvex (ringCenter u) FlashTiling.succ9`

消费 `FlashTilingSignsRing63` 的 63 条（独立冻结，本件失败不影响其核）。
按 i 分 9 块把每目标的候选降到 ≤7 条，避免全 63 备选的搜索代价。
-/

noncomputable section
set_option maxHeartbeats 8000000

namespace N11Formalization.FlashTilingSigns
open N11Formalization

/-- i = 0 块：`∀ j ≠ 0, j ≠ 1 → 0 < orient (C 0) (C 1) (C j)`。 -/
theorem rc0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (0 : Fin 9) → j ≠ (0 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_0_1_2 hu
      | exact orient_0_1_3 hu
      | exact orient_0_1_4 hu
      | exact orient_0_1_5 hu
      | exact orient_0_1_6 hu
      | exact orient_0_1_7 hu
      | exact orient_0_1_8 hu

/-- i = 1 块：`∀ j ≠ 1, j ≠ 2 → 0 < orient (C 1) (C 2) (C j)`。 -/
theorem rc1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (1 : Fin 9) → j ≠ (1 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_1_2_0 hu
      | exact orient_1_2_3 hu
      | exact orient_1_2_4 hu
      | exact orient_1_2_5 hu
      | exact orient_1_2_6 hu
      | exact orient_1_2_7 hu
      | exact orient_1_2_8 hu

/-- i = 2 块：`∀ j ≠ 2, j ≠ 3 → 0 < orient (C 2) (C 3) (C j)`。 -/
theorem rc2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (2 : Fin 9) → j ≠ (2 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_2_3_0 hu
      | exact orient_2_3_1 hu
      | exact orient_2_3_4 hu
      | exact orient_2_3_5 hu
      | exact orient_2_3_6 hu
      | exact orient_2_3_7 hu
      | exact orient_2_3_8 hu

/-- i = 3 块：`∀ j ≠ 3, j ≠ 4 → 0 < orient (C 3) (C 4) (C j)`。 -/
theorem rc3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (3 : Fin 9) → j ≠ (3 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_3_4_0 hu
      | exact orient_3_4_1 hu
      | exact orient_3_4_2 hu
      | exact orient_3_4_5 hu
      | exact orient_3_4_6 hu
      | exact orient_3_4_7 hu
      | exact orient_3_4_8 hu

/-- i = 4 块：`∀ j ≠ 4, j ≠ 5 → 0 < orient (C 4) (C 5) (C j)`。 -/
theorem rc4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (4 : Fin 9) → j ≠ (4 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_4_5_0 hu
      | exact orient_4_5_1 hu
      | exact orient_4_5_2 hu
      | exact orient_4_5_3 hu
      | exact orient_4_5_6 hu
      | exact orient_4_5_7 hu
      | exact orient_4_5_8 hu

/-- i = 5 块：`∀ j ≠ 5, j ≠ 6 → 0 < orient (C 5) (C 6) (C j)`。 -/
theorem rc5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (5 : Fin 9) → j ≠ (5 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_5_6_0 hu
      | exact orient_5_6_1 hu
      | exact orient_5_6_2 hu
      | exact orient_5_6_3 hu
      | exact orient_5_6_4 hu
      | exact orient_5_6_7 hu
      | exact orient_5_6_8 hu

/-- i = 6 块：`∀ j ≠ 6, j ≠ 7 → 0 < orient (C 6) (C 7) (C j)`。 -/
theorem rc6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (6 : Fin 9) → j ≠ (6 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_6_7_0 hu
      | exact orient_6_7_1 hu
      | exact orient_6_7_2 hu
      | exact orient_6_7_3 hu
      | exact orient_6_7_4 hu
      | exact orient_6_7_5 hu
      | exact orient_6_7_8 hu

/-- i = 7 块：`∀ j ≠ 7, j ≠ 8 → 0 < orient (C 7) (C 8) (C j)`。 -/
theorem rc7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (7 : Fin 9) → j ≠ (7 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_7_8_0 hu
      | exact orient_7_8_1 hu
      | exact orient_7_8_2 hu
      | exact orient_7_8_3 hu
      | exact orient_7_8_4 hu
      | exact orient_7_8_5 hu
      | exact orient_7_8_6 hu

/-- i = 8 块：`∀ j ≠ 8, j ≠ 0 → 0 < orient (C 8) (C 0) (C j)`。 -/
theorem rc8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    ∀ j : Fin 9, j ≠ (8 : Fin 9) → j ≠ (8 : Fin 9) + 1 →
      0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u j) := by
  intro j hj hj2
  fin_cases j <;>
    first
      | (exfalso; exact absurd rfl hj)
      | (exfalso; exact absurd rfl hj2)
      | exact orient_8_0_1 hu
      | exact orient_8_0_2 hu
      | exact orient_8_0_3 hu
      | exact orient_8_0_4 hu
      | exact orient_8_0_5 hu
      | exact orient_8_0_6 hu
      | exact orient_8_0_7 hu

/-- **装配**。 -/
theorem ringConvex {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    FlashTiling.RingConvex (ringCenter u) FlashTiling.succ9 := by
  intro i j hij hne
  fin_cases i
  · exact rc0 hu j hij hne
  · exact rc1 hu j hij hne
  · exact rc2 hu j hij hne
  · exact rc3 hu j hij hne
  · exact rc4 hu j hij hne
  · exact rc5 hu j hij hne
  · exact rc6 hu j hij hne
  · exact rc7 hu j hij hne
  · exact rc8 hu j hij hne

end N11Formalization.FlashTilingSigns
