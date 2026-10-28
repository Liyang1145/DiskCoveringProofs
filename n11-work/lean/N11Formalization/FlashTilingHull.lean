import Mathlib
import N11Formalization.FlashTilingCyclic

/-!
# FlashTilingHull —— 11 面覆盖 11 中心凸包（flash-tiling 写域，raw 11 面表原序）

结论形态：`∀ p ∈ convexHull ℝ (Set.range (centers11 C h0 h1)), ∃ f : Fin 11, p ∈ convexHull ℝ {fv1 f, fv2 f, fv3 f}`
（`fv1/fv2/fv3` 的索引顺序与 `flash-boundary-caps` 的 `faceI1/faceI2/faceI3` 逐位一致）。

可付前提：
* `hcv : RingConvex C succ9` —— 环严格凸 CCW（63 条定向不等式）；
* `hh0/hh1 : ∀ i, 0 ≤ phi C succ9 i hub` —— **两个 hub 位于环凸包内**（18 条；这条是把 9 环结论提升到
  11 中心凸包的关键：`Covers` 用的是 11 中心凸包）；
* `hchordA/hchordB` —— 弦 `[C 2,C 6]` 两侧号（子多边形闭合边条件）；
* `hq`/`hflip` —— **消费** `FlashBoundaryCapsFlip` 的公共点 `q` 与 `diagonal_flip`（本文件不重写）。

装配：`fan_dart`（apex 任意）→ 9 边形（apex `C 2`）得 `A' ∪ B'`；再对 `qA`（apex `h0`）/`qB`（apex `h1`）
各用一次 → 9 个列出面；两枚闭合边见证 `conv(h_i,C 2,C 6)` 由 `hflip` 归到中心面 9/10。

无 sorry / 自定义 axiom / native_decide。
-/

namespace N11Formalization.FlashTiling

open N11Formalization

/-- 11 个中心（raw 顺序：环 0..8、hub0、hub1）。 -/
def centers11 (C : Fin 9 → Point) (h0 h1 : Point) : Fin 11 → Point :=
  ![C 0, C 1, C 2, C 3, C 4, C 5, C 6, C 7, C 8, h0, h1]

/-- raw 11 面表第 1 个顶点（= `faceI1`）。 -/
def fv1 (C : Fin 9 → Point) : Fin 11 → Point :=
  ![C 0, C 1, C 2, C 3, C 4, C 5, C 6, C 7, C 8, C 2, C 6]

/-- raw 11 面表第 2 个顶点（= `faceI2`）。 -/
def fv2 (C : Fin 9 → Point) (h0 : Point) : Fin 11 → Point :=
  ![C 1, C 2, C 3, C 4, C 5, C 6, C 7, C 8, C 0, h0, h0]

/-- raw 11 面表第 3 个顶点（= `faceI3`，hub 位：9 号位为 `hub0`，10 号位为 `hub1`）。 -/
def fv3 (_C : Fin 9 → Point) (h0 h1 : Point) : Fin 11 → Point :=
  ![h1, h1, h0, h0, h0, h0, h1, h1, h1, h1, h1]

/-- 9 边形（环本体）。 -/
def q9 (C : Fin 9 → Point) : Fin 9 → Point := fun i => C i

theorem range_qA_eq (C : Fin 9 → Point) :
    Set.range (qA C) = ({C 2, C 3, C 4, C 5, C 6} : Set Point) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [qA]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩

theorem range_qB_eq (C : Fin 9 → Point) :
    Set.range (qB C) = ({C 6, C 7, C 8, C 0, C 1, C 2} : Set Point) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [qB]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩

/-- 三元子集落入 `A'` 的凸包。 -/
theorem hull3_subset_A (C : Fin 9 → Point) {a b c : Point}
    (ha : a ∈ Set.range (qA C)) (hb : b ∈ Set.range (qA C)) (hc : c ∈ Set.range (qA C)) :
    convexHull ℝ ({a, b, c} : Set Point) ⊆ convexHull ℝ (Set.range (qA C)) :=
  convexHull_mono (by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc)

/-- 三元子集落入 `B'` 的凸包。 -/
theorem hull3_subset_B (C : Fin 9 → Point) {a b c : Point}
    (ha : a ∈ Set.range (qB C)) (hb : b ∈ Set.range (qB C)) (hc : c ∈ Set.range (qB C)) :
    convexHull ℝ ({a, b, c} : Set Point) ⊆ convexHull ℝ (Set.range (qB C)) :=
  convexHull_mono (by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc)

/-- 环边半平面在每个环顶点上非负（含相等情形）。 -/
theorem phi_ring_nonneg (C : Fin 9 → Point) (hcv : RingConvex C succ9) (i j : Fin 9) :
    0 ≤ phi C succ9 i (C j) := by
  rcases eq_or_ne j i with rfl | hji
  · simp only [phi, orient, sub_self, det2_zero_right, le_refl]
  · rcases eq_or_ne j (succ9 i) with hjs | hjs
    · rw [hjs]
      have h : phi C succ9 i (C (succ9 i)) = 0 := by
        simp only [phi, orient]
        rw [det2_self]
      rw [h]
    · exact le_of_lt (hcv i j hji hjs)

/-- 11 中心凸包里每点满足环的全部 9 条边半平面条件（**hub 必须也在环内**：`hh0/hh1`）。 -/
theorem phi_nonneg_of_mem_hull (C : Fin 9 → Point) (h0 h1 : Point)
    (hcv : RingConvex C succ9) (hh0 : ∀ i : Fin 9, 0 ≤ phi C succ9 i h0)
    (hh1 : ∀ i : Fin 9, 0 ≤ phi C succ9 i h1)
    {p : Point} (hp : p ∈ convexHull ℝ (Set.range (centers11 C h0 h1))) :
    ∀ i : Fin 9, 0 ≤ phi C succ9 i p := by
  intro i
  have hsub : ∀ k : Fin 11, 0 ≤ orient (C i) (C (succ9 i)) (centers11 C h0 h1 k) := by
    intro k
    fin_cases k <;> simp only [centers11]
    · exact phi_ring_nonneg C hcv i 0
    · exact phi_ring_nonneg C hcv i 1
    · exact phi_ring_nonneg C hcv i 2
    · exact phi_ring_nonneg C hcv i 3
    · exact phi_ring_nonneg C hcv i 4
    · exact phi_ring_nonneg C hcv i 5
    · exact phi_ring_nonneg C hcv i 6
    · exact phi_ring_nonneg C hcv i 7
    · exact phi_ring_nonneg C hcv i 8
    · exact hh0 i
    · exact hh1 i
  exact convexHull_subset_orient_nonneg (centers11 C h0 h1) (C i) (C (succ9 i)) hsub hp

/-- **主装配定理**：11 个 raw 面覆盖 11 中心凸包。 -/
theorem hull_cover_11 (C : Fin 9 → Point) (h0 h1 : Point)
    (hcv : RingConvex C succ9)
    (hh0 : ∀ i : Fin 9, 0 ≤ phi C succ9 i h0)
    (hh1 : ∀ i : Fin 9, 0 ≤ phi C succ9 i h1)
    (hchordA : ∀ j : Fin 9, (j = 3 ∨ j = 4 ∨ j = 5) → 0 < orient (C 6) (C 2) (C j))
    (hchordB : ∀ j : Fin 9, (j = 7 ∨ j = 8 ∨ j = 0 ∨ j = 1) → 0 < orient (C 2) (C 6) (C j))
    (hqcross : ∃ q : Point, q ∈ segment ℝ (C 2) (C 6) ∧ q ∈ segment ℝ h0 h1)
    (hflip : ∀ A B H0 H1 q : Point, q ∈ segment ℝ A B → q ∈ segment ℝ H0 H1 →
      convexHull ℝ ({H0, A, B} : Set Point) ∪ convexHull ℝ ({H1, A, B} : Set Point) ⊆
      convexHull ℝ ({A, H0, H1} : Set Point) ∪ convexHull ℝ ({B, H0, H1} : Set Point)) :
    ∀ p ∈ convexHull ℝ (Set.range (centers11 C h0 h1)),
      ∃ f : Fin 11, p ∈ convexHull ℝ ({fv1 C f, fv2 C h0 f, fv3 C h0 h1 f} : Set Point) := by
  have hA : RingConvex (qA C) succ5 := ringConvex_qA C hcv hchordA
  have hB : RingConvex (qB C) succ6 := ringConvex_qB C hcv hchordB
  intro p hp
  have hphi := phi_nonneg_of_mem_hull C h0 h1 hcv hh0 hh1 hp
  obtain ⟨i, hi⟩ := fan_dart (n := 8) succ9_pred9 succ9_ne succ9_ne_pred9 succ9_succ9_ne
    hcv (sumClosed9 (q9 C)) (x := C 2) hphi
  -- 分裂：9 边形的 fan 见证落在 A' 或 B'
  have hAB : p ∈ convexHull ℝ (Set.range (qA C)) ∨ p ∈ convexHull ℝ (Set.range (qB C)) := by
    fin_cases i
    · right
      refine hull3_subset_B C ⟨5, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩ ?_
      simpa [q9, succ9, qB] using hi
    · right
      refine hull3_subset_B C ⟨5, rfl⟩ ⟨4, rfl⟩ ⟨5, rfl⟩ ?_
      simpa [q9, succ9, qB] using hi
    · left
      refine hull3_subset_A C ⟨0, rfl⟩ ⟨0, rfl⟩ ⟨1, rfl⟩ ?_
      simpa [q9, succ9, qA] using hi
    · left
      refine hull3_subset_A C ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩ ?_
      simpa [q9, succ9, qA] using hi
    · left
      refine hull3_subset_A C ⟨0, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ ?_
      simpa [q9, succ9, qA] using hi
    · left
      refine hull3_subset_A C ⟨0, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩ ?_
      simpa [q9, succ9, qA] using hi
    · right
      refine hull3_subset_B C ⟨5, rfl⟩ ⟨0, rfl⟩ ⟨1, rfl⟩ ?_
      simpa [q9, succ9, qB] using hi
    · right
      refine hull3_subset_B C ⟨5, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩ ?_
      simpa [q9, succ9, qB] using hi
    · right
      refine hull3_subset_B C ⟨5, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ ?_
      simpa [q9, succ9, qB] using hi
  rcases hAB with hpA | hpB
  · -- A 侧：qA 的 fan（apex h0）
    have hphiA : ∀ i : Fin 5, 0 ≤ phi (qA C) succ5 i p := by
      intro i
      have hsubA : ∀ j : Fin 5, 0 ≤ orient (qA C i) (qA C (succ5 i)) (qA C j) := by
        intro j
        rcases eq_or_ne j i with rfl | h1'
        · simp only [orient, sub_self, det2_zero_right, le_refl]
        · rcases eq_or_ne j (succ5 i) with hjs | h2'
          · rw [hjs]
            have h : orient (qA C i) (qA C (succ5 i)) (qA C (succ5 i)) = 0 := by
              simp only [orient]
              rw [det2_self]
            rw [h]
          · exact le_of_lt (hA i j h1' h2')
      exact convexHull_subset_orient_nonneg (qA C) (qA C i) (qA C (succ5 i)) hsubA hpA
    obtain ⟨iA, hAi⟩ := fan_dart (n := 4) succ5_pred5 succ5_ne succ5_ne_pred5 succ5_succ5_ne
      hA (sumClosed5 (qA C)) (x := h0) hphiA
    fin_cases iA
    · refine ⟨2, convexHull_mono ?_ hAi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qA, succ5, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · refine ⟨3, convexHull_mono ?_ hAi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qA, succ5, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · refine ⟨4, convexHull_mono ?_ hAi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qA, succ5, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · refine ⟨5, convexHull_mono ?_ hAi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qA, succ5, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · -- 闭合边见证 conv(h0, C 6, C 2) ⊆ 面 9 ∪ 面 10
      obtain ⟨q, hq1, hq2⟩ := hqcross
      have hmemA : p ∈ convexHull ℝ ({h0, C 2, C 6} : Set Point) := by
        refine convexHull_mono ?_ hAi
        intro z hz
        simp only [qA, succ5, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto
      have hfl := hflip (C 2) (C 6) h0 h1 q hq1 hq2
      have hpu : p ∈ convexHull ℝ ({h0, C 2, C 6} : Set Point) ∪
          convexHull ℝ ({h1, C 2, C 6} : Set Point) := Or.inl hmemA
      rcases hfl hpu with h9 | h10
      · refine ⟨9, convexHull_mono ?_ h9⟩
        intro z hz
        simp only [fv1, fv2, fv3, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto
      · refine ⟨10, convexHull_mono ?_ h10⟩
        intro z hz
        simp only [fv1, fv2, fv3, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto
  · -- B 侧：qB 的 fan（apex h1）
    have hphiB : ∀ i : Fin 6, 0 ≤ phi (qB C) succ6 i p := by
      intro i
      have hsubB : ∀ j : Fin 6, 0 ≤ orient (qB C i) (qB C (succ6 i)) (qB C j) := by
        intro j
        rcases eq_or_ne j i with rfl | h1'
        · simp only [orient, sub_self, det2_zero_right, le_refl]
        · rcases eq_or_ne j (succ6 i) with hjs | h2'
          · rw [hjs]
            have h : orient (qB C i) (qB C (succ6 i)) (qB C (succ6 i)) = 0 := by
              simp only [orient]
              rw [det2_self]
            rw [h]
          · exact le_of_lt (hB i j h1' h2')
      exact convexHull_subset_orient_nonneg (qB C) (qB C i) (qB C (succ6 i)) hsubB hpB
    obtain ⟨iB, hBi⟩ := fan_dart (n := 5) succ6_pred6 succ6_ne succ6_ne_pred6 succ6_succ6_ne
      hB (sumClosed6 (qB C)) (x := h1) hphiB
    fin_cases iB
    · refine ⟨6, convexHull_mono ?_ hBi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qB, succ6, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · refine ⟨7, convexHull_mono ?_ hBi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qB, succ6, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · refine ⟨8, convexHull_mono ?_ hBi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qB, succ6, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · refine ⟨0, convexHull_mono ?_ hBi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qB, succ6, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · refine ⟨1, convexHull_mono ?_ hBi⟩
      intro z hz
      simp only [fv1, fv2, fv3, qB, succ6, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    · -- 闭合边见证 conv(h1, C 2, C 6) ⊆ 面 9 ∪ 面 10
      obtain ⟨q, hq1, hq2⟩ := hqcross
      have hmemB : p ∈ convexHull ℝ ({h1, C 2, C 6} : Set Point) := by
        refine convexHull_mono ?_ hBi
        intro z hz
        simp only [qB, succ6, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto
      have hfl := hflip (C 2) (C 6) h0 h1 q hq1 hq2
      have hpu : p ∈ convexHull ℝ ({h0, C 2, C 6} : Set Point) ∪
          convexHull ℝ ({h1, C 2, C 6} : Set Point) := Or.inr hmemB
      rcases hfl hpu with h9 | h10
      · refine ⟨9, convexHull_mono ?_ h9⟩
        intro z hz
        simp only [fv1, fv2, fv3, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto
      · refine ⟨10, convexHull_mono ?_ h10⟩
        intro z hz
        simp only [fv1, fv2, fv3, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto

/-- **三点凸包的 barycentric 形式**（Root `hcover` 所需形状）。
由 `convexHull_min` 对系数集 `T := {la•a+lb•b+lc•c | la,lb,lc ≥ 0, Σ=1}` 使用：`T` 凸且含三顶点。 -/
theorem mem_convexHull_three {a b c p : Point}
    (h : p ∈ convexHull ℝ ({a, b, c} : Set Point)) :
    ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
      p = la • a + lb • b + lc • c := by
  have hTc : Convex ℝ {q : Point | ∃ la lb lc : ℝ,
      0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧ q = la • a + lb • b + lc • c} := by
    intro x hx y hy s t hs ht hst
    obtain ⟨la, lb, lc, hla, hlb, hlc, hsum, rfl⟩ := hx
    obtain ⟨ka, kb, kc, hka, hkb, hkc, hksum, rfl⟩ := hy
    refine ⟨s * la + t * ka, s * lb + t * kb, s * lc + t * kc, ?_, ?_, ?_, ?_, ?_⟩
    · positivity
    · positivity
    · positivity
    · nlinarith [hsum, hksum, hst]
    · module
  have ha : a ∈ {q : Point | ∃ la lb lc : ℝ,
      0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧ q = la • a + lb • b + lc • c} :=
    ⟨1, 0, 0, zero_le_one, le_refl 0, le_refl 0, by norm_num, by simp⟩
  have hb : b ∈ {q : Point | ∃ la lb lc : ℝ,
      0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧ q = la • a + lb • b + lc • c} :=
    ⟨0, 1, 0, le_refl 0, zero_le_one, le_refl 0, by norm_num, by simp⟩
  have hc : c ∈ {q : Point | ∃ la lb lc : ℝ,
      0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧ q = la • a + lb • b + lc • c} :=
    ⟨0, 0, 1, le_refl 0, le_refl 0, zero_le_one, by norm_num, by simp⟩
  have hsub : ({a, b, c} : Set Point) ⊆ {q : Point | ∃ la lb lc : ℝ,
      0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧ q = la • a + lb • b + lc • c} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  exact convexHull_min hsub hTc h

/-- **Root `hcover` 形状**：11 面剖分的 barycentric 形式（与 `faceI1/2/3` 索引逐位一致）。 -/
theorem hcover_barycentric (C : Fin 9 → Point) (h0 h1 : Point)
    (hcv : RingConvex C succ9)
    (hh0 : ∀ i : Fin 9, 0 ≤ phi C succ9 i h0)
    (hh1 : ∀ i : Fin 9, 0 ≤ phi C succ9 i h1)
    (hchordA : ∀ j : Fin 9, (j = 3 ∨ j = 4 ∨ j = 5) → 0 < orient (C 6) (C 2) (C j))
    (hchordB : ∀ j : Fin 9, (j = 7 ∨ j = 8 ∨ j = 0 ∨ j = 1) → 0 < orient (C 2) (C 6) (C j))
    (hqcross : ∃ q : Point, q ∈ segment ℝ (C 2) (C 6) ∧ q ∈ segment ℝ h0 h1)
    (hflip : ∀ A B H0 H1 q : Point, q ∈ segment ℝ A B → q ∈ segment ℝ H0 H1 →
      convexHull ℝ ({H0, A, B} : Set Point) ∪ convexHull ℝ ({H1, A, B} : Set Point) ⊆
      convexHull ℝ ({A, H0, H1} : Set Point) ∪ convexHull ℝ ({B, H0, H1} : Set Point)) :
    ∀ p ∈ convexHull ℝ (Set.range (centers11 C h0 h1)),
      ∃ f : Fin 11, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • fv1 C f + lb • fv2 C h0 f + lc • fv3 C h0 h1 f := by
  intro p hp
  obtain ⟨f, hf⟩ :=
    hull_cover_11 C h0 h1 hcv hh0 hh1 hchordA hchordB hqcross hflip p hp
  obtain ⟨la, lb, lc, h1', h2', h3', h4', h5'⟩ := mem_convexHull_three hf
  exact ⟨f, la, lb, lc, h1', h2', h3', h4', h5'⟩

end N11Formalization.FlashTiling

#print axioms N11Formalization.FlashTiling.hull_cover_11
#print axioms N11Formalization.FlashTiling.hcover_barycentric
#print axioms N11Formalization.FlashTiling.mem_convexHull_three
#print axioms N11Formalization.FlashTiling.phi_nonneg_of_mem_hull