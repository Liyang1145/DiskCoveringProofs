/-
# FlashCoverReductionNearestEdge — unitDisk 截线真正接入受限见证判据 + cover 最近邻排除

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。

## 本文件做什么

1. `interval_helly`：**有限区间 Helly** 的一般形式（区间族共同相交 ⟺ 两两相交）。
2. `restricted_witness_in_disk_iff`：把 `unitDisk` 截线区间**真正接进**受限见证判据
   （不是"可直接追加"）：右端多出 `0 ≤ diskD`（截线非空）与两条**跨类**相容条件
   （竞争者下界 ≤ 盘上界 / 盘下界 ≤ 竞争者上界）。
   注意 `X ∈ unitDisk` 这一条**不可省**：`Real.sqrt` 在 `D < 0` 时取 0 会让形式区间塌成一点。
3. `nearest_le_cover_radius`：**覆盖消费者**——`X` 在盘内且是站点 `i` 的最近点 ⇒ `dist X (c i) ≤ r`
   （由 `Covers` 给出某站点 ≤ r，再用最近性）。
4. `cover_common_nearest_necessary`：`Covers` + 盘内共同最近点 ⇒ 受限见证判据的右端全部成立
   （**必要**方向；逆只给 Voronoi 相交，**不**声称覆盖）。
5. `nearest_adjacency_excluded_by_pair`：若两两相容条件失败（§7 的 pair obstruction），
   则**不存在**这样的盘内共同最近点 ⇒ 该 nearest 邻接被排除。

**声明**：本文件把"受限见证"与"覆盖 ⇒ ≤ r"接起来；它**不**断言任意 cover 的图分类。
-/

import Mathlib
import N11Formalization.Definitions
import N11Formalization.FlashCoverReductionBlockerGeometry
import N11Formalization.FlashCoverReductionUnitDiskTruncation

namespace N11Formalization

open scoped RealInnerProductSpace

/-! ## 1. 有限区间 Helly（一般形式） -/

/-- **有限 1D Helly**：有限族区间 `[lo i, hi i]` 有公共点 ⟺ 任意两区间相交。 -/
theorem interval_helly {ι : Type*} [Fintype ι] [Nonempty ι] (lo hi : ι → ℝ) :
    (∃ τ : ℝ, ∀ i, lo i ≤ τ ∧ τ ≤ hi i) ↔ ∀ i j, lo i ≤ hi j := by
  constructor
  · rintro ⟨τ, h⟩ i j
    exact le_trans (h i).1 (h j).2
  · intro h
    obtain ⟨i₀, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ lo Finset.univ_nonempty
    exact ⟨lo i₀, fun i => ⟨hmax i (Finset.mem_univ i), h i₀ i⟩⟩

/-! ## 2. 记号 -/

/-- 判据里的 `t = √(r² − ‖C−A‖²/4)`。 -/
noncomputable def tLens (A C : Point) (r : ℝ) : ℝ := Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)

/-- 竞争者 `k` 的下界。 -/
noncomputable def cLo (A C M u : Point) (cc : κ → Point) (r : ℝ) (k : κ) : ℝ :=
  tauLo (compB A u (cc k)) (compC0 A C M (cc k)) (tLens A C r)

/-- 竞争者 `k` 的上界。 -/
noncomputable def cHi (A C M u : Point) (cc : κ → Point) (r : ℝ) (k : κ) : ℝ :=
  tauHi (compB A u (cc k)) (compC0 A C M (cc k)) (tLens A C r)

/-! ## 3. unitDisk 截线接入受限见证判据 -/

/-- **盘内受限见证判据**。在 §8 基础上加入 `‖X‖ ≤ 1`，右端相应多出
`0 ≤ diskD` 与两条跨类相容条件。 -/
theorem restricted_witness_in_disk_iff {κ : Type*} [Fintype κ] [Nonempty κ]
    (A C : Point) (cc : κ → Point) (r : ℝ) {M u : Point}
    (hAC : A ≠ C) (hM : M = (2 : ℝ)⁻¹ • (A + C)) (hu1 : ‖u‖ = 1)
    (hu : (inner ℝ u (C - A) : ℝ) = 0) :
    (∃ X : Point, ‖X - A‖ = ‖X - C‖ ∧ ‖X - A‖ ≤ r ∧ ‖X‖ ≤ 1
        ∧ ∀ k, ‖X - A‖ ≤ ‖X - cc k‖)
      ↔ ‖C - A‖ ≤ 2 * r ∧ 0 ≤ diskD M u ∧
        (∀ k, compB A u (cc k) = 0 → 0 ≤ compC0 A C M (cc k)) ∧
        (∀ k l, cLo A C M u cc r k ≤ cHi A C M u cc r l) ∧
        (∀ k, cLo A C M u cc r k ≤ diskHi M u) ∧
        (∀ k, diskLo M u ≤ cHi A C M u cc r k) := by
  have hd : 0 ≤ ‖C - A‖ := norm_nonneg _
  constructor
  · -- (⇒)
    rintro ⟨X, heq, hrX, hX1, hne⟩
    have h2r : ‖C - A‖ ≤ 2 * r := by
      have h1 : ‖C - A‖ ≤ ‖C - X‖ + ‖X - A‖ := by
        have h := norm_add_le (C - X) (X - A)
        rwa [show C - X + (X - A) = C - A by abel] at h
      have h2 : ‖C - X‖ = ‖X - A‖ := by rw [norm_sub_rev, heq]
      linarith
    obtain ⟨τ, hXτ⟩ := equidistant_representation hAC hM hu1 hu heq
    have hτ := abs_tau_le_sqrt hM hXτ hu1 hu hrX
    -- 截线非空：由 ‖X‖ ≤ 1 与配方
    have hD0 : 0 ≤ diskD M u := by
      have hle1 : ‖M + τ • u‖ ≤ 1 := by rw [← hXτ]; exact hX1
      have hle : ‖M + τ • u‖ ^ 2 ≤ 1 := by nlinarith [hle1, norm_nonneg (M + τ • u)]
      have hsq := norm_sq_along_line (M := M) (u := u) (τ := τ) hu1
      rw [hsq] at hle
      have h2 : (0 : ℝ) ≤ (τ + (inner ℝ M u : ℝ)) ^ 2 := sq_nonneg _
      simp only [diskD]
      linarith
    have hdlo : diskLo M u ≤ τ := by
      have h := (unitDisk_tau_interval hu1 hD0).mp (by rw [← hXτ]; exact hX1)
      exact h.1
    have hdhi : τ ≤ diskHi M u := by
      have h := (unitDisk_tau_interval hu1 hD0).mp (by rw [← hXτ]; exact hX1)
      exact h.2
    have hdiff : ∀ k, ‖M + τ • u - cc k‖ ^ 2 - ‖M + τ • u - A‖ ^ 2 =
        (‖cc k - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4) - 2 * τ * (inner ℝ u (cc k - A) : ℝ) :=
      fun k => bisector_difference' (a := A) (c := C) (b := cc k) (M := M) (u := u)
        (τ := τ) hM
    have hsat : ∀ k, 2 * τ * (inner ℝ u (cc k - A) : ℝ)
        ≤ ‖cc k - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4 := by
      intro k
      have h1 : ‖X - cc k‖ ^ 2 - ‖X - A‖ ^ 2 ≥ 0 := by
        nlinarith [norm_nonneg (X - cc k), norm_nonneg (X - A), hne k]
      rw [hXτ] at h1
      linarith [hdiff k, h1]
    have ht0 : (0 : ℝ) ≤ tLens A C r := Real.sqrt_nonneg _
    have hb1 : -tLens A C r ≤ τ := (abs_le.mp hτ).1
    have hb2 : τ ≤ tLens A C r := (abs_le.mp hτ).2
    refine ⟨h2r, hD0, ?_, ?_, ?_, ?_⟩
    · intro k hk0
      have h := hsat k
      have hb : (inner ℝ u (cc k - A) : ℝ) = 0 := hk0
      rw [hb] at h
      simpa [compC0] using h
    · intro k l
      have hLk : cLo A C M u cc r k ≤ τ := by
        by_cases hbk : compB A u (cc k) = 0
        · simp only [cLo, tauLo, hbk, lt_self_iff_false, ↓reduceIte]
          exact hb1
        · exact tauLo_le_of (c := compC0 A C M (cc k)) hbk (hsat k) hb1
      have hHl : τ ≤ cHi A C M u cc r l := by
        by_cases hbl : compB A u (cc l) = 0
        · simp only [cHi, tauHi, hbl, lt_self_iff_false, ↓reduceIte]
          exact hb2
        · exact le_tauHi_of (c := compC0 A C M (cc l)) hbl (hsat l) hb2
      exact le_trans hLk hHl
    · intro k
      have hLk : cLo A C M u cc r k ≤ τ := by
        by_cases hbk : compB A u (cc k) = 0
        · simp only [cLo, tauLo, hbk, lt_self_iff_false, ↓reduceIte]
          exact hb1
        · exact tauLo_le_of (c := compC0 A C M (cc k)) hbk (hsat k) hb1
      exact le_trans hLk hdhi
    · intro k
      have hHl : τ ≤ cHi A C M u cc r k := by
        by_cases hbk : compB A u (cc k) = 0
        · simp only [cHi, tauHi, hbk, lt_self_iff_false, ↓reduceIte]
          exact hb2
        · exact le_tauHi_of (c := compC0 A C M (cc k)) hbk (hsat k) hb2
      exact le_trans hdlo hHl
  · -- (⇐)
    rintro ⟨h2r, hD0, hzero, hpair, hcrossL, hcrossR⟩
    have hr : 0 ≤ r := by linarith [hd, h2r]
    have hnn : 0 ≤ r ^ 2 - ‖C - A‖ ^ 2 / 4 := by nlinarith [hd, hr, h2r]
    have htsq : tLens A C r ^ 2 = r ^ 2 - ‖C - A‖ ^ 2 / 4 := Real.sq_sqrt hnn
    have ht0 : (0 : ℝ) ≤ tLens A C r := Real.sqrt_nonneg _
    have hdD : diskLo M u ≤ diskHi M u := by
      have h : (0 : ℝ) ≤ Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2) :=
        Real.sqrt_nonneg _
      simp only [diskLo, diskHi]
      linarith
    -- 端点界的辅助事实
    have hcHi_le_t : ∀ k, cHi A C M u cc r k ≤ tLens A C r := by
      intro k
      by_cases hb : compB A u (cc k) = 0
      · simp only [cHi, tauHi, hb, lt_self_iff_false, ↓reduceIte]
        exact le_refl _
      · rcases lt_or_gt_of_ne hb with hneg | hpos
        · simp only [cHi, tauHi, if_neg (by linarith : ¬ (0 < compB A u (cc k)))]
          exact le_refl _
        · simp only [cHi, tauHi, if_pos hpos]
          exact min_le_right _ _
    have hcLo_ge_neg : ∀ k, -tLens A C r ≤ cLo A C M u cc r k := by
      intro k
      by_cases hb : compB A u (cc k) = 0
      · simp only [cLo, tauLo, hb, lt_self_iff_false, ↓reduceIte]
        exact le_refl _
      · rcases lt_or_gt_of_ne hb with hneg | hpos
        · simp only [cLo, tauLo, if_pos hneg]
          exact le_max_right _ _
        · simp only [cLo, tauLo, if_neg (by linarith : ¬ (compB A u (cc k) < 0))]
          exact le_refl _
    obtain ⟨k₀, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun k => cLo A C M u cc r k) Finset.univ_nonempty
    set τ₀ := max (diskLo M u) (cLo A C M u cc r k₀) with hτ₀
    have hclo_max : ∀ k, cLo A C M u cc r k ≤ τ₀ := fun k =>
      le_trans (hmax k (Finset.mem_univ k)) (le_max_right _ _)
    have hτt : τ₀ ≤ tLens A C r := by
      rw [hτ₀]
      exact max_le (le_trans (hcrossR k₀) (hcHi_le_t k₀))
        (le_trans (hpair k₀ k₀) (hcHi_le_t k₀))
    have hτgt : -tLens A C r ≤ τ₀ :=
      le_trans (hcLo_ge_neg k₀) (le_max_right _ _)
    have hτdisk : τ₀ ≤ diskHi M u := by
      rw [hτ₀]
      exact max_le hdD (hcrossL k₀)
    have hchi : ∀ k, τ₀ ≤ cHi A C M u cc r k := by
      intro k
      rw [hτ₀]
      exact max_le (hcrossR k) (hpair k₀ k)
    have hτabs : |τ₀| ≤ tLens A C r := abs_le.mpr ⟨hτgt, hτt⟩
    have hτ2 : τ₀ ^ 2 ≤ tLens A C r ^ 2 := by
      have h5 : |τ₀| ≤ |tLens A C r| := by rwa [abs_of_nonneg ht0]
      simpa [sq_abs] using sq_le_sq.mpr h5
    refine ⟨M + τ₀ • u, bisector_equidistant' hM hu, ?_, ?_, ?_⟩
    · -- ‖X−A‖ ≤ r
      have hsq := norm_sq_eq_tau_sq_add hM (rfl : M + τ₀ • u = M + τ₀ • u) hu1 hu
      have hle : ‖M + τ₀ • u - A‖ ^ 2 ≤ r ^ 2 := by rw [hsq]; linarith [hτ2, htsq]
      nlinarith [norm_nonneg (M + τ₀ • u - A), hle]
    · -- ‖X‖ ≤ 1
      exact (unitDisk_tau_interval hu1 hD0).mpr ⟨le_max_left _ _, hτdisk⟩
    · -- ∀k: A 不弱于 cc k
      intro k
      have hdiff := bisector_difference' (a := A) (c := C) (b := cc k) (M := M) (u := u)
        (τ := τ₀) hM
      have hnh : ‖M + τ₀ • u - cc k‖ ^ 2 - ‖M + τ₀ • u - A‖ ^ 2 ≥ 0 := by
        rw [hdiff]
        by_cases hb : compB A u (cc k) = 0
        · have hk0 : 0 ≤ compC0 A C M (cc k) := hzero k hb
          simp only [compB, compC0] at hb hk0
          rw [hb]; simp only [mul_zero, sub_zero]; exact hk0
        · have hsat := sat_of_interval (b := compB A u (cc k)) (c := compC0 A C M (cc k))
            (t := tLens A C r) hb (hclo_max k) (hchi k)
          simp only [compB, compC0] at hsat
          linarith
      nlinarith [norm_nonneg (M + τ₀ • u - cc k), norm_nonneg (M + τ₀ • u - A), hnh]

/-! ## 4. cover 消费者：盘内最近点 ⇒ 距离 ≤ r；pair obstruction ⇒ 排除该 nearest 邻接 -/

/-- **覆盖消费者**：`X` 在盘内且是站点 `i` 的最近点 ⇒ `dist X (c i) ≤ r`。 -/
theorem nearest_le_cover_radius {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r)
    {i : Fin 11} {X : Point} (hX : X ∈ unitDisk)
    (hne : ∀ k, dist X (c i) ≤ dist X (c k)) : dist X (c i) ≤ r := by
  obtain ⟨j, hj⟩ := hcov X hX
  exact le_trans (hne j) hj

/-- **必要性**（cover + 盘内共同最近点 ⇒ 受限见证判据右端全部成立）。
注意逆方向只给 Voronoi 相交，**不**声称覆盖。 -/
theorem cover_common_nearest_necessary {c : Fin 11 → Point} {r : ℝ} (hcov : Covers c r)
    {A C : Point} {M u : Point} (hAC : A ≠ C) (hM : M = (2 : ℝ)⁻¹ • (A + C))
    (hu1 : ‖u‖ = 1) (hu : (inner ℝ u (C - A) : ℝ) = 0)
    (hX : ∃ X : Point, X ∈ unitDisk ∧ ‖X - A‖ = ‖X - C‖ ∧ ∀ k, ‖X - A‖ ≤ ‖X - c k‖) :
    ‖C - A‖ ≤ 2 * r ∧ 0 ≤ diskD M u ∧
      (∀ k, compB A u (c k) = 0 → 0 ≤ compC0 A C M (c k)) ∧
      (∀ k l, cLo A C M u c r k ≤ cHi A C M u c r l) ∧
      (∀ k, cLo A C M u c r k ≤ diskHi M u) ∧
      (∀ k, diskLo M u ≤ cHi A C M u c r k) := by
  obtain ⟨X, hX1, heq, hne⟩ := hX
  have hr : ‖X - A‖ ≤ r := by
    obtain ⟨j, hj⟩ := hcov X hX1
    have h := hne j
    simpa [dist_eq_norm] using le_trans (by simpa [dist_eq_norm] using h) hj
  exact (restricted_witness_in_disk_iff A C c r hAC hM hu1 hu).mp
    ⟨X, heq, hr, hX1, hne⟩

/-- **pair obstruction 排除该 nearest 邻接**：只要出现任一"上界 < 下界"的阻塞
（竞争者对，或盘边界与竞争者），就**不存在**盘内共同最近点。 -/
theorem nearest_adjacency_excluded_of_obstruction {c : Fin 11 → Point} {r : ℝ}
    (hcov : Covers c r) {A C : Point} {M u : Point} (hAC : A ≠ C)
    (hM : M = (2 : ℝ)⁻¹ • (A + C)) (hu1 : ‖u‖ = 1)
    (hu : (inner ℝ u (C - A) : ℝ) = 0)
    (hobs : (∃ k l : Fin 11, cHi A C M u c r l < cLo A C M u c r k)
      ∨ (∃ k : Fin 11, diskHi M u < cLo A C M u c r k)
      ∨ (∃ k : Fin 11, cHi A C M u c r k < diskLo M u)) :
    ¬ ∃ X : Point, X ∈ unitDisk ∧ ‖X - A‖ = ‖X - C‖ ∧ ∀ k, ‖X - A‖ ≤ ‖X - c k‖ := by
  intro hX
  obtain ⟨h2r, hD0, hzero, hpair, hcrossL, hcrossR⟩ :=
    cover_common_nearest_necessary hcov hAC hM hu1 hu hX
  rcases hobs with ⟨k, l, hkl⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact absurd (hpair k l) (not_le.mpr hkl)
  · exact absurd (hcrossL k) (not_le.mpr hk)
  · exact absurd (hcrossR k) (not_le.mpr hk)

end N11Formalization
