import N11Formalization.FlashTenBoundaryAnalytic
open scoped Interval
open MeasureTheory
namespace N11Formalization

/-- 纯记账引理：Icc 指示函数在包含区间上的积分 = 子区间上的积分（f 连续即可）。 -/
theorem probe_indicator_interval {f : ℝ → ℝ} (hf : Continuous f) {φ t : ℝ}
    (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) :
    ∫ θ in (φ - Real.pi)..(φ + Real.pi),
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)
      = ∫ θ in (φ - t)..(φ + t), f θ := by
  have hpt : ∀ θ ∈ Set.uIcc (φ - t) (φ + t),
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = f θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith)] at hθ
    simp [hθ]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ =>
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)) volume a b := by
    intro a b
    have hbase : IntervalIntegrable f volume a b := hf.intervalIntegrable (μ := volume) a b
    have hgm : AEStronglyMeasurable (fun θ : ℝ =>
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0))
        (volume.restrict (Ι a b)) :=
      (Measurable.ite measurableSet_Icc hf.measurable measurable_const).aestronglyMeasurable
    refine hbase.mono_fun hgm ?_
    filter_upwards with θ
    by_cases h : θ ∈ Set.Icc (φ - t) (φ + t)
    · simp only [h, if_true]; exact le_rfl
    · simp only [h, if_false, norm_zero]; exact norm_nonneg _
  have hsplit1 : ∫ θ in (φ - Real.pi)..(φ + Real.pi),
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)
      = (∫ θ in (φ - Real.pi)..(φ - t), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0))
        + (∫ θ in (φ - t)..(φ + Real.pi), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint (φ - Real.pi) (φ - t)) (hint (φ - t) (φ + Real.pi))).symm
  have hsplit2 : ∫ θ in (φ - t)..(φ + Real.pi), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)
      = (∫ θ in (φ - t)..(φ + t), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0))
        + (∫ θ in (φ + t)..(φ + Real.pi), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint (φ - t) (φ + t)) (hint (φ + t) (φ + Real.pi))).symm
  have hmin_left : min (φ - Real.pi) (φ - t) = φ - Real.pi := min_eq_left (by linarith)
  have hmax_left : max (φ - Real.pi) (φ - t) = φ - t := max_eq_right (by linarith)
  have hmin_right : min (φ + t) (φ + Real.pi) = φ + t := min_eq_left (by linarith)
  have hmax_right : max (φ + t) (φ + Real.pi) = φ + Real.pi := max_eq_right (by linarith)
  have hz_left : ∫ θ in (φ - Real.pi)..(φ - t),
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
    have hae : ∀ᵐ θ ∂volume, θ ∈ Ι (φ - Real.pi) (φ - t) →
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (by simp : volume ({φ - t} : Set ℝ) = 0)]
        with θ hθne hθin
      have h2 : θ ≤ φ - t := by
        have := hθin.2; rwa [hmax_left] at this
      have hnot : θ ∉ Set.Icc (φ - t) (φ + t) := by
        intro hmem
        exact hθne (le_antisymm h2 hmem.1)
      simp [hnot]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]
  have hz_right : ∫ θ in (φ + t)..(φ + Real.pi),
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
    have hae : ∀ᵐ θ ∂volume, θ ∈ Ι (φ + t) (φ + Real.pi) →
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (by simp : volume ({φ + t} : Set ℝ) = 0)]
        with θ hθne hθin
      have h1 : φ + t < θ := by
        have := hθin.1; rwa [hmin_right] at this
      have hnot : θ ∉ Set.Icc (φ - t) (φ + t) := fun hmem => hθne (le_antisymm hmem.2 (le_of_lt h1))
      simp [hnot]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]
  rw [hsplit1, hsplit2, hz_left, hz_right, zero_add,
    intervalIntegral.integral_congr hpt, add_zero]

end N11Formalization
