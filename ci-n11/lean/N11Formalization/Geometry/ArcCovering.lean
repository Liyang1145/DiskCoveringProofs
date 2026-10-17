/-
n=11 全局最优性形式化 —— 弧覆盖计数桥 ArcCovering（kernel-checked）

本文件把 (c)（cap = 半平面截圆）与 (a)（`arcsin (19/50) < π/8`）连成**计数定理**：

  `theorem card_mul_two_arcsin_ge_two_pi`：
  若有限个（任意中心 `c : ι → Point`、任意半径 `0 ≤ r < 1`）等半径闭盘覆盖单位圆周，
  则 `2π ≤ #ι * (2 * arcsin r)`。
  特别地 m 个半径 r 的闭盘覆盖单位圆至少需要 `r ≥ sin (π / m)`
  （这正是圆被 m 个闭盘覆盖的已知最优半径，故本界是 sharp 的）。

推论 `not_eight_ball_covers_of_lt_R0`：`r < R0 = 19/50` 时 8 个闭盘不可能覆盖单位圆周
（用 (a) 的 `8 * arcsin (19/50) < π`）。这是主装配（UNRESTRICTED-PROOF-ASSEMBLY §1）
所需的那一步。

技术路线（不引入角度类型、不引入圆上的测度论）：
* 用参数化 `circleMap t = !₂[cos t, sin t]` 把问题拉回实轴；
* `exists_abs_sub_two_pi_mul_int_le`：`cos δ ≤ cos x`（`0 ≤ δ ≤ π`）⟹ 圆距离 `≤ δ`（用 `Int.floor` 取代表元）；
* `volume_cos_ge_le`：`{t ∈ (0,2π) : cos δ ≤ cos (t-θ)}`（`θ ∈ (-π, π]`、`0 ≤ δ ≤ π/2`）的 Lebesgue 测度 ≤ `2δ`；
* 每个 cap 的弧参数原像含于这样的集合（用 (c) + 方向角），于是
  `2π = vol (0,2π) ≤ Σ vol (A i) ≤ #ι * 2δ`。

零 `sorry`、零自定义 `axiom`。

文档：research-2026/n11-formalization/evidence/CAP-ARC-REDUCTION.md
-/
import Mathlib
import N11Formalization.Geometry.CapArc

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization

noncomputable section

open MeasureTheory

/-! ## 单位圆参数化 -/

/-- 单位圆参数化 `t ↦ (cos t, sin t)`。 -/
def circleMap (t : ℝ) : Point := !₂[Real.cos t, Real.sin t]

theorem circleMap_apply_zero (t : ℝ) : (circleMap t).ofLp 0 = Real.cos t := by
  simp [circleMap]

theorem circleMap_apply_one (t : ℝ) : (circleMap t).ofLp 1 = Real.sin t := by
  simp [circleMap]

/-- 参数化落在单位圆上。 -/
theorem circleMap_norm (t : ℝ) : ‖circleMap t‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [circleMap_apply_zero, circleMap_apply_one, Real.norm_eq_abs, sq_abs]
  rw [add_comm, Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- 参数化的 2π 周期性（与 `AddCircle` 约定一致，供下游复用）。 -/
theorem circleMap_add_two_pi (t : ℝ) : circleMap (t + 2 * Real.pi) = circleMap t := by
  have hc : Real.cos (t + 2 * Real.pi) = Real.cos t := by
    simpa using Real.cos_add_int_mul_two_pi t 1
  have hs : Real.sin (t + 2 * Real.pi) = Real.sin t := by
    simpa using Real.sin_add_int_mul_two_pi t 1
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [circleMap, hc, hs]

/-- 参数化的内积是夹角余弦：`⟪circleMap t, circleMap θ⟫ = cos (t - θ)`。 -/
theorem inner_circleMap (t θ : ℝ) : inner ℝ (circleMap t) (circleMap θ) = Real.cos (t - θ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, Fin.sum_univ_two, circleMap_apply_zero,
    circleMap_apply_one]
  rw [Real.cos_sub]; ring

/-- `x ∈ S¹` 的方向角（`Complex.arg`，落在 `(-π, π]`）。 -/
def circleAngle (x : Point) : ℝ := Complex.arg (Complex.mk (x.ofLp 0) (x.ofLp 1))

theorem circleAngle_mem_Ioc (x : Point) : circleAngle x ∈ Set.Ioc (-Real.pi) Real.pi :=
  Complex.arg_mem_Ioc _

/-- 参数化在单位圆上满射：每个单位向量都是 `circleMap θ`（用 `Complex.arg` 构造 `θ`）。 -/
theorem circleMap_circleAngle (x : Point) (hx : ‖x‖ = 1) : circleMap (circleAngle x) = x := by
  set z : ℂ := Complex.mk (x.ofLp 0) (x.ofLp 1) with hz
  have hsq : x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 = 1 := by
    have h' : ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 = 1 := by
      have h := EuclideanSpace.norm_eq (𝕜 := ℝ) x
      rw [hx, Fin.sum_univ_two] at h
      have h2 : (Real.sqrt (‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2)) ^ 2 = 1 := by
        rw [← h]; norm_num
      rwa [Real.sq_sqrt (by positivity)] at h2
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at h'
  have hzn : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ 2 = 1 := by
      have hsqz : Complex.normSq z = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 := by
        simp [Complex.normSq_apply, hz, sq]
      rw [Complex.sq_norm, hsqz]
      linarith [hsq]
    nlinarith [norm_nonneg z]
  have hne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzn
    linarith
  have hcos : Real.cos (circleAngle x) = x.ofLp 0 := by
    have := Complex.cos_arg hne
    rw [hzn, div_one] at this
    simpa [circleAngle, hz] using this
  have hsin : Real.sin (circleAngle x) = x.ofLp 1 := by
    have := Complex.sin_arg z
    rw [hzn, div_one] at this
    simpa [circleAngle, hz] using this
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [circleMap, hcos, hsin]

/-! ## 余弦界 ⟹ 圆距离界 -/

/-- **圆距离引理**：`0 ≤ δ ≤ π` 且 `cos δ ≤ cos x` 时，`x` 落在某个 `2πk` 的 `δ`-邻域内。 -/
theorem exists_abs_sub_two_pi_mul_int_le {x δ : ℝ} (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
    (h : Real.cos δ ≤ Real.cos x) : ∃ k : ℤ, |x - k * (2 * Real.pi)| ≤ δ := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have key : ∀ y : ℝ, -(Real.pi) ≤ y → y < Real.pi → Real.cos δ ≤ Real.cos y → |y| ≤ δ := by
    intro y hy1 hy2 hcos
    rw [abs_le]
    constructor
    · by_contra hc
      rw [not_le] at hc
      have hz0 : 0 ≤ -y := by linarith
      have hzπ : -y ≤ Real.pi := by linarith
      have hlt : δ < -y := by linarith
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hδ0 hzπ hlt
      rw [Real.cos_neg] at this
      linarith
    · by_contra hc
      rw [not_le] at hc
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hδ0 (le_of_lt hy2) hc
      linarith
  set n : ℤ := ⌊(x + Real.pi) / (2 * Real.pi)⌋ with hn
  have h1 : (n : ℝ) ≤ (x + Real.pi) / (2 * Real.pi) := by
    have := Int.floor_le ((x + Real.pi) / (2 * Real.pi))
    rwa [← hn] at this
  have h2 : (x + Real.pi) / (2 * Real.pi) < (n : ℝ) + 1 := by
    have := Int.lt_floor_add_one ((x + Real.pi) / (2 * Real.pi))
    rwa [← hn] at this
  have hle : n * (2 * Real.pi) ≤ x + Real.pi := by
    have := mul_le_mul_of_nonneg_right h1 h2π.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2π)] at this
  have hlt : x + Real.pi < (n + 1) * (2 * Real.pi) := by
    have := mul_lt_mul_of_pos_right h2 h2π
    rwa [div_mul_cancel₀ _ (ne_of_gt h2π)] at this
  refine ⟨n, ?_⟩
  have hy1 : -(Real.pi) ≤ x - n * (2 * Real.pi) := by linarith
  have hy2 : x - n * (2 * Real.pi) < Real.pi := by linarith
  have hcos' : Real.cos δ ≤ Real.cos (x - n * (2 * Real.pi)) := by
    rw [Real.cos_sub_int_mul_two_pi x n]; exact h
  exact key _ hy1 hy2 hcos'

/-! ## 每个 cap 的弧参数原像含于两个候选区间 -/

/-- `t` 在 `(0,2π)`、`θ ∈ (-π,π]`、`0 ≤ δ ≤ π/2` 时，`cos δ ≤ cos (t-θ)` 迫使
`t` 落在 `[θ-δ, θ+δ]` 或 `[θ+2π-δ, θ+2π+δ]`（`k=-1`、`|k|≥2` 均被排除）。 -/
theorem circle_preimage_subset {t θ δ : ℝ} (ht : t ∈ Set.Ioo 0 (2 * Real.pi))
    (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi / 2)
    (hcos : Real.cos δ ≤ Real.cos (t - θ)) :
    (t ∈ Set.Icc (θ - δ) (θ + δ)) ∨
      (t ∈ Set.Icc (θ + 2 * Real.pi - δ) (θ + 2 * Real.pi + δ)) := by
  have hδπ' : δ ≤ Real.pi := by linarith [Real.pi_pos]
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  obtain ⟨k, hk⟩ := exists_abs_sub_two_pi_mul_int_le hδ0 hδπ' hcos
  have hkabs : |((k : ℝ) * (2 * Real.pi))| ≤ δ + |t - θ| := by
    calc |(k : ℝ) * (2 * Real.pi)| = |(t - θ) - (t - θ - k * (2 * Real.pi))| := by ring_nf
      _ ≤ |t - θ| + |t - θ - k * (2 * Real.pi)| := abs_sub _ _
      _ ≤ |t - θ| + δ := by linarith
      _ = δ + |t - θ| := by ring
  have htb : |t - θ| < 3 * Real.pi := by
    rw [abs_lt]
    constructor
    · linarith [ht.1, hθ.2]
    · linarith [ht.2, hθ.1]
  have hklt : (k : ℝ) < 2 := by
    rw [abs_mul, abs_of_pos h2π] at hkabs
    have h4 : |(k : ℝ)| * (2 * Real.pi) < 2 * (2 * Real.pi) := by linarith
    have habs : |(k : ℝ)| < 2 := by nlinarith [Real.pi_pos]
    linarith [abs_nonneg (k : ℝ), le_abs_self (k : ℝ)]
  have hkgt : (-2 : ℝ) < (k : ℝ) := by
    rw [abs_mul, abs_of_pos h2π] at hkabs
    have habs : |(k : ℝ)| < 2 := by nlinarith [Real.pi_pos]
    linarith [neg_abs_le (k : ℝ)]
  have hk01 : k = -1 ∨ k = 0 ∨ k = 1 := by
    have h1 : k < 2 := by exact_mod_cast hklt
    have h2 : -2 < k := by exact_mod_cast hkgt
    omega
  rcases hk01 with rfl | rfl | rfl
  · exfalso
    have h2 := (abs_le.mp hk).2
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h2
    have : t ≤ θ + δ - 2 * Real.pi := by linarith
    linarith [ht.1, hθ.2]
  · left
    have h2 := (abs_le.mp hk)
    simp only [Int.cast_zero, zero_mul, sub_zero] at h2
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · right
    have h2 := (abs_le.mp hk)
    simp only [Int.cast_one, one_mul] at h2
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ## 测度界：`{t ∈ (0,2π) : cos δ ≤ cos (t-θ)}` 的 Lebesgue 测度 ≤ `2δ` -/

/-- **核心测度引理**。`θ ∈ (-π,π]`、`0 ≤ δ ≤ π/2` 时，一个角半宽 `δ` 的弧与 `(0,2π)` 的交
的 Lebesgue 测度不超过 `2δ`（弧可能跨过 `0`，故分三种情形处理）。 -/
theorem volume_cos_ge_le {θ δ : ℝ} (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (hδ0 : 0 ≤ δ)
    (hδπ : δ ≤ Real.pi / 2) :
    volume {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧ Real.cos δ ≤ Real.cos (t - θ)}
      ≤ ENNReal.ofReal (2 * δ) := by
  set S : Set ℝ := {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧ Real.cos δ ≤ Real.cos (t - θ)}
    with hS
  have hmain : ∀ t ∈ S, t ∈ Set.Icc (θ - δ) (θ + δ)
      ∨ t ∈ Set.Icc (θ + 2 * Real.pi - δ) (θ + 2 * Real.pi + δ) :=
    fun t ht => circle_preimage_subset ht.1 hθ hδ0 hδπ ht.2
  by_cases hcase : δ ≤ θ
  · -- Case A: `δ ≤ θ`：第二支不可能（下界 ≥ 2π > t）
    have hsub : S ⊆ Set.Icc (θ - δ) (θ + δ) := by
      rintro t ht
      obtain ⟨htlo, htup⟩ : 0 < t ∧ t < 2 * Real.pi := ht.1
      rcases hmain t ht with h | h
      · exact h
      · exfalso
        rw [Set.mem_Icc] at h
        linarith [h.1, htup, hcase]
    calc volume S ≤ volume (Set.Icc (θ - δ) (θ + δ)) := measure_mono hsub
      _ = ENNReal.ofReal (2 * δ) := by
          rw [Real.volume_Icc]; congr 1; ring
  · -- `θ < δ`
    have hcase' : θ < δ := not_le.mp hcase
    by_cases hθle : -δ ≤ θ
    · -- Case B: `-δ ≤ θ < δ`：`[θ-δ,θ+δ]` 截断为 `[0,θ+δ]`，第二支截断为 `[θ+2π-δ,2π]`
      have hsub : S ⊆ Set.Icc 0 (θ + δ) ∪ Set.Icc (θ + 2 * Real.pi - δ) (2 * Real.pi) := by
        rintro t ht
        obtain ⟨htlo, htup⟩ : 0 < t ∧ t < 2 * Real.pi := ht.1
        rcases hmain t ht with h | h
        · rw [Set.mem_Icc] at h
          exact Or.inl ⟨le_of_lt htlo, h.2⟩
        · rw [Set.mem_Icc] at h
          exact Or.inr ⟨h.1, le_of_lt htup⟩
      calc volume S
          ≤ volume (Set.Icc 0 (θ + δ) ∪ Set.Icc (θ + 2 * Real.pi - δ) (2 * Real.pi)) :=
            measure_mono hsub
        _ ≤ volume (Set.Icc 0 (θ + δ)) + volume (Set.Icc (θ + 2 * Real.pi - δ) (2 * Real.pi)) :=
            measure_union_le _ _
        _ = ENNReal.ofReal (2 * δ) := by
            rw [Real.volume_Icc, Real.volume_Icc]
            rw [show 2 * Real.pi - (θ + 2 * Real.pi - δ) = δ - θ by ring]
            rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
            congr 1; ring
    · -- Case C: `θ < -δ`：第一支截断为空，只剩第二支整段
      have hθlt : θ < -δ := not_le.mp hθle
      have hsub : S ⊆ Set.Icc (θ + 2 * Real.pi - δ) (θ + 2 * Real.pi + δ) := by
        rintro t ht
        obtain ⟨htlo, htup⟩ : 0 < t ∧ t < 2 * Real.pi := ht.1
        rcases hmain t ht with h | h
        · exfalso
          rw [Set.mem_Icc] at h
          linarith [h.2, htlo, hθlt]
        · exact h
      calc volume S ≤ volume (Set.Icc (θ + 2 * Real.pi - δ) (θ + 2 * Real.pi + δ)) :=
            measure_mono hsub
        _ = ENNReal.ofReal (2 * δ) := by
            rw [Real.volume_Icc]; congr 1; ring

/-! ## 单条弧形式：cap ⊂ 一条角半宽 `arcsin r` 的弧 -/

/-- **GUIDE §1 所需的那一句**：`r < 1`、`c ≠ 0` 时，`S¹ ∩ closedBall c r` 中每个点 `x`
的角坐标都落在「`c` 的方向角 `θ`」的 `arcsin r` 邻域内（模 `2π`）——
即这条 cap 含于**一条**角宽 `≤ 2 arcsin r` 的弧中。
`c = 0` 时 cap 为空（`r < 1`），故 `hc : c ≠ 0` 不损失一般性。 -/
theorem cap_subset_arc {c x : Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : ‖x‖ = 1)
    (hc : c ≠ 0) (h : dist x c ≤ r) :
    ∃ k : ℤ, |circleAngle x - circleAngle ((‖c‖)⁻¹ • c) - k * (2 * Real.pi)| ≤ Real.arcsin r := by
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hnorm : ‖(‖c‖)⁻¹ • c‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (ne_of_gt hs)]
  set θ : ℝ := circleAngle ((‖c‖)⁻¹ • c) with hθdef
  have hθ : circleMap θ = (‖c‖)⁻¹ • c := by
    rw [hθdef]; exact circleMap_circleAngle _ hnorm
  have hc_eq : c = ‖c‖ • circleMap θ := by
    rw [hθ, smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
  have hx' : circleMap (circleAngle x) = x := circleMap_circleAngle x hx
  have hinner : inner ℝ x c = ‖c‖ * Real.cos (circleAngle x - θ) := by
    have h1 : inner ℝ x c = inner ℝ (circleMap (circleAngle x)) (‖c‖ • circleMap θ) := by
      conv_lhs => rw [← hx', hc_eq]
    rw [h1, real_inner_smul_right, inner_circleMap]
  have hiff := (mem_sphere_closedBall_iff hr0 hx).mp h
  rw [hinner] at hiff
  have hnum : 0 ≤ 1 + ‖c‖ ^ 2 - r ^ 2 := by nlinarith
  have hden : (0 : ℝ) < 2 * ‖c‖ := by linarith
  have hτ : (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) ≤ Real.cos (circleAngle x - θ) := by
    rw [div_le_iff₀ hden]
    linarith
  have hτ0 : 0 ≤ (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) := div_nonneg hnum hden.le
  have hsqrt : Real.sqrt (1 - r ^ 2) ≤ (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) := by
    have hden2 : (0 : ℝ) < (2 * ‖c‖) ^ 2 := by nlinarith [hs]
    have hsq : (Real.sqrt (1 - r ^ 2)) ^ 2
        ≤ ((1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖)) ^ 2 := by
      rw [Real.sq_sqrt (by nlinarith), div_pow, le_div_iff₀ hden2]
      nlinarith [sq_nonneg (‖c‖ ^ 2 - (1 - r ^ 2))]
    have h2 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hτ0] at h2
  have hcos : Real.cos (Real.arcsin r) ≤ Real.cos (circleAngle x - θ) := by
    rw [Real.cos_arcsin]
    linarith
  exact exists_abs_sub_two_pi_mul_int_le (Real.arcsin_nonneg.mpr hr0)
    (le_trans (Real.arcsin_le_pi_div_two r) (by linarith [Real.pi_pos])) hcos

/-! ## 计数定理 -/

/-- **弧覆盖计数（sharp 形式）**：任意有限个等半径闭盘覆盖单位圆周 ⟹
`2π ≤ #ι * (2 arcsin r)`。等价地 `r ≥ sin (π / #ι)`。 -/
theorem card_mul_two_arcsin_ge_two_pi {ι : Type*} [Fintype ι] (c : ι → Point) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ i, dist x (c i) ≤ r) :
    2 * Real.pi ≤ (Fintype.card ι : ℝ) * (2 * Real.arcsin r) := by
  set δ : ℝ := Real.arcsin r with hδdef
  have hδ0 : 0 ≤ δ := Real.arcsin_nonneg.mpr hr0
  have hδ2 : δ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two r
  have hcosδ : Real.cos δ = Real.sqrt (1 - r ^ 2) := by rw [hδdef, Real.cos_arcsin]
  set A : ι → Set ℝ := fun i => {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧
    dist (circleMap t) (c i) ≤ r} with hA
  have hbound : ∀ i, volume (A i) ≤ ENNReal.ofReal (2 * δ) := by
    intro i
    rcases eq_or_ne (c i) 0 with hzero | hne
    · have hempty : A i = ∅ := by
        ext t
        constructor
        · rintro ⟨-, hd⟩
          rw [hzero, dist_zero_right, circleMap_norm] at hd
          linarith
        · intro h
          exact absurd h (Set.notMem_empty t)
      rw [hempty, measure_empty]
      exact bot_le
    · have hs : 0 < ‖c i‖ := norm_pos_iff.mpr hne
      have hnorm : ‖(‖c i‖)⁻¹ • c i‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (ne_of_gt hs)]
      set θ : ℝ := circleAngle ((‖c i‖)⁻¹ • c i) with hθdef
      have hθmem : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
        rw [hθdef]; exact circleAngle_mem_Ioc _
      have hθ : circleMap θ = (‖c i‖)⁻¹ • c i := by
        rw [hθdef]; exact circleMap_circleAngle _ hnorm
      have hc_eq : c i = ‖c i‖ • circleMap θ := by
        rw [hθ, smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      have hsub : A i ⊆ {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧
          Real.cos δ ≤ Real.cos (t - θ)} := by
        rintro t ⟨htI, hd⟩
        refine ⟨htI, ?_⟩
        have h1 : inner ℝ (circleMap t) (c i)
            = inner ℝ (circleMap t) (‖c i‖ • circleMap θ) := by
          conv_lhs => rw [hc_eq]
        have hinner : inner ℝ (circleMap t) (c i) = ‖c i‖ * Real.cos (t - θ) := by
          rw [h1, real_inner_smul_right, inner_circleMap]
        have hiff := (mem_sphere_closedBall_iff hr0 (circleMap_norm t)).mp hd
        rw [hinner] at hiff
        have hnum : 0 ≤ 1 + ‖c i‖ ^ 2 - r ^ 2 := by nlinarith
        have hden : (0 : ℝ) < 2 * ‖c i‖ := by linarith
        have hτ0 : 0 ≤ (1 + ‖c i‖ ^ 2 - r ^ 2) / (2 * ‖c i‖) := div_nonneg hnum hden.le
        have hτ : (1 + ‖c i‖ ^ 2 - r ^ 2) / (2 * ‖c i‖) ≤ Real.cos (t - θ) := by
          rw [div_le_iff₀ hden]
          linarith
        have hsqrt : Real.sqrt (1 - r ^ 2) ≤ (1 + ‖c i‖ ^ 2 - r ^ 2) / (2 * ‖c i‖) := by
          have hden2 : (0 : ℝ) < (2 * ‖c i‖) ^ 2 := by nlinarith [hs]
          have hsq : (Real.sqrt (1 - r ^ 2)) ^ 2
              ≤ ((1 + ‖c i‖ ^ 2 - r ^ 2) / (2 * ‖c i‖)) ^ 2 := by
            rw [Real.sq_sqrt (by nlinarith), div_pow, le_div_iff₀ hden2]
            nlinarith [sq_nonneg (‖c i‖ ^ 2 - (1 - r ^ 2))]
          have h2 := sq_le_sq.mp hsq
          rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hτ0] at h2
        rw [hcosδ]
        linarith
      calc volume (A i)
          ≤ volume {t : ℝ | t ∈ Set.Ioo 0 (2 * Real.pi) ∧
              Real.cos δ ≤ Real.cos (t - θ)} := measure_mono hsub
        _ ≤ ENNReal.ofReal (2 * δ) := volume_cos_ge_le hθmem hδ0 hδ2
  have hcover : Set.Ioo 0 (2 * Real.pi) ⊆ ⋃ i, A i := by
    intro t ht
    obtain ⟨i, hi⟩ := hcov (circleMap t) (circleMap_norm t)
    exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩
  have hchain : ENNReal.ofReal (2 * Real.pi)
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * δ)) := by
    calc ENNReal.ofReal (2 * Real.pi) = volume (Set.Ioo 0 (2 * Real.pi)) := by
          rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume (⋃ i, A i) := measure_mono hcover
      _ ≤ ∑ i, volume (A i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : ι, ENNReal.ofReal (2 * δ) := Finset.sum_le_sum fun i _ => hbound i
      _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * δ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have := (ENNReal.ofReal_le_ofReal_iff (by
    have : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    nlinarith [this, hδ0])).mp hchain
  rw [hδdef] at this
  exact this

/-- 覆盖**闭单位圆盘**（而不只是圆周）的版本：直接由圆周覆盖得到。 -/
theorem card_mul_two_arcsin_ge_two_pi_of_covers_disk {ι : Type*} [Fintype ι] (c : ι → Point)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcov : ∀ x : Point, ‖x‖ ≤ 1 → ∃ i, dist x (c i) ≤ r) :
    2 * Real.pi ≤ (Fintype.card ι : ℝ) * (2 * Real.arcsin r) :=
  card_mul_two_arcsin_ge_two_pi c hr0 hr1 fun x hx => hcov x (le_of_eq hx)

/-- 8 个半径 `r < R0 = 19/50` 的闭盘不可能覆盖单位圆周（用 (a) 的 `8 arcsin R0 < π`）。 -/
theorem not_eight_ball_covers_circle_of_lt_R0 (c : Fin 8 → Point) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < (19 : ℝ) / 50) (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ i, dist x (c i) ≤ r) : False := by
  have hr1 : r < 1 := by linarith
  have h8 := card_mul_two_arcsin_ge_two_pi c hr0 hr1 hcov
  rw [Fintype.card_fin] at h8
  norm_num at h8
  have hmono : Real.arcsin r < Real.arcsin ((19 : ℝ) / 50) :=
    Real.arcsin_lt_arcsin (by linarith) hr (by norm_num)
  have hlt : (16 : ℝ) * Real.arcsin r < 2 * Real.pi := by
    have := eight_mul_arcsin_R0_lt_pi
    linarith
  linarith

/-- 覆盖单位闭圆盘的 8 盘版本。 -/
theorem not_eight_ball_covers_disk_of_lt_R0 (c : Fin 8 → Point) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < (19 : ℝ) / 50)
    (hcov : ∀ x : Point, ‖x‖ ≤ 1 → ∃ i, dist x (c i) ≤ r) : False :=
  not_eight_ball_covers_circle_of_lt_R0 c hr0 hr fun x hx => hcov x (le_of_eq hx)

/-- **主装配所需的形式**：`r < R0 = 19/50` 时，覆盖单位圆周的等半径闭盘个数至少 9。 -/
theorem nine_le_card_of_covers_circle_of_lt_R0 {ι : Type*} [Fintype ι] (c : ι → Point) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < (19 : ℝ) / 50)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ i, dist x (c i) ≤ r) : 9 ≤ Fintype.card ι := by
  have hr1 : r < 1 := by linarith
  have hmain := card_mul_two_arcsin_ge_two_pi c hr0 hr1 hcov
  have hmono : Real.arcsin r < Real.pi / 8 :=
    lt_trans (Real.arcsin_lt_arcsin (by linarith) hr (by norm_num)) arcsin_R0_lt_pi_div_eight
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [hmain, Real.pi_pos, Real.arcsin_nonneg.mpr hr0]
  have hlt : 2 * Real.pi < (Fintype.card ι : ℝ) * (Real.pi / 4) := by
    nlinarith [hmain, hmono, hpos]
  have h8 : (8 : ℝ) < (Fintype.card ι : ℝ) := by nlinarith [hlt, Real.pi_pos]
  have h8' : 8 < Fintype.card ι := by exact_mod_cast h8
  omega

/-- 覆盖单位**闭圆盘**的版本：`r < R0` 时至少需要 9 个等半径闭盘。 -/
theorem nine_le_card_of_covers_disk_of_lt_R0 {ι : Type*} [Fintype ι] (c : ι → Point) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < (19 : ℝ) / 50)
    (hcov : ∀ x : Point, ‖x‖ ≤ 1 → ∃ i, dist x (c i) ≤ r) : 9 ≤ Fintype.card ι :=
  nine_le_card_of_covers_circle_of_lt_R0 c hr0 hr fun x hx => hcov x (le_of_eq hx)

end

/-! ## 可信基础：公理依赖 -/

#print axioms N11Formalization.circleMap_norm
#print axioms N11Formalization.exists_abs_sub_two_pi_mul_int_le
#print axioms N11Formalization.cap_subset_arc
#print axioms N11Formalization.volume_cos_ge_le
#print axioms N11Formalization.card_mul_two_arcsin_ge_two_pi
#print axioms N11Formalization.not_eight_ball_covers_circle_of_lt_R0
#print axioms N11Formalization.nine_le_card_of_covers_circle_of_lt_R0
#print axioms N11Formalization.nine_le_card_of_covers_disk_of_lt_R0

end N11Formalization
