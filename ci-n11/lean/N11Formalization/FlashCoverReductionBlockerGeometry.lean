/-
# FlashCoverReductionBlockerGeometry — 单竞争者几何判据的真实消费者

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。
**前置**：`FlashCoverReductionBlocker.lean`（scalar 内核，已冻结）。

## 本文件显式导出的东西（不留黑箱）

1. `norm_sq_eq_tau_sq_add`：`X = M + τ•u`、`M = ½(A+C)`、`u ⊥ (C−A)`、`‖u‖ = 1`
   ⇒ `‖X−A‖² = τ² + ‖C−A‖²/4`。
2. `abs_tau_le_sqrt`：进一步 `‖X−A‖ ≤ r ⇒ |τ| ≤ √(r² − ‖C−A‖²/4)`。
3. `sub_midpoint_orthogonal_of_equidistant`：`‖X−A‖ = ‖X−C‖ ⇒ ⟪X−M, C−A⟫ = 0`。
4. `parallel_of_orthogonal`：2D 一维性（**用 finrank 证，不用坐标/sorry**）：
   `u ≠ 0`、`w ≠ 0`、`⟪u,w⟫ = 0`、`⟪v,w⟫ = 0` ⇒ `∃τ, v = τ•u`。
5. `equidistant_representation`：把参数化**导出**为结论——
   `A ≠ C`、`‖u‖ = 1`、`u ⊥ (C−A)`、`‖X−A‖ = ‖X−C‖` ⇒ `∃τ, X = M + τ•u`。

**声明**：本文件只证欧氏恒等式与表示式，**不**断言任何覆盖/图/弦事实。
-/

import Mathlib
import N11Formalization.Definitions

namespace N11Formalization

-- simp only 清单在多个证明间复用，个别条目在某些证明里用不到；关掉该 linter 以免噪声。
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace

/-! ## 0. 冻结内核的**镜像**（standalone 检查需要，避免 olean 依赖）

下面这条与 `FlashCoverReductionBlocker.lean` 中**同名同陈述**的定理一致；
此处重复证一遍只为让本文件可独立 `lake env lean`（该文件的 olean 由 lead 构建）。
**若冻结文件修改，这里必须同步。** -/

/-- 镜像：`(∃ τ, |τ| ≤ t ∧ 2τb ≤ c) ↔ 0 ≤ c + 2t|b|`。 -/
theorem exists_tau_mul_le_iff' {t c b : ℝ} (ht : 0 ≤ t) :
    (∃ τ : ℝ, |τ| ≤ t ∧ 2 * τ * b ≤ c) ↔ 0 ≤ c + 2 * t * |b| := by
  constructor
  · rintro ⟨τ, hτ, hle⟩
    have h1 : |τ * b| ≤ t * |b| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hτ (abs_nonneg b)
    have h2 : -(t * |b|) ≤ τ * b := neg_le_of_abs_le h1
    linarith
  · intro h
    rcases lt_trichotomy b 0 with hb | hb | hb
    · refine ⟨t, ?_, ?_⟩
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg hb] at h
        linarith
    · refine ⟨0, ?_, ?_⟩
      · simpa using ht
      · rw [hb] at h
        simpa using h
    · refine ⟨-t, ?_, ?_⟩
      · rw [abs_neg, abs_of_nonneg ht]
      · rw [abs_of_pos hb] at h
        linarith

/-- 镜像：范数平方差恒等式。 -/
theorem norm_sub_sq_sub_norm_sub_sq' (x a b : Point) :
    ‖x - a‖ ^ 2 - ‖x - b‖ ^ 2 = ‖a‖ ^ 2 - ‖b‖ ^ 2 + 2 * (inner ℝ x (b - a) : ℝ) := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  ring

/-- 镜像：平分线差式（`c0 − 2τb_⟂` 形式）。 -/
theorem bisector_difference' {a c b M u : Point} {τ : ℝ}
    (hM : M = (2 : ℝ)⁻¹ • (a + c)) :
    ‖(M + τ • u) - b‖ ^ 2 - ‖(M + τ • u) - a‖ ^ 2 =
      (‖b - M‖ ^ 2 - ‖c - a‖ ^ 2 / 4) - 2 * τ * (inner ℝ u (b - a) : ℝ) := by
  subst hM
  simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    smul_add, smul_smul, real_inner_self_eq_norm_sq, real_inner_comm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  ring

/-- 镜像：平分线等距。 -/
theorem bisector_equidistant' {a c M u : Point} {τ : ℝ}
    (hM : M = (2 : ℝ)⁻¹ • (a + c)) (hu : (inner ℝ u (c - a) : ℝ) = 0) :
    ‖(M + τ • u) - a‖ = ‖(M + τ • u) - c‖ := by
  have hu' : (inner ℝ (c - a) u : ℝ) = 0 := by rw [real_inner_comm]; exact hu
  have hzero : ‖(M + τ • u) - a‖ ^ 2 - ‖(M + τ • u) - c‖ ^ 2 = 0 := by
    subst hM
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      smul_add, smul_smul, real_inner_self_eq_norm_sq, real_inner_comm, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    have hcu : (inner ℝ c u : ℝ) = inner ℝ a u := by
      have h := hu'
      rw [inner_sub_left] at h
      linarith
    ring_nf
    linear_combination (2 * τ) * hcu
  have hsq : ‖(M + τ • u) - a‖ ^ 2 = ‖(M + τ • u) - c‖ ^ 2 := sub_eq_zero.mp hzero
  have h1 : (0 : ℝ) ≤ ‖(M + τ • u) - a‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖(M + τ • u) - c‖ := norm_nonneg _
  nlinarith [hsq, h1, h2, sq_nonneg (‖(M + τ • u) - a‖ - ‖(M + τ • u) - c‖)]

/-! ## 1–2. 参数化见证的范数平方与 τ 界 -/

/-- 平分线参数化下的范数平方：`‖X−A‖² = τ² + ‖C−A‖²/4`。 -/
theorem norm_sq_eq_tau_sq_add {A C M u X : Point} {τ : ℝ}
    (hM : M = (2 : ℝ)⁻¹ • (A + C)) (hX : X = M + τ • u)
    (hu1 : ‖u‖ = 1) (hu : (inner ℝ u (C - A) : ℝ) = 0) :
    ‖X - A‖ ^ 2 = τ ^ 2 + ‖C - A‖ ^ 2 / 4 := by
  subst hM
  subst hX
  have hsplit : (2 : ℝ)⁻¹ • (A + C) + τ • u - A = (2 : ℝ)⁻¹ • (C - A) + τ • u := by
    module
  rw [hsplit, norm_add_sq_real]
  have horth : (inner ℝ ((2 : ℝ)⁻¹ • (C - A)) (τ • u) : ℝ) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm u (C - A), hu]
    ring
  rw [horth, norm_smul, norm_smul, hu1,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
    Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- **τ 界**：`‖X−A‖ ≤ r ⇒ |τ| ≤ √(r² − ‖C−A‖²/4)`。 -/
theorem abs_tau_le_sqrt {A C M u X : Point} {τ r : ℝ}
    (hM : M = (2 : ℝ)⁻¹ • (A + C)) (hX : X = M + τ • u)
    (hu1 : ‖u‖ = 1) (hu : (inner ℝ u (C - A) : ℝ) = 0)
    (hr : ‖X - A‖ ≤ r) :
    |τ| ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) := by
  have hsq := norm_sq_eq_tau_sq_add hM hX hu1 hu
  have hτ : τ ^ 2 ≤ r ^ 2 - ‖C - A‖ ^ 2 / 4 := by
    have h2 : ‖X - A‖ ^ 2 ≤ r ^ 2 := by nlinarith [hr, norm_nonneg (X - A)]
    linarith [hsq, h2]
  have hnn : 0 ≤ r ^ 2 - ‖C - A‖ ^ 2 / 4 := by linarith [hτ, sq_nonneg τ]
  have h3 : τ ^ 2 ≤ (Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)) ^ 2 := by
    rw [Real.sq_sqrt hnn]; exact hτ
  have h4 : |τ| ≤ |Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)| := sq_le_sq.mp h3
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h4

/-! ## 3. 等距 ⇒ 垂直中点的连线 -/

/-- `‖X−A‖ = ‖X−C‖ ⇒ ⟪X−M, C−A⟫ = 0`（`M = ½(A+C)`）。 -/
theorem sub_midpoint_orthogonal_of_equidistant {A C M X : Point}
    (hM : M = (2 : ℝ)⁻¹ • (A + C)) (h : ‖X - A‖ = ‖X - C‖) :
    (inner ℝ (X - M) (C - A) : ℝ) = 0 := by
  have hsq : ‖X - A‖ ^ 2 = ‖X - C‖ ^ 2 := by rw [h]
  have hsub : ‖X - A‖ ^ 2 - ‖X - C‖ ^ 2 = 0 := sub_eq_zero.mpr hsq
  rw [norm_sub_sq_sub_norm_sub_sq' X A C] at hsub
  have h1 : (inner ℝ X (C - A) : ℝ) = ‖C‖ ^ 2 / 2 - ‖A‖ ^ 2 / 2 := by linarith [hsub]
  have h2 : (inner ℝ ((2 : ℝ)⁻¹ • (A + C)) (C - A) : ℝ) = ‖C‖ ^ 2 / 2 - ‖A‖ ^ 2 / 2 := by
    simp only [real_inner_smul_left, inner_add_left, inner_sub_right,
      real_inner_comm C A, real_inner_self_eq_norm_sq]
    ring
  subst hM
  rw [inner_sub_left]
  linarith [h1, h2]

/-! ## 4. 2D 一维性（finrank 证明） -/

/-- **平行引理**：`u ≠ 0`、`w ≠ 0`、`⟪u,w⟫ = 0`、`⟪v,w⟫ = 0` ⇒ `∃τ, v = τ•u`。

证明用维度：`ℝ∙u ≤ (ℝ∙w)ᗮ`，两边 finrank 都是 1（后者由
`finrank_add_finrank_orthogonal` 与 `finrank (EuclideanSpace ℝ (Fin 2)) = 2` 得），
故相等，`v` 落在其中。 -/
theorem parallel_of_orthogonal {u w v : Point} (hu : u ≠ 0) (hw0 : w ≠ 0)
    (huw : (inner ℝ u w : ℝ) = 0) (hvw : (inner ℝ v w : ℝ) = 0) :
    ∃ τ : ℝ, v = τ • u := by
  have hmem : ∀ x : Point, (inner ℝ x w : ℝ) = 0 → x ∈ (ℝ ∙ w)ᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [real_inner_smul_left]
    have hwx : (inner ℝ w x : ℝ) = 0 := by
      rw [real_inner_comm]
      exact hx
    rw [hwx, mul_zero]
  have hu_mem : u ∈ (ℝ ∙ w)ᗮ := hmem u huw
  have hv_mem : v ∈ (ℝ ∙ w)ᗮ := hmem v hvw
  have hle : ℝ ∙ u ≤ (ℝ ∙ w)ᗮ := (Submodule.span_singleton_le_iff_mem u _).mpr hu_mem
  have hfr_u : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu
  have hfr_w : Module.finrank ℝ (ℝ ∙ w) = 1 := finrank_span_singleton hw0
  have hfr_E : Module.finrank ℝ Point = 2 := by
    rw [finrank_euclideanSpace]; norm_num
  have hfr_orth : Module.finrank ℝ (ℝ ∙ w)ᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ w : Submodule ℝ Point)
    omega
  have heq : ℝ ∙ u = (ℝ ∙ w)ᗮ :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr_u, hfr_orth])
  have hv' : v ∈ ℝ ∙ u := heq ▸ hv_mem
  obtain ⟨τ, hτ⟩ := Submodule.mem_span_singleton.mp hv'
  exact ⟨τ, hτ.symm⟩

/-! ## 5. 等距线上任意点的参数化表示 -/

/-- **表示定理**：`A ≠ C`、`‖u‖ = 1`、`u ⊥ (C−A)`、`‖X−A‖ = ‖X−C‖`
⇒ `∃τ, X = M + τ•u`（参数化是**结论**，不是前提）。 -/
theorem equidistant_representation {A C M u X : Point}
    (hAC : A ≠ C) (hM : M = (2 : ℝ)⁻¹ • (A + C))
    (hu1 : ‖u‖ = 1) (hu : (inner ℝ u (C - A) : ℝ) = 0)
    (h : ‖X - A‖ = ‖X - C‖) :
    ∃ τ : ℝ, X = M + τ • u := by
  have hw0 : C - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAC)
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu1
    norm_num at hu1
  have hperp : (inner ℝ (X - M) (C - A) : ℝ) = 0 :=
    sub_midpoint_orthogonal_of_equidistant hM h
  obtain ⟨τ, hτ⟩ := parallel_of_orthogonal hu_ne hw0 hu hperp
  exact ⟨τ, by rw [← hτ]; abel⟩

/-! ## 6. **完整单竞争者几何判据**（本文件的数学 stop）

`A`、`C` 是两步对；`B` 是竞争者；`M = ½(A+C)`；`u` 是 A–C 平分线单位方向。
则"平分线上存在一个 `A` 最不弱于 `B` 且 `‖·−A‖ ≤ r` 的点"**当且仅当**
```
‖C−A‖ ≤ 2r      且      0 ≤ (‖B−M‖² − ‖C−A‖²/4) + 2·√(r² − ‖C−A‖²/4)·|⟪u, B−A⟫|
```
- 左端 `∃X`：`X` 到 `A`、`C` 等距、在 `A` 的 r 邻域内、且 `A` 不弱于 `B`。
- `‖C−A‖ ≤ 2r` 这一项**不可省**：`d > 2r` 时透镜为空（`Real.sqrt` 的参数为负取 0），
  单靠符号式会误判可行。
- 参数化 `X = M + τ•u` 由 §5 **导出**（不是前提）；`r ≥ 0` 由 `d ≤ 2r` 推出。

**声明**：这是单竞争者的完整判据；它**不**断言"多站点同时最近"或任何覆盖/弦事实。
-/
theorem single_competitor_criterion {A C B M u : Point} {r : ℝ}
    (hAC : A ≠ C) (hM : M = (2 : ℝ)⁻¹ • (A + C)) (hu1 : ‖u‖ = 1)
    (hu : (inner ℝ u (C - A) : ℝ) = 0) :
    (∃ X : Point, ‖X - A‖ = ‖X - C‖ ∧ ‖X - A‖ ≤ r ∧ ‖X - A‖ ≤ ‖X - B‖)
      ↔ ‖C - A‖ ≤ 2 * r ∧
        0 ≤ (‖B - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4) +
            2 * Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) * |(inner ℝ u (B - A) : ℝ)| := by
  have hd : 0 ≤ ‖C - A‖ := norm_nonneg _
  constructor
  · -- (⇒)
    rintro ⟨X, heq, hrX, hleXB⟩
    have h2r : ‖C - A‖ ≤ 2 * r := by
      have h1 : ‖C - A‖ ≤ ‖C - X‖ + ‖X - A‖ := by
        have h := norm_add_le (C - X) (X - A)
        rwa [show C - X + (X - A) = C - A by abel] at h
      have h2 : ‖C - X‖ = ‖X - A‖ := by rw [norm_sub_rev, heq]
      linarith
    obtain ⟨τ, hXτ⟩ := equidistant_representation hAC hM hu1 hu heq
    have hτ := abs_tau_le_sqrt hM hXτ hu1 hu hrX
    have hdiff : ‖M + τ • u - B‖ ^ 2 - ‖M + τ • u - A‖ ^ 2 =
        (‖B - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4) - 2 * τ * (inner ℝ u (B - A) : ℝ) :=
      bisector_difference' (a := A) (c := C) (b := B) (M := M) (u := u) (τ := τ) hM
    have hc0 : 2 * τ * (inner ℝ u (B - A) : ℝ) ≤ ‖B - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4 := by
      have h1 : ‖X - B‖ ^ 2 - ‖X - A‖ ^ 2 ≥ 0 := by
        nlinarith [norm_nonneg (X - B), norm_nonneg (X - A), hleXB]
      rw [hXτ] at h1
      linarith [hdiff, h1]
    exact ⟨h2r, (exists_tau_mul_le_iff' (Real.sqrt_nonneg _)).mp ⟨τ, hτ, hc0⟩⟩
  · -- (⇐)
    rintro ⟨h2r, hsign⟩
    have hr : 0 ≤ r := by linarith [hd, h2r]
    have hnn : 0 ≤ r ^ 2 - ‖C - A‖ ^ 2 / 4 := by nlinarith [hd, hr, h2r]
    have htsq : Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) ^ 2 = r ^ 2 - ‖C - A‖ ^ 2 / 4 :=
      Real.sq_sqrt hnn
    obtain ⟨τ, hτ, hc0⟩ := (exists_tau_mul_le_iff' (t := Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4))
      (c := ‖B - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4) (b := (inner ℝ u (B - A) : ℝ))
      (Real.sqrt_nonneg _)).mpr hsign
    refine ⟨M + τ • u, bisector_equidistant' hM hu, ?_, ?_⟩
    · have hsq := norm_sq_eq_tau_sq_add hM (rfl : M + τ • u = M + τ • u) hu1 hu
      have ht0 : (0 : ℝ) ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) := Real.sqrt_nonneg _
      have htau2 : τ ^ 2 ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) ^ 2 := by
        have h1 : |τ| ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) := hτ
        have h2 : |τ| ≤ |Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)| := by rwa [abs_of_nonneg ht0]
        simpa [sq_abs] using sq_le_sq.mpr h2
      have hle : ‖M + τ • u - A‖ ^ 2 ≤ r ^ 2 := by rw [hsq]; linarith [htau2, htsq]
      nlinarith [norm_nonneg (M + τ • u - A), hle]
    · have hdiff : ‖M + τ • u - B‖ ^ 2 - ‖M + τ • u - A‖ ^ 2 =
          (‖B - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4) - 2 * τ * (inner ℝ u (B - A) : ℝ) :=
        bisector_difference' (a := A) (c := C) (b := B) (M := M) (u := u) (τ := τ) hM
      have hge : ‖M + τ • u - B‖ ^ 2 - ‖M + τ • u - A‖ ^ 2 ≥ 0 := by
        rw [hdiff]; linarith
      nlinarith [norm_nonneg (M + τ • u - B), norm_nonneg (M + τ • u - A), hge]

/-! ## 7. 多竞争者：有限 1D Helly + 1/2 见证者阻塞

每个竞争者 `k` 给半空间 `2τb_k ≤ c_k`（符号约定已核），加上环境 `−t ≤ τ ≤ t`。
把它们化归成 τ 轴上的区间 `[tauLo_k, tauHi_k]`，于是**共同**可行性 ⟺ 所有区间**两两**相容；
不可行时必由**一个**（`b_k = 0 ∧ c_k < 0`）或**两个**（`tauHi_l < tauLo_k`）竞争者见证。
**关键**：证的是**同一个** τ 同时满足所有约束；不允许把各 `k` 单独的 `∃τ` 拼起来。
-/

/-- 竞争者 `(b,c)` 与环境界合起来给出的 τ 区间**下界**。 -/
noncomputable def tauLo (b c t : ℝ) : ℝ := if b < 0 then max (c / (2 * b)) (-t) else -t

/-- 上界。 -/
noncomputable def tauHi (b c t : ℝ) : ℝ := if 0 < b then min (c / (2 * b)) t else t

/-- `b ≠ 0` 时，单个竞争者的约束集恰是区间 `[tauLo, tauHi]`。 -/
theorem iff_interval_of_competitor {b c t τ : ℝ} (hb : b ≠ 0) :
    (2 * τ * b ≤ c ∧ -t ≤ τ ∧ τ ≤ t) ↔ tauLo b c t ≤ τ ∧ τ ≤ tauHi b c t := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have h2b : 2 * b < 0 := by linarith
    have hb0 : ¬ (0 < b) := by linarith
    rw [tauLo, if_pos hneg, tauHi, if_neg hb0, max_le_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      rw [div_le_iff_of_neg h2b]
      linarith
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h2, h3⟩
      have h4 : τ * (2 * b) ≤ c := (div_le_iff_of_neg h2b).mp h1
      linarith
  · have h2b : 0 < 2 * b := by linarith
    have hb0 : ¬ (b < 0) := by linarith
    rw [tauLo, if_neg hb0, tauHi, if_pos hpos, le_min_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, ?_, h3⟩
      rw [le_div_iff₀ h2b]
      linarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h1, h3⟩
      have h4 : τ * (2 * b) ≤ c := (le_div_iff₀ h2b).mp h2
      linarith

/-- 约束在 `τ` 成立 ⇒ `tauLo ≤ τ`（`b ≠ 0`）。 -/
theorem tauLo_le_of {b c t τ : ℝ} (hb : b ≠ 0) (h : 2 * τ * b ≤ c) (hτ : -t ≤ τ) :
    tauLo b c t ≤ τ := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · rw [tauLo, if_pos hneg, max_le_iff]
    refine ⟨?_, hτ⟩
    rw [div_le_iff_of_neg (by linarith : 2 * b < 0)]
    linarith
  · rw [tauLo, if_neg (by linarith : ¬ b < 0)]
    exact hτ

/-- 约束在 `τ` 成立 ⇒ `τ ≤ tauHi`（`b ≠ 0`）。 -/
theorem le_tauHi_of {b c t τ : ℝ} (hb : b ≠ 0) (h : 2 * τ * b ≤ c) (hτ : τ ≤ t) :
    τ ≤ tauHi b c t := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · rw [tauHi, if_neg (by linarith : ¬ 0 < b)]
    exact hτ
  · rw [tauHi, if_pos hpos, le_min_iff]
    refine ⟨?_, hτ⟩
    rw [le_div_iff₀ (by linarith : 0 < 2 * b)]
    linarith

/-- 落在区间内 ⇒ 约束成立（`b ≠ 0`）。 -/
theorem sat_of_interval {b c t τ : ℝ} (hb : b ≠ 0)
    (hlo : tauLo b c t ≤ τ) (hhi : τ ≤ tauHi b c t) : 2 * τ * b ≤ c := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · rw [tauLo, if_pos hneg] at hlo
    have h1 : c / (2 * b) ≤ τ := le_trans (le_max_left _ _) hlo
    rw [div_le_iff_of_neg (by linarith : 2 * b < 0)] at h1
    linarith
  · rw [tauHi, if_pos hpos] at hhi
    have h1 : τ ≤ c / (2 * b) := le_trans hhi (min_le_left _ _)
    rw [le_div_iff₀ (by linarith : 0 < 2 * b)] at h1
    linarith

/-- **多竞争者共同可行性判据（有限 1D Helly）**：单个 τ 同时满足所有 `2τb_k ≤ c_k`
与 `−t ≤ τ ≤ t`，**当且仅当** `b_k = 0` 者都有 `c_k ≥ 0`，且所有区间对相容
（`∀ k l, tauLo_k ≤ tauHi_l`）。 -/
theorem joint_tau_iff {ι : Type*} [Fintype ι] [Nonempty ι] (b c : ι → ℝ) (t : ℝ) :
    (∃ τ : ℝ, -t ≤ τ ∧ τ ≤ t ∧ ∀ k, 2 * τ * b k ≤ c k)
      ↔ (∀ k, b k = 0 → 0 ≤ c k) ∧ ∀ k l, tauLo (b k) (c k) t ≤ tauHi (b l) (c l) t := by
  constructor
  · rintro ⟨τ, ht1, ht2, hk⟩
    refine ⟨?_, ?_⟩
    · intro k hk0
      have h := hk k
      rw [hk0] at h
      simpa using h
    · intro k l
      by_cases hbk : b k = 0
      · have hL : tauLo (b k) (c k) t = -t := by simp [tauLo, hbk]
        rw [hL]
        by_cases hbl : b l = 0
        · have hH : tauHi (b l) (c l) t = t := by simp [tauHi, hbl]
          rw [hH]; linarith
        · exact le_trans ht1 (le_tauHi_of hbl (hk l) ht2)
      · by_cases hbl : b l = 0
        · have hH : tauHi (b l) (c l) t = t := by simp [tauHi, hbl]
          rw [hH]; exact le_trans (tauLo_le_of hbk (hk k) ht1) ht2
        · exact le_trans (tauLo_le_of hbk (hk k) ht1) (le_tauHi_of hbl (hk l) ht2)
  · rintro ⟨hzero, hpair⟩
    obtain ⟨k₀, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun k => tauLo (b k) (c k) t) Finset.univ_nonempty
    refine ⟨tauLo (b k₀) (c k₀) t, ?_, ?_, ?_⟩
    · by_cases hb0 : b k₀ = 0
      · simp [tauLo, hb0]
      · rcases lt_or_gt_of_ne hb0 with hneg | hpos
        · rw [tauLo, if_pos hneg]; exact le_max_right _ _
        · rw [tauLo, if_neg (by linarith : ¬ b k₀ < 0)]
    · refine le_trans (hpair k₀ k₀) ?_
      by_cases hb0 : b k₀ = 0
      · simp [tauHi, hb0]
      · rcases lt_or_gt_of_ne hb0 with hneg | hpos
        · rw [tauHi, if_neg (by linarith : ¬ 0 < b k₀)]
        · rw [tauHi, if_pos hpos]; exact min_le_right _ _
    · intro k
      by_cases hbk : b k = 0
      · rw [hbk]; simpa using hzero k hbk
      · exact sat_of_interval hbk (hmax k (Finset.mem_univ k)) (hpair k₀ k)

/-- **阻塞见证（1 或 2 个竞争者）**：共同区间为空 ⇒ 要么某 `b_k = 0` 的竞争者 `c_k < 0`
（**单**竞争者阻塞），要么存在**一对** `(k,l)` 使 `tauHi_l < tauLo_k`（**两**竞争者阻塞）。 -/
theorem obstruction_pair {ι : Type*} [Fintype ι] [Nonempty ι] (b c : ι → ℝ) (t : ℝ)
    (h : ¬ ∃ τ : ℝ, -t ≤ τ ∧ τ ≤ t ∧ ∀ k, 2 * τ * b k ≤ c k) :
    (∃ k, b k = 0 ∧ c k < 0)
      ∨ ∃ k l, tauHi (b l) (c l) t < tauLo (b k) (c k) t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact h ((joint_tau_iff b c t).mpr ⟨fun k hk => h1 k hk, fun k l => h2 k l⟩)

/-! ## 8. **受限 Voronoi 透镜见证判据**（restricted Voronoi lens witness）

把 §6（单竞争者差式）与 §7（多竞争者 1D Helly）的记号对接：

* `compB A u B := ⟪u, B − A⟫`（判据里的 `b_k`）；
* `compC0 A C M B := ‖B − M‖² − ‖C−A‖²/4`（判据里的 `c_k`，恒等式 `= (B−A)·(B−C)`）。

**scope 措辞（lead 更正，已采纳）**：本定理断言的是**存在一个 `X`**，使
`‖X−A‖ = ‖X−C‖`（等距）、`‖X−A‖ ≤ r`、且 `A` 对所有竞争者 `cc k` 不弱。
这**不是** `cover-relevant`：还缺 (i) `X ∈ unitDisk`，(ii) "覆盖"那一半
（`‖X−A‖ ≤ r` 只说 `A` 距 `X` 在 `r` 内，不等于盘被覆盖）。这两项分别由
新文件里的 `unitDisk` 截线区间与既有覆盖结构承担；本定理本身不声称它们。
-/

/-- 竞争者 `B` 在判据里的系数 `b = ⟪u, B−A⟫`。 -/
noncomputable def compB (A u B : Point) : ℝ := (inner ℝ u (B - A) : ℝ)

/-- 竞争者 `B` 在判据里的常数 `c = ‖B−M‖² − ‖C−A‖²/4`（`= (B−A)·(B−C)`）。 -/
noncomputable def compC0 (A C M B : Point) : ℝ := ‖B - M‖ ^ 2 - ‖C - A‖ ^ 2 / 4

/-- **受限 Voronoi 透镜见证判据**。对 `A ≠ C`、`M = ½(A+C)`、单位 `u ⊥ (C−A)`：
```
(∃ X, ‖X−A‖ = ‖X−C‖ ∧ ‖X−A‖ ≤ r ∧ ∀k, ‖X−A‖ ≤ ‖X−cc k‖)
 ↔ ‖C−A‖ ≤ 2r ∧ (∀k, compB A u (cc k) = 0 → 0 ≤ compC0 A C M (cc k))
     ∧ (∀k l, tauLo (compB A u (cc k)) (compC0 A C M (cc k)) t
            ≤ tauHi (compB A u (cc l)) (compC0 A C M (cc l)) t)
```
其中 `t = √(r² − ‖C−A‖²/4)`。`r ≥ 0` 由 `‖C−A‖ ≤ 2r` 与 `‖C−A‖ ≥ 0` 显式推得
（`hr` 分支），不需要额外假设。 -/
theorem restricted_lens_witness_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (A C : Point) (cc : ι → Point) (r : ℝ) {M u : Point}
    (hAC : A ≠ C) (hM : M = (2 : ℝ)⁻¹ • (A + C)) (hu1 : ‖u‖ = 1)
    (hu : (inner ℝ u (C - A) : ℝ) = 0) :
    (∃ X : Point, ‖X - A‖ = ‖X - C‖ ∧ ‖X - A‖ ≤ r ∧ ∀ k, ‖X - A‖ ≤ ‖X - cc k‖)
      ↔ ‖C - A‖ ≤ 2 * r ∧
        (∀ k, compB A u (cc k) = 0 → 0 ≤ compC0 A C M (cc k)) ∧
        ∀ k l, tauLo (compB A u (cc k)) (compC0 A C M (cc k))
              (Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4))
            ≤ tauHi (compB A u (cc l)) (compC0 A C M (cc l))
              (Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)) := by
  have hd : 0 ≤ ‖C - A‖ := norm_nonneg _
  constructor
  · -- (⇒)
    rintro ⟨X, heq, hrX, hne⟩
    have h2r : ‖C - A‖ ≤ 2 * r := by
      have h1 : ‖C - A‖ ≤ ‖C - X‖ + ‖X - A‖ := by
        have h := norm_add_le (C - X) (X - A)
        rwa [show C - X + (X - A) = C - A by abel] at h
      have h2 : ‖C - X‖ = ‖X - A‖ := by rw [norm_sub_rev, heq]
      linarith
    obtain ⟨τ, hXτ⟩ := equidistant_representation hAC hM hu1 hu heq
    have hτ := abs_tau_le_sqrt hM hXτ hu1 hu hrX
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
    have ht0 : (0 : ℝ) ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) := Real.sqrt_nonneg _
    refine ⟨h2r, ?_, ?_⟩
    · intro k hk0
      have h := hsat k
      have hb : (inner ℝ u (cc k - A) : ℝ) = 0 := hk0
      rw [hb] at h
      simpa [compC0] using h
    · -- 两两相容：`tauLo_k ≤ τ ≤ tauHi_l`
      have hb1 : -Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) ≤ τ := (abs_le.mp hτ).1
      have hb2 : τ ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) := (abs_le.mp hτ).2
      intro k l
      have hLk : tauLo (compB A u (cc k)) (compC0 A C M (cc k))
          (Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)) ≤ τ := by
        by_cases hbk : compB A u (cc k) = 0
        · simp only [tauLo, hbk, lt_self_iff_false, ↓reduceIte]
          exact hb1
        · exact tauLo_le_of (c := compC0 A C M (cc k)) hbk (hsat k) hb1
      have hHl : τ ≤ tauHi (compB A u (cc l)) (compC0 A C M (cc l))
          (Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)) := by
        by_cases hbl : compB A u (cc l) = 0
        · simp only [tauHi, hbl, lt_self_iff_false, ↓reduceIte]
          exact hb2
        · exact le_tauHi_of (c := compC0 A C M (cc l)) hbl (hsat l) hb2
      exact le_trans hLk hHl
  · -- (⇐)
    rintro ⟨h2r, hzero, hpair⟩
    have hr : 0 ≤ r := by linarith [hd, h2r]
    have hnn : 0 ≤ r ^ 2 - ‖C - A‖ ^ 2 / 4 := by nlinarith [hd, hr, h2r]
    have htsq : Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) ^ 2 = r ^ 2 - ‖C - A‖ ^ 2 / 4 :=
      Real.sq_sqrt hnn
    obtain ⟨τ, ht1, ht2, hsat⟩ := (joint_tau_iff (fun k => compB A u (cc k))
      (fun k => compC0 A C M (cc k)) (Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4))).mpr
        ⟨fun k hk => hzero k hk, fun k l => hpair k l⟩
    have ht0 : (0 : ℝ) ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) := Real.sqrt_nonneg _
    have htau2 : τ ^ 2 ≤ Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4) ^ 2 := by
      have h2 : |τ| ≤ |Real.sqrt (r ^ 2 - ‖C - A‖ ^ 2 / 4)| := by
        rw [abs_of_nonneg ht0]
        exact abs_le.mpr ⟨ht1, ht2⟩
      simpa [sq_abs] using sq_le_sq.mpr h2
    refine ⟨M + τ • u, bisector_equidistant' hM hu, ?_, ?_⟩
    · have hsq := norm_sq_eq_tau_sq_add hM (rfl : M + τ • u = M + τ • u) hu1 hu
      have hle : ‖M + τ • u - A‖ ^ 2 ≤ r ^ 2 := by rw [hsq]; linarith [htau2, htsq]
      nlinarith [norm_nonneg (M + τ • u - A), hle]
    · intro k
      have hdiff := bisector_difference' (a := A) (c := C) (b := cc k) (M := M) (u := u) (τ := τ) hM
      have hnh : ‖M + τ • u - cc k‖ ^ 2 - ‖M + τ • u - A‖ ^ 2 ≥ 0 := by
        rw [hdiff]
        have := hsat k
        simp only [compB, compC0] at this
        linarith
      nlinarith [norm_nonneg (M + τ • u - cc k), norm_nonneg (M + τ • u - A), hnh]

/-! ## 9. 真实负控：**每条单独可行、但无共同 τ**（校准 ∃/∀ 接口）

数据（lead 指定）：`t = 1`、`b₀ = 1, c₀ = −1`、`b₁ = −1, c₁ = −1`。
- 竞争者 0：`2τ·1 ≤ −1 ⟺ τ ≤ −1/2` ⇒ `τ = −1/2` 可行；
- 竞争者 1：`2τ·(−1) ≤ −1 ⟺ τ ≥ 1/2` ⇒ `τ = 1/2` 可行；
- 但**没有**共同 τ（`τ ≤ −1/2` 与 `τ ≥ 1/2` 不相容）。

这校准的正是本路线最关键的一步：**"每个 k 单独 `∃τ`" 推不出 "共同 `∃τ`"**。 -/

/-- 负控的 `b` 族。 -/
def ncB : Fin 2 → ℝ := ![1, -1]

/-- 负控的 `c` 族。 -/
def ncC : Fin 2 → ℝ := ![-1, -1]

/-- 每个竞争者**单独**在 `|τ| ≤ 1` 内可行。 -/
theorem negcontrol_individual (k : Fin 2) :
    ∃ τ : ℝ, -1 ≤ τ ∧ τ ≤ 1 ∧ 2 * τ * ncB k ≤ ncC k := by
  fin_cases k
  · exact ⟨-1 / 2, by norm_num [ncB, ncC]⟩
  · exact ⟨1 / 2, by norm_num [ncB, ncC]⟩

/-- 但**不存在共同 τ**（逐 k 拼接是错的）。 -/
theorem negcontrol_no_common :
    ¬ ∃ τ : ℝ, -1 ≤ τ ∧ τ ≤ 1 ∧ ∀ k : Fin 2, 2 * τ * ncB k ≤ ncC k := by
  rintro ⟨τ, h1, h2, h3⟩
  have h0 := h3 0
  have h1' := h3 1
  simp only [ncB, ncC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1'
  norm_num at h0 h1'
  linarith

/-- §7 的判据与之一致：两两相容在 `(k,l) = (1,0)` 处失败。 -/
theorem negcontrol_pair_fails :
    ¬ (∀ k l : Fin 2, tauLo (ncB k) (ncC k) 1 ≤ tauHi (ncB l) (ncC l) 1) := by
  intro h
  have h10 := h 1 0
  simp only [ncB, ncC, tauLo, tauHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h10
  norm_num at h10

/-- 该阻塞是**两**竞争者型（与 `obstruction_pair` 的第二支相符）：
`tauHi_0 = −1/2 < 1/2 = tauLo_1`。 -/
theorem negcontrol_pair_witness :
    tauHi (ncB 0) (ncC 0) 1 < tauLo (ncB 1) (ncC 1) 1 := by
  simp only [ncB, ncC, tauLo, tauHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  norm_num

end N11Formalization
