/-
# FlashCoverReductionSinusoid — 圆上"线–圆至多两点"的核可形式

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。

## 内容与它在来源论证里的位置

源 `VORONOI-BOUNDARY-REDUCTION.md` §1 的解析核心：
"the difference of their squared distances is the restriction of a nonconstant affine
function to the unit circle … an affine line intersects a circle in at most two points,
and opposite endpoint signs force an odd number of transverse intersections; hence
exactly one intersection in the overlap."

**lead 指正（已接受）**：只证"零点 ≤ 2 + 端点异号"**不足以**推出唯一穿越，
还须证**每个零点都是 simple（横穿、符号改变）**。本模块只形式化"至多两点"这一支
（`cos` 在 `[0, 2π)` 上每个值至多两个原像），"割线 ⇒ 每个零点简单"作为解析陈述写在
`NOTE-SWITCH-UNIQUENESS-ANALYTIC.md`（引理 Z′）。本模块**无 sorry**。

## 证明策略（避免一切整型/实型混合的算术）

`cos` 在 `[0, π]` 上严格**反**单调（mathlib `Real.strictAntiOn_cos`），
在 `[π, 2π]` 上严格**单**调（下方自证，用 `cos(2π − t) = cos t` 与反单调合成）。
三点落在两段之一 ⇒ 鸽巢给出两点同段 ⇒ 该段内 `cos` 单射 ⇒ 两点相等。
-/

import Mathlib

namespace N11Formalization

open Real

/-- `cos` 在 `[π, 2π]` 上严格单调增（由 `[0,π]` 上的严格反单调 + `cos(2π−t)=cos t` 得到）。 -/
theorem cos_strictMonoOn_Icc_pi_two_pi :
    StrictMonoOn Real.cos (Set.Icc π (2 * π)) := by
  intro x hx y hy hxy
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hx' : 2 * π - x ∈ Set.Icc 0 π := by
    refine ⟨?_, ?_⟩ <;> [linarith [hx.2]; linarith [hx.1]]
  have hy' : 2 * π - y ∈ Set.Icc 0 π := by
    refine ⟨?_, ?_⟩ <;> [linarith [hy.2]; linarith [hy.1]]
  have hlt : 2 * π - y < 2 * π - x := by linarith
  have hanti := Real.strictAntiOn_cos hy' hx' hlt
  have h1 : Real.cos (2 * π - x) = Real.cos x := by
    rw [Real.cos_sub]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  have h2 : Real.cos (2 * π - y) = Real.cos y := by
    rw [Real.cos_sub]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  linarith [hanti, h1.symm ▸ hanti, h2.symm ▸ hanti]

/-- `cos` 在 `[0, 2π)` 上至多两个原像。

若 `t₁, t₂, t₃ ∈ [0, 2π)` 且两两 `cos` 值相同，则三者中至少两个相等。 -/
theorem cos_image_card_le_two {t₁ t₂ t₃ : ℝ}
    (h₁ : t₁ ∈ Set.Ico 0 (2 * π)) (h₂ : t₂ ∈ Set.Ico 0 (2 * π))
    (h₃ : t₃ ∈ Set.Ico 0 (2 * π))
    (h : Real.cos t₁ = Real.cos t₂ ∧ Real.cos t₂ = Real.cos t₃) :
    t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃ := by
  -- 同段两点 ⇒ 相等
  have key : ∀ {x y : ℝ}, x ∈ Set.Ico 0 (2 * π) → y ∈ Set.Ico 0 (2 * π) →
      Real.cos x = Real.cos y →
      ((x ≤ π ∧ y ≤ π) ∨ (π ≤ x ∧ π ≤ y)) → x = y := by
    intro x y hx hy hc hcase
    rcases hcase with ⟨hxπ, hyπ⟩ | ⟨hπx, hπy⟩
    · exact Real.strictAntiOn_cos.injOn ⟨hx.1, hxπ⟩ ⟨hy.1, hyπ⟩ hc
    · exact cos_strictMonoOn_Icc_pi_two_pi.injOn ⟨hπx, hx.2.le⟩ ⟨hπy, hy.2.le⟩ hc
  have h13 : Real.cos t₁ = Real.cos t₃ := h.1.trans h.2
  by_cases h1π : t₁ ≤ π
  · by_cases h2π : t₂ ≤ π
    · exact Or.inl (key h₁ h₂ h.1 (Or.inl ⟨h1π, h2π⟩))
    · by_cases h3π : t₃ ≤ π
      · exact Or.inr (Or.inl (key h₁ h₃ h13 (Or.inl ⟨h1π, h3π⟩)))
      · exact Or.inr (Or.inr (key h₂ h₃ h.2
          (Or.inr ⟨(not_le.mp h2π).le, (not_le.mp h3π).le⟩)))
  · by_cases h2π : t₂ ≤ π
    · by_cases h3π : t₃ ≤ π
      · exact Or.inr (Or.inr (key h₂ h₃ h.2 (Or.inl ⟨h2π, h3π⟩)))
      · -- t₁ > π 且 t₃ > π ⇒ 同段（都 ≥ π）⇒ t₁ = t₃
        exact Or.inr (Or.inl (key h₁ h₃ h13
          (Or.inr ⟨(not_le.mp h1π).le, (not_le.mp h3π).le⟩)))
    · -- t₁ > π 且 t₂ > π ⇒ 同段 ⇒ t₁ = t₂
      exact Or.inl (key h₁ h₂ h.1
        (Or.inr ⟨(not_le.mp h1π).le, (not_le.mp h2π).le⟩))

end N11Formalization
