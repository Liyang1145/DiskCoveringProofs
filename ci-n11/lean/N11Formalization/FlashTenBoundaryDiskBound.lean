import N11Formalization.FlashTenBoundaryHper
import N11Formalization.FlashTenBoundaryArcsinBound

/-!
# C450 第 1 段：`t` 落在数据盒 + 外圆分支符号（Hper 不动）

**语法坑（已定位）**：Hper 内两种写法并存 —— `halfwidth_cos`/`halfwidth_arccos` 用
`(19:ℝ)^2 / 50^2`，而 `exists_t_of_rho` 用 `(19/50)^2`（它内部用 `hR` 换过一次）。
两者在新件里相遇会让 `isDefEq` 心跳超时（1e6~4e6 都不够）。修法：把那个等式提成
**具名引理** `R_sq_form`，在需要处显式 `rw` 对齐，不做隐式统一。

* `exists_t_of_rho_mem`：`exists_t_of_rho` + 数据盒上界（接已证 `arcsin_R_le_bound`）+ 域事实 `sin²t ≤ R²`；
* `outer_t_of_rho`：`t` 作显式参数，给出源变量 `(t, s)`。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

section

/-- Hper 内部用过的等式（提出成具名引理，供跨件对齐写法）。 -/
theorem R_sq_form : ((19 : ℝ) ^ 2 / 50 ^ 2) = (19 / 50) ^ 2 := by ring

/-- `exists_t_of_rho` + 数据盒上界 + 域事实。 -/
theorem exists_t_of_rho_mem {ρ : ℝ} (h1 : 1 - 19 / 50 ≤ ρ) (h2 : ρ ≤ 1 + 19 / 50) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ (0.3897962964742606 : ℝ) ∧ t ∈ Set.Icc 0 Real.pi ∧
      (Real.sin t) ^ 2 ≤ (19 / 50) ^ 2 ∧
      (ρ = Real.cos t + Real.sqrt ((19 / 50) ^ 2 - (Real.sin t) ^ 2)
        ∨ ρ = Real.cos t - Real.sqrt ((19 / 50) ^ 2 - (Real.sin t) ^ 2)) := by
  obtain ⟨t, ht0, htle, htIcc, hcases⟩ := exists_t_of_rho h1 h2
  have hasin_le : Real.arcsin (19 / 50) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  refine ⟨t, ht0, le_trans htle arcsin_R_le_bound, htIcc, ?_, hcases⟩
  have hsin_le : Real.sin t ≤ 19 / 50 := by
    have htmem : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [ht0, Real.pi_pos], by linarith [hasin_le]⟩
    have hasinmem : Real.arcsin (19 / 50) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_le_arcsin _, hasin_le⟩
    rcases lt_or_eq_of_le htle with hlt | heq
    · have hmono : Real.sin t < Real.sin (Real.arcsin (19 / 50)) :=
        Real.strictMonoOn_sin htmem hasinmem hlt
      rw [Real.sin_arcsin (by norm_num) (by norm_num)] at hmono
      exact le_of_lt hmono
    · rw [heq, Real.sin_arcsin (by norm_num) (by norm_num)]
  have hsin_nonneg : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [hasin_le])
  nlinarith [hsin_le, hsin_nonneg, (show (0 : ℝ) < 19 / 50 by norm_num)]

/-- **外圆源变量对应**（`t` 作显式参数；对齐写法用 `R_sq_form`）。 -/
theorem outer_t_of_rho {ρ t : ℝ} (h1 : 1 - 19 / 50 ≤ ρ) (h2 : ρ ≤ 1 + 19 / 50)
    (ht : t = Real.arccos ((1 + ρ ^ 2 - (19 / 50) ^ 2) / (2 * ρ))) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 ≤ t ∧ t ≤ (0.3897962964742606 : ℝ) ∧
      t ∈ Set.Icc 0 Real.pi ∧ (Real.sin t) ^ 2 ≤ (19 / 50) ^ 2 ∧
      ρ = Real.cos t + s * Real.sqrt ((19 / 50) ^ 2 - (Real.sin t) ^ 2) := by
  have hρpos : 0 < ρ := by
    linarith [show (0 : ℝ) < 19 / 50 by norm_num, show (19 : ℝ) / 50 < 1 by norm_num]
  obtain ⟨t0, ht0, htle, htIcc, hdom, hcases⟩ := exists_t_of_rho_mem h1 h2
  have hdom' : (Real.sin t0) ^ 2 ≤ (19 : ℝ) ^ 2 / 50 ^ 2 := by simpa [R_sq_form] using hdom
  have hcases' : ρ = Real.cos t0 + Real.sqrt ((19 : ℝ) ^ 2 / 50 ^ 2 - (Real.sin t0) ^ 2)
      ∨ ρ = Real.cos t0 - Real.sqrt ((19 : ℝ) ^ 2 / 50 ^ 2 - (Real.sin t0) ^ 2) := by
    rcases hcases with hr | hr
    · exact Or.inl (by simpa [R_sq_form] using hr)
    · exact Or.inr (by simpa [R_sq_form] using hr)
  have hkey : Real.arccos ((1 + ρ ^ 2 - (19 : ℝ) ^ 2 / 50 ^ 2) / (2 * ρ)) = t0 := by
    rcases hcases' with hr | hr
    · exact halfwidth_arccos (ne_of_gt hρpos) (by norm_num : (1 : ℝ) ^ 2 = 1) hdom'
        htIcc.1 htIcc.2 (by simpa [sub_eq_add_neg] using hr)
    · exact halfwidth_arccos (ne_of_gt hρpos) (by norm_num : ((-1 : ℝ)) ^ 2 = 1) hdom'
        htIcc.1 htIcc.2 (by simpa [sub_eq_add_neg] using hr)
  have ht0' : t = t0 := by rw [ht, ← R_sq_form]; exact hkey
  rcases hcases with hr | hr
  · exact ⟨1, Or.inl rfl, by rw [ht0']; exact ht0, by rw [ht0']; exact htle,
      by rw [ht0']; exact htIcc, by rw [ht0']; exact hdom, by rw [ht0']; simpa [sub_eq_add_neg] using hr⟩
  · exact ⟨-1, Or.inr rfl, by rw [ht0']; exact ht0, by rw [ht0']; exact htle,
      by rw [ht0']; exact htIcc, by rw [ht0']; exact hdom, by rw [ht0']; simpa [sub_eq_add_neg] using hr⟩

end

end N11Formalization