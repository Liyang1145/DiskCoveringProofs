import N11Formalization.C892Hook
import N11Formalization.TcRootHook
import N11Formalization.RootRangeBoxFull

/-!
ResumeAttainment —— C892 消费者收窄：RootRange 前提消除 + 盒限定剩余义务。
写域：本文件 + evidence/resume-attainment/。不改共享模块。
剩余义务 `G2BoxObligation` 仍是**未证**具名 Prop（不是全局完成）。
-/

namespace N11Formalization.ResumeAttainment
open N11Formalization N11Formalization.RootRangeBoxFull

/-- 盒限定剩余义务：只对合法根盒内、残差为零的 `u` 要求中间环区覆盖。 -/
def G2BoxObligation : Prop :=
  ∀ u : Fin 12 → ℝ, InCertBox u → residual u = 0 → u 5 ≤ 0 → 0 ≤ u 6 + u 5 →
    ∀ x : Point, ¬ NegAxisPoint x → innerRadius u ≤ ‖x‖ → ‖x‖ < 1 →
      ∃ i : Fin 11, dist x (centersOfRoot u i) ≤ u 6

/-- 全称义务蕴含盒限定义务（收窄是真弱化）。 -/
theorem boxObligation_of_remaining (h : G2RemainingObligation) : G2BoxObligation :=
  fun u hu hres h5 h56 => h u (rootRange_of_box u hu) hres h5 h56

/-- 盒版整盘覆盖：内球/圆周/pinch 已证，环区由 `G2BoxObligation` 承担。
目标类型：残差为零 + 合法根盒 → `Covers (centersOfRoot u) (u 6)`（整个闭盘）。 -/
theorem covers_of_box_obligation (hrem : G2BoxObligation) (u : Fin 12 → ℝ)
    (hu : InCertBox u) (hres : residual u = 0) (hy1 : u 5 ≤ 0) (hRy : 0 ≤ u 6 + u 5) :
    Covers (centersOfRoot u) (u 6) := by
  have H := rootRange_of_box u hu
  intro x hx
  by_cases h1 : ‖x‖ ≤ innerRadius u
  · exact ⟨10, by rw [centersOfRoot_ten]; exact hub1_covers_ball u h1⟩
  · have h2 : innerRadius u ≤ ‖x‖ := le_of_lt (not_le.mp h1)
    have hx1 : ‖x‖ ≤ 1 := mem_unitDisk.mp hx
    by_cases h3 : ‖x‖ = 1
    · obtain ⟨k, hk⟩ := circle_covered_of_range u H x h3
      exact ⟨⟨(k : ℕ), by omega⟩, by rwa [centersOfRoot_ring]⟩
    · have h4 : ‖x‖ < 1 := lt_of_le_of_ne hx1 h3
      by_cases hp : NegAxisPoint x
      · obtain ⟨r, hr0, hr1, rfl⟩ := hp
        exact neg_axis_covered_all_of_residual u (H.hsin 0) H.hR hy1 hRy
          (by simp [hres]) hr0 hr1
      · exact hrem u hu hres hy1 hRy x hp h2 h4

/-- 替代 `TcRootHook.nd_box_final_attain`：不再要 `RootRange`，只剩 `G2BoxObligation`。 -/
theorem nd_box_final_attain_box :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧
      (G2BoxObligation → ∃ c : Fin 11 → Point, Covers c (Rstar S)) := by
  obtain ⟨S, hs, hlo, hhi, hidx, hlt, hR⟩ := nd_box_final_rootRange
  have hbox : InCertBox S.root := by
    intro i; have h := S.root_mem.1 i; rw [hlo, hhi] at h; exact h
  obtain ⟨_, _, hres, h5, h56⟩ := TcRootHook.c892RootHook_of_spec S hs hlo hhi hidx hR
  refine ⟨S, hs, hidx, hlt, fun hrem => ⟨centersOfRoot S.root, ?_⟩⟩
  have : Rstar S = S.root 6 := by simp [Rstar, hidx]
  rw [this]
  exact covers_of_box_obligation hrem S.root hbox hres h5 h56

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.covers_of_box_obligation
#print axioms N11Formalization.ResumeAttainment.nd_box_final_attain_box
