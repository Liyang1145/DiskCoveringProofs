import N11Formalization.GridBridge
import N11Formalization.C892Hook

namespace N11Formalization.TcRootHook
open N11Formalization

theorem hi5 : boxHiCert 5 = -722591877320515100682603 / 2 ^ 82 := rfl
theorem lo5 : boxLoCert 5 = -722591886991921657599637 / 2 ^ 82 := rfl
theorem lo6 : boxLoCert 6 = 1837489159457200081021291 / 2 ^ 82 := rfl

/-- C892RootHook 的内容（RootRange 为显式前提），对任意钉成 TCSystem+证书盒的规格成立。 -/
theorem hook_of_spec (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    (hR : RootRange S.root) :
    S.radiusIndex = 6 ∧ RootRange S.root ∧ residual S.root = 0 ∧
      S.root 5 ≤ 0 ∧ 0 ≤ S.root 6 + S.root 5 := by
  obtain ⟨hbox, hz⟩ := S.root_mem
  rw [hsys] at hz
  rw [hlo, hhi] at hbox
  refine ⟨hidx, hR, ?_, ?_, ?_⟩
  · funext i
    have h := congrFun hz ⟨(i : ℕ), by omega⟩
    rw [TCSystem_first] at h
    simpa using h
  · have h := (hbox 5).2
    rw [hi5] at h
    have : ((-722591877320515100682603 / 2 ^ 82 : ℚ) : ℝ) ≤ 0 := by norm_num
    linarith
  · have h5 := (hbox 5).1
    have h6 := (hbox 6).1
    rw [lo5] at h5
    rw [lo6] at h6
    have : (0 : ℝ) ≤ ((1837489159457200081021291 / 2 ^ 82 : ℚ) : ℝ) +
        ((-722591886991921657599637 / 2 ^ 82 : ℚ) : ℝ) := by norm_num
    linarith

/-- 由 nd_box_final 的 S 供给钩子（RootRange 显式前提）。 -/
theorem nd_box_final_hook :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧
      (RootRange S.root →
        S.radiusIndex = 6 ∧ RootRange S.root ∧ residual S.root = 0 ∧
          S.root 5 ≤ 0 ∧ 0 ≤ S.root 6 + S.root 5) := by
  obtain ⟨S, hs, hlo, hhi, hidx, _, hlt⟩ := GridBridge.nd_box_final
  exact ⟨S, hs, hidx, hlt, hook_of_spec S hs hlo hhi hidx⟩

/-- defeq 桥：结论写成 `C892RootHook S`。 -/
theorem c892RootHook_of_spec (S : C891RootSpec) (hsys : S.sys = TCSystem)
    (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    (hR : RootRange S.root) : C892RootHook S :=
  hook_of_spec S hsys hlo hhi hidx hR

/-- 半径分量非负（RootRange.hR 可由盒下界单独供给）。 -/
theorem root6_nonneg (S : C891RootSpec) (hlo : S.boxLo = boxLoCert) : 0 ≤ S.root 6 := by
  have h := (S.root_mem.1 6).1
  rw [hlo, lo6] at h
  have : (0 : ℝ) ≤ ((1837489159457200081021291 / 2 ^ 82 : ℚ) : ℝ) := by norm_num
  linarith

/-- hattain 条件端：只剩 G2RemainingObligation 与 RootRange。 -/
theorem nd_box_final_attain :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧
      (G2RemainingObligation → RootRange S.root → ∃ c : Fin 11 → Point, Covers c (Rstar S)) := by
  obtain ⟨S, hs, hlo, hhi, hidx, _, hlt⟩ := GridBridge.nd_box_final
  exact ⟨S, hs, hidx, hlt, fun hrem hR =>
    hattain_of_remaining S hrem (c892RootHook_of_spec S hs hlo hhi hidx hR)⟩

end N11Formalization.TcRootHook
