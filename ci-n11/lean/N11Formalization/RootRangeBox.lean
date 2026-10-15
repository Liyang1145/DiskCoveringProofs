import N11Formalization.TcRootHook

namespace N11Formalization.RootRangeBox
open N11Formalization

/-- 盒内点（证书盒）。 -/
def InCertBox (u : Fin 12 → ℝ) : Prop :=
  ∀ i : Fin 12, (boxLoCert i : ℝ) ≤ u i ∧ u i ≤ (boxHiCert i : ℝ)

theorem ha_hapi_of_box (u : Fin 12 → ℝ) (hu : InCertBox u) :
    0 ≤ u 6 ∧ (∀ k : Fin 9, 0 ≤ angleVec u k) ∧ (∀ k : Fin 9, angleVec u k ≤ Real.pi) := by
  have l0 := (hu 0).1; have l1 := (hu 1).1; have l2 := (hu 2).1; have l3 := (hu 3).1
  have h0 := (hu 0).2; have h1 := (hu 1).2; have h2 := (hu 2).2; have h3 := (hu 3).2
  have l6 := (hu 6).1
  have e0 : boxLoCert 0 = 1798923298417342433274219 / 2 ^ 82 := rfl
  have e1 : boxLoCert 1 = 1648215922234750999800171 / 2 ^ 82 := rfl
  have e2 : boxLoCert 2 = 1357971481365603998574955 / 2 ^ 82 := rfl
  have e3 : boxLoCert 3 = 1852132483251062452070763 / 2 ^ 82 := rfl
  have e6 : boxLoCert 6 = 1837489159457200081021291 / 2 ^ 82 := rfl
  have f0 : boxHiCert 0 = 1798923308088748990191253 / 2 ^ 82 := rfl
  have f1 : boxHiCert 1 = 1648215931906157556717205 / 2 ^ 82 := rfl
  have f2 : boxHiCert 2 = 1357971491037010555491989 / 2 ^ 82 := rfl
  have f3 : boxHiCert 3 = 1852132492922469008987797 / 2 ^ 82 := rfl
  rw [e0] at l0; rw [e1] at l1; rw [e2] at l2; rw [e3] at l3; rw [e6] at l6
  rw [f0] at h0; rw [f1] at h1; rw [f2] at h2; rw [f3] at h3
  push_cast at l0 l1 l2 l3 l6 h0 h1 h2 h3
  have hp := Real.pi_gt_three
  refine ⟨by linarith, ?_, ?_⟩
  · intro k; fin_cases k <;> simp [angleVec] <;> linarith
  · intro k; fin_cases k <;> simp [angleVec] <;> linarith

/-- 未证字段（需盒口径 sin/sqrt 区间件）：具名保留。 -/
def TrigRangeBox (u : Fin 12 → ℝ) : Prop :=
  (∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) ∧ (∀ k : Fin 9, 0 ≤ rhoK u k)

theorem rootRange_of_box (u : Fin 12 → ℝ) (hu : InCertBox u) (ht : TrigRangeBox u) :
    RootRange u := by
  obtain ⟨hR, ha, hapi⟩ := ha_hapi_of_box u hu
  exact ⟨hR, ha, hapi, ht.1, ht.2⟩

end N11Formalization.RootRangeBox
