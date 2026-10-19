import N11Formalization.Conditional.RootSpec
import N11Formalization.Assembly.G2Unified

namespace N11Formalization

/-- C892 root hook: facts about the C891 root `S.root` itself that are needed to wire in the G2 cover. -/
def C892RootHook (S : C891RootSpec) : Prop :=
  S.radiusIndex = 6 ∧ RootRange S.root ∧ residual S.root = 0 ∧
    S.root 5 ≤ 0 ∧ 0 ≤ S.root 6 + S.root 5

/-- Named Prop: the same root attains coverage. -/
def C892SameRootAttain (S : C891RootSpec) : Prop :=
  ∃ c : Fin 11 → Point, Covers c (Rstar S)

theorem c892_of_unified (S : C891RootSpec) (hG : G2Unified) (h : C892RootHook S) :
    C892SameRootAttain S := by
  obtain ⟨hidx, hR, hres, h5, h56⟩ := h
  refine ⟨centersOfRoot S.root, ?_⟩
  have : Rstar S = S.root 6 := by simp [Rstar, hidx]
  rw [this]; exact hG S.root hR hres h5 h56

theorem hattain_of_remaining (S : C891RootSpec)
    (hrem : G2RemainingObligation) (h : C892RootHook S) :
    ∃ c : Fin 11 → Point, Covers c (Rstar S) :=
  c892_of_unified S (covers_of_remaining_obligation hrem) h

theorem n11_main_of_c892_hook (S : C891RootSpec)
    (hrem : G2RemainingObligation) (h : C892RootHook S)
    (hbound : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → Rstar S ≤ r) :
    N11MainStatement (Rstar S) :=
  n11_main_conditional S (hattain_of_remaining S hrem h) hbound

end N11Formalization

