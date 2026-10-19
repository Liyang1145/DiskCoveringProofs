import N11Formalization.ActualHubRingPaths

/-! Generic deletion of the base vertex of a true simple cycle. Used for
the ACTUAL ring link's auxiliary circle node, not an assumed topology. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCycleDeletion

theorem remove_base {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) :
    ∃ a b : V, ∃ q : G.Walk a b,
      q.IsPath ∧ a ≠ b ∧
      (∀ x : V, x ∈ q.support ↔ x ∈ p.support ∧ x ≠ u) ∧
      G.Adj u a ∧ G.Adj b u := by
  classical
  have hp3 := hp.three_le_length
  have htlen := p.length_tail
  have htail : ¬ p.tail.Nil := by
    rw [← SimpleGraph.Walk.length_eq_zero_iff]
    omega
  let q := p.tail.dropLast
  have hqPath : q.IsPath := hp.isPath_tail.dropLast
  have hqLen : q.length+2 = p.length := by
    have hh := p.tail.length_dropLast_add_one htail
    dsimp only [q]
    omega
  have hqnon : ¬ q.Nil := by
    rw [← SimpleGraph.Walk.length_eq_zero_iff]
    omega
  have hab : p.snd ≠ p.tail.penultimate := fun he => hqnon (hqPath.nil_iff_eq.mpr he)
  have htailSupp : q.support ++ [u] = p.support.tail := by
    change p.tail.dropLast.support ++ [u] = p.support.tail
    rw [p.tail.support_dropLast_concat htail,p.support_tail_of_not_nil hp.not_nil]
  have hno : u ∉ q.support := by
    have hnodup := hp.support_nodup
    rw [← htailSupp,List.nodup_append] at hnodup
    intro hu
    exact hnodup.2.2 u hu u (by simp) rfl
  refine ⟨p.snd,p.tail.penultimate,q,hqPath,hab,?_,p.adj_snd hp.not_nil,p.tail.adj_penultimate htail⟩
  intro x
  have hcons : p.support = u :: (q.support ++ [u]) := by
    rw [← p.cons_tail_support,← htailSupp]
  rw [hcons]
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  constructor
  · intro hx
    exact ⟨Or.inr (Or.inl hx),fun he => hno (he ▸ hx)⟩
  · rintro ⟨(he | hx | he),hne⟩
    · exact (hne he).elim
    · exact hx
    · exact (hne he).elim

end N11Formalization.ActualCycleDeletion
#check @N11Formalization.ActualCycleDeletion.remove_base
#print axioms N11Formalization.ActualCycleDeletion.remove_base
