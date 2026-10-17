import N11Formalization.ActualHubLinkCycles

/-! Delete the other hub from an ACTUAL hub-link cycle: a genuine simple
ring path containing ALL actual ring neighbors. Its distinct endpoints
give the two central triangles and retain true original nearest witnesses.
No canonical cut, path length, boundary order or two-fan count is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubRingPaths
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementLocalLinks
open ActualRefinementVertexLinks ActualHubLinkCycles

theorem cycle_remove_base {G : SimpleGraph (Fin 11)} {u : Fin 11}
    (p : G.Walk u u) (hp : p.IsCycle) :
    ∃ a b : Fin 11, ∃ q : G.Walk a b,
      q.IsPath ∧ a ≠ b ∧
      (∀ x : Fin 11, x ∈ q.support ↔ x ∈ p.support ∧ x ≠ u) ∧
      G.Adj u a ∧ G.Adj b u ∧ q.length+2 = p.length := by
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
  refine ⟨p.snd,p.tail.penultimate,q,hqPath,hab,?_,p.adj_snd hp.not_nil,
    p.tail.adj_penultimate htail,hqLen⟩
  intro x
  have hcons : p.support = u :: (q.support ++ [u]) := by
    rw [p.support_eq_cons,← htailSupp]
  rw [hcons]
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  constructor
  · intro hx
    exact ⟨Or.inr (Or.inl hx),fun he => hno (he ▸ hx)⟩
  · rintro ⟨(he | hx | he),hne⟩
    · exact (hne he).elim
    · exact hx
    · exact (hne he).elim

theorem hubs_exhaust : ∀ i j k : Fin 11,
    ((i = 9 ∧ j = 10) ∨ (i = 10 ∧ j = 9)) → k ≠ i → k ≠ j → k.val < 9 := by
  decide +kernel

structure RingPath {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i u : Fin 11) where
  first : Fin 11
  last : Fin 11
  walk : (linkGraph R i).Walk first last
  simple : walk.IsPath
  endpoints_ne : first ≠ last
  exact_vertices : ∀ k : Fin 11, k ∈ walk.support ↔ Neighbor R i k ∧ k ≠ u
  ring_vertices : ∀ k ∈ walk.support, k.val < 9
  first_central : ∃ a : R.Index, i ∈ labelSet R a ∧ u ∈ labelSet R a ∧ first ∈ labelSet R a
  last_central : ∃ a : R.Index, i ∈ labelSet R a ∧ u ∈ labelSet R a ∧ last ∈ labelSet R a

theorem actual_ring_path {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) {i u : Fin 11}
    (hhubs : (i = 9 ∧ u = 10) ∨ (i = 10 ∧ u = 9)) :
    Nonempty (RingPath R i u) := by
  have hi : 9 ≤ i.val := by rcases hhubs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  obtain ⟨a,_,_,_,ha9,ha10,_,_⟩ := ActualRefinementFacetRetention.Refinement.hub_edge_two_retained R h hr
  have hu : Neighbor R i u := by
    rcases hhubs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨by decide,a,mem_labelSet.mpr ha9,mem_labelSet.mpr ha10⟩
    · exact ⟨by decide,a,mem_labelSet.mpr ha10,mem_labelSet.mpr ha9⟩
  obtain ⟨p,hp,hverts,_⟩ := actual_hub_link_cycle h hr R hi hu
  have hpverts (k : Fin 11) : k ∈ p.support ↔ Neighbor R i k := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph,hverts]
    rfl
  obtain ⟨first,last,q,hq,hne,hqverts,hfirst,hlast,_⟩ := cycle_remove_base p hp
  have hvertex (k : Fin 11) : k ∈ q.support ↔ Neighbor R i k ∧ k ≠ u := by
    rw [hqverts,hpverts]
  have hfirstT := hfirst.2.2.2
  obtain ⟨A,hAi,hAu,hAf⟩ := hfirstT
  obtain ⟨B,hBi,hBl,hBu⟩ := hlast.2.2.2
  refine ⟨⟨first,last,q,hq,hne,hvertex,?_,⟨A,hAi,hAu,hAf⟩,⟨B,hBi,hBu,hBl⟩⟩⟩
  intro k hk
  have hK := (hvertex k).mp hk
  exact hubs_exhaust i u k hhubs hK.1.1 hK.2

theorem actual_two_ring_paths {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    Nonempty (RingPath R 9 10) ∧ Nonempty (RingPath R 10 9) :=
  ⟨actual_ring_path h hr R (Or.inl ⟨rfl,rfl⟩),
    actual_ring_path h hr R (Or.inr ⟨rfl,rfl⟩)⟩

end N11Formalization.ActualHubRingPaths
#check @N11Formalization.ActualHubRingPaths.actual_two_ring_paths
#print axioms N11Formalization.ActualHubRingPaths.cycle_remove_base
#print axioms N11Formalization.ActualHubRingPaths.actual_ring_path
#print axioms N11Formalization.ActualHubRingPaths.actual_two_ring_paths
