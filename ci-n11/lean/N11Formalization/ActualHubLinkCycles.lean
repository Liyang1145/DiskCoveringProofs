import N11Formalization.ActualHubLinkConnected

/-! ACTUAL hub links are single finite cycles, not merely2-regular graphs.
Each cycle contains ALL selected neighbors, including the other hub, and
its edges are exactly the genuine selected-triangle link edges. No cycle,
disk or two-fan hypothesis is added. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubLinkCycles
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementInteriorFacetCount
open ActualRefinementLinkDegrees ActualRefinementLocalLinks ActualRefinementVertexLinks
open ActualHubLinkConnected ActualRefinementFacetRetention

theorem boundary_labels_ring : ∀ i j : Fin 11, BoundaryLabels i j → i.val < 9 := by
  decide +kernel

theorem link_neighborSet_eq {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {i j : Fin 11} (hij : i ≠ j) :
    (linkGraph R i).neighborSet j = (linkNeighbors R i j hij : Set (Fin 11)) := by
  ext k
  change (linkGraph R i).Adj j k ↔ k ∈ linkNeighbors R i j hij
  rw [mem_linkNeighbors]
  constructor
  · rintro ⟨hjk,hji,hki,a,hi,hj,hk⟩
    refine ⟨hki,hjk.symm,a,?_⟩
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hi
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hj
    have he := Finset.mem_singleton.mp hl
    subst l
    exact hk
  · rintro ⟨hki,hkj,a,hsub⟩
    exact ⟨hkj.symm,hij.symm,hki,a,hsub (by simp),hsub (by simp),hsub (by simp)⟩

theorem actual_hub_link_degree_two {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i j : Fin 11} (hi : 9 ≤ i.val) (hj : Neighbor R i j) :
    ((linkGraph R i).neighborSet j).ncard = 2 := by
  obtain ⟨a,hai,haj⟩ := hj.2
  have hnb : ¬ BoundaryLabels i j := by
    intro hb
    have hh := boundary_labels_ring i j hb
    omega
  rw [link_neighborSet_eq R hj.1.symm,Set.ncard_coe_finset]
  have hd := actual_link_degree h hr R hj.1.symm hai haj
  rwa [if_neg hnb] at hd

theorem neighbor_of_link_adj {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {i j k : Fin 11} (hjk : (linkGraph R i).Adj j k) : Neighbor R i j :=
  ⟨hjk.2.1,by obtain ⟨a,hi,hj,_⟩ := hjk.2.2.2; exact ⟨a,hi,hj⟩⟩

theorem actual_hub_link_isCycles {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 11} (hi : 9 ≤ i.val) : (linkGraph R i).IsCycles := by
  intro j hj
  obtain ⟨k,hjk⟩ := hj
  exact actual_hub_link_degree_two h hr R hi (neighbor_of_link_adj R hjk)

theorem actual_hub_link_cycle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i u : Fin 11} (hi : 9 ≤ i.val) (hu : Neighbor R i u) :
    ∃ p : (linkGraph R i).Walk u u, p.IsCycle ∧
      p.toSubgraph.verts = {j : Fin 11 | Neighbor R i j} ∧
      ∀ j k : Fin 11, Neighbor R i j →
        ((p.toSubgraph.spanningCoe).Adj j k ↔ (linkGraph R i).Adj j k) := by
  classical
  let G := linkGraph R i
  let C := G.connectedComponentMk u
  have hcycles : G.IsCycles := actual_hub_link_isCycles h hr R hi
  have hne : (G.neighborSet u).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [actual_hub_link_degree_two h hr R hi hu]; decide)
  have hC : C.supp = {j : Fin 11 | Neighbor R i j} := by
    ext j
    constructor
    · intro hj
      by_cases hju : j = u
      · subst j
        exact hu
      have hreach : G.Reachable j u :=
        C.reachable_of_mem_supp hj SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hsupp := SimpleGraph.mem_support_of_reachable hju hreach
      obtain ⟨k,hjk⟩ := SimpleGraph.mem_support G |>.mp hsupp
      exact neighbor_of_link_adj R hjk
    · intro hj
      change G.connectedComponentMk j = G.connectedComponentMk u
      apply SimpleGraph.ConnectedComponent.sound
      exact (actual_hub_link_reachable h hr R hi hu hj).symm
  obtain ⟨p,hp,hverts⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C) SimpleGraph.ConnectedComponent.connectedComponentMk_mem hne
  have hvertices : p.toSubgraph.verts = {j : Fin 11 | Neighbor R i j} := hverts.trans hC
  refine ⟨p,hp,hvertices,?_⟩
  intro j k hj
  have hjmem : j ∈ p.toSubgraph.verts := by rw [hvertices]; exact hj
  exact hp.adj_toSubgraph_iff_of_isCycles hcycles hjmem k

theorem actual_hub_cycle_through_other_hub {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (∃ p : (linkGraph R 9).Walk 10 10, p.IsCycle ∧
      p.toSubgraph.verts = {j : Fin 11 | Neighbor R 9 j}) ∧
    (∃ p : (linkGraph R 10).Walk 9 9, p.IsCycle ∧
      p.toSubgraph.verts = {j : Fin 11 | Neighbor R 10 j}) := by
  obtain ⟨a,_,_,_,ha9,ha10,_,_⟩ := Refinement.hub_edge_two_retained R h hr
  have h9 : Neighbor R 9 10 := ⟨by decide,a,mem_labelSet.mpr ha9,mem_labelSet.mpr ha10⟩
  have h10 : Neighbor R 10 9 := ⟨by decide,a,mem_labelSet.mpr ha10,mem_labelSet.mpr ha9⟩
  obtain ⟨p,hp,hv,_⟩ := actual_hub_link_cycle h hr R (by decide : 9 ≤ (9 : Fin 11).val) h9
  obtain ⟨q,hq,hw,_⟩ := actual_hub_link_cycle h hr R (by decide : 9 ≤ (10 : Fin 11).val) h10
  exact ⟨⟨p,hp,hv⟩,⟨q,hq,hw⟩⟩

end N11Formalization.ActualHubLinkCycles
#check @N11Formalization.ActualHubLinkCycles.actual_hub_cycle_through_other_hub
#print axioms N11Formalization.ActualHubLinkCycles.actual_hub_link_degree_two
#print axioms N11Formalization.ActualHubLinkCycles.actual_hub_link_cycle
#print axioms N11Formalization.ActualHubLinkCycles.actual_hub_cycle_through_other_hub
