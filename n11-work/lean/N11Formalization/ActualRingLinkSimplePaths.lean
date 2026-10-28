import N11Formalization.ActualRingLinkConnected

/-! Every ACTUAL ring link has a genuine simple path spanning ALL real
selected neighbors, with the two true boundary neighbors as endpoints.
Produced by deleting the auxiliary circle node and an injective projection,
not by assuming the cell has a polygonal boundary or the link is a path. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingLinkSimplePaths
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementLocalLinks ActualRefinementVertexLinks ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualAugmentedRingLinkConnected ActualAugmentedRingLinkCycles
open ActualRingLinkConnected ActualCycleDeletion

theorem realSubgraphHom_injective {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 9) (H : (augmentedLink R i).Subgraph) (hNo : none ∉ H.verts) :
    Function.Injective (realSubgraphHom R i H hNo) := by
  intro j k he
  apply Subtype.ext
  have hjNo : j.val ≠ none := fun he => hNo (he ▸ j.property)
  have hkNo : k.val ≠ none := fun he => hNo (he ▸ k.property)
  change j.val.getD (ringSite i) = k.val.getD (ringSite i) at he
  cases hJ : j.val with
  | none => exact (hjNo hJ).elim
  | some a =>
    cases hK : k.val with
    | none => exact (hkNo hK).elim
    | some b =>
      have hab : a = b := by simpa only [hJ,hK,Option.getD_some] using he
      exact congrArg Option.some hab

structure LinkPath {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9) where
  first : Fin 11
  last : Fin 11
  walk : (linkGraph R (ringSite i)).Walk first last
  simple : walk.IsPath
  endpoints_ne : first ≠ last
  exact_vertices : ∀ j : Fin 11, j ∈ walk.support ↔ Neighbor R (ringSite i) j
  boundary_ends : ({first,last} : Finset (Fin 11)) = {prevSite i,nextSite i}

theorem actual_ring_link_simple_path {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    Nonempty (LinkPath R i) := by
  classical
  obtain ⟨p,hp,hpv⟩ := actual_augmented_ring_cycle h hr R i
  obtain ⟨a,b,q,hqpath,hab,hq,ha,hb⟩ := remove_base p hp
  have hpN (s : Option (Fin 11)) : s ∈ p.support ↔ Included R i s := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph,hpv]
    rfl
  have hNo : none ∉ q.toSubgraph.verts := by
    intro hn
    exact ((hq none).mp (q.mem_verts_toSubgraph.mp hn)).2 rfl
  have hqNo (s : Option (Fin 11)) (hs : s ∈ q.support) : s ≠ none := ((hq s).mp hs).2
  let f := realSubgraphHom R i q.toSubgraph hNo
  let P := q.mapToSubgraph.map f
  have hqSub : q.mapToSubgraph.IsPath := SimpleGraph.Walk.IsPath.of_map
    (by rw [q.map_mapToSubgraph_hom]; exact hqpath)
  have hP : P.IsPath := hqSub.map (realSubgraphHom_injective R i q.toSubgraph hNo)
  have hsOrig : q.mapToSubgraph.support.map (fun x => x.val) = q.support := by
    have hh := congrArg SimpleGraph.Walk.support q.map_mapToSubgraph_hom
    rw [SimpleGraph.Walk.support_map] at hh
    exact hh
  have hsP : P.support = q.support.map (fun s => s.getD (ringSite i)) := by
    rw [← hsOrig,List.map_map]
    exact SimpleGraph.Walk.support_map f q.mapToSubgraph
  have hvertices (j : Fin 11) : j ∈ P.support ↔ Neighbor R (ringSite i) j := by
    rw [hsP,List.mem_map]
    constructor
    · rintro ⟨s,hs,he⟩
      have hnot := hqNo s hs
      have hInc := (hpN s).mp ((hq s).mp hs).1
      cases s with
      | none => exact (hnot rfl).elim
      | some k =>
        have hkj : k = j := he
        subst j
        exact hInc
    · intro hj
      refine ⟨some j,?_,rfl⟩
      exact (hq (some j)).mpr ⟨(hpN (some j)).mpr hj,by simp⟩
  have haNo : a ≠ none := hqNo a q.start_mem_support
  have hbNo : b ≠ none := hqNo b q.end_mem_support
  have hendNe : a.getD (ringSite i) ≠ b.getD (ringSite i) := by
    intro he
    cases a with
    | none => exact (haNo rfl).elim
    | some a =>
      cases b with
      | none => exact (hbNo rfl).elim
      | some b =>
        have heq : a = b := he
        exact hab (congrArg Option.some heq)
  have haBound : BoundaryNeighbor i (a.getD (ringSite i)) := by
    cases a with
    | none => exact (haNo rfl).elim
    | some a => exact ha
  have hbBound : BoundaryNeighbor i (b.getD (ringSite i)) := by
    cases b with
    | none => exact (hbNo rfl).elim
    | some b => exact hb
  have hends : ({a.getD (ringSite i),b.getD (ringSite i)} : Finset (Fin 11)) = {prevSite i,nextSite i} := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.mem_insert.mpr (haBound.imp_right Finset.mem_singleton.mpr)
      · have he := Finset.mem_singleton.mp hj
        subst j
        exact Finset.mem_insert.mpr (hbBound.imp_right Finset.mem_singleton.mpr)
    · simp [hendNe,(boundary_sites_distinct i).2.2]
  exact ⟨⟨a.getD (ringSite i),b.getD (ringSite i),P,hP,hendNe,hvertices,hends⟩⟩

end N11Formalization.ActualRingLinkSimplePaths
#check @N11Formalization.ActualRingLinkSimplePaths.actual_ring_link_simple_path
#print axioms N11Formalization.ActualRingLinkSimplePaths.realSubgraphHom_injective
#print axioms N11Formalization.ActualRingLinkSimplePaths.actual_ring_link_simple_path
