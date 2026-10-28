import N11Formalization.ActualAugmentedRingLinkCycles
import N11Formalization.ActualCycleDeletion

/-! Actual ring links are connected on ALL real selected neighbors. Delete
the circle node from the produced single augmented cycle, then project its
real subgraph into the actual selected link. All frontier/degree/cycle
premises are produced upstream, not postulated for the cover. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingLinkConnected
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementLocalLinks ActualRefinementVertexLinks ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualAugmentedRingLinkConnected ActualAugmentedRingLinkCycles
open ActualCycleDeletion

def realSubgraphHom {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9)
    (H : (augmentedLink R i).Subgraph) (hNo : none ∉ H.verts) :
    H.coe →g linkGraph R (ringSite i) where
  toFun j := j.val.getD (ringSite i)
  map_rel' := by
    intro j k hjk
    have hjNo : j.val ≠ none := fun he => hNo (he ▸ j.property)
    have hkNo : k.val ≠ none := fun he => hNo (he ▸ k.property)
    cases hJ : j.val with
    | none => exact (hjNo hJ).elim
    | some a =>
      cases hK : k.val with
      | none => exact (hkNo hK).elim
      | some b =>
        have he := H.adj_sub hjk
        rw [hJ,hK] at he
        exact he

theorem actual_ring_link_reachable {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {j k : Fin 11} (hJ : Neighbor R (ringSite i) j) (hK : Neighbor R (ringSite i) k) :
    (linkGraph R (ringSite i)).Reachable j k := by
  classical
  obtain ⟨p,hp,hpv⟩ := actual_augmented_ring_cycle h hr R i
  obtain ⟨a,b,q,_,_,hq,_,_⟩ := remove_base p hp
  have hpN (s : Option (Fin 11)) : s ∈ p.support ↔ Included R i s := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph,hpv]
    rfl
  have hNo : none ∉ q.toSubgraph.verts := by
    intro hn
    have hs := q.mem_verts_toSubgraph.mp hn
    exact ((hq none).mp hs).2 rfl
  have hjmem : some j ∈ q.toSubgraph.verts := by
    apply q.mem_verts_toSubgraph.mpr
    apply (hq (some j)).mpr
    exact ⟨(hpN (some j)).mpr hJ,by simp⟩
  have hkmem : some k ∈ q.toSubgraph.verts := by
    apply q.mem_verts_toSubgraph.mpr
    apply (hq (some k)).mpr
    exact ⟨(hpN (some k)).mpr hK,by simp⟩
  have hreach := q.toSubgraph_connected ⟨some j,hjmem⟩ ⟨some k,hkmem⟩
  exact hreach.map (realSubgraphHom R i q.toSubgraph hNo)

theorem actual_all_site_links_reachable {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) {j k : Fin 11} (hJ : Neighbor R i j) (hK : Neighbor R i k) :
    (linkGraph R i).Reachable j k := by
  by_cases hir : i.val < 9
  · let I : Fin 9 := ⟨i.val,hir⟩
    have hi : ringSite I = i := Fin.ext rfl
    have hh := actual_ring_link_reachable h hr R I
      (by rw [hi]; exact hJ) (by rw [hi]; exact hK)
    rwa [hi] at hh
  · exact ActualHubLinkConnected.actual_hub_link_reachable h hr R (by omega) hJ hK

end N11Formalization.ActualRingLinkConnected
#check @N11Formalization.ActualRingLinkConnected.actual_ring_link_reachable
#check @N11Formalization.ActualRingLinkConnected.actual_all_site_links_reachable
#print axioms N11Formalization.ActualRingLinkConnected.actual_ring_link_reachable
#print axioms N11Formalization.ActualRingLinkConnected.actual_all_site_links_reachable
