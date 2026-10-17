import N11Formalization.ActualAugmentedRingLinkConnected
import N11Formalization.ActualHubLinkCycles

/-! The actual circle-augmented ring link is ONE finite cycle. The circle
node has the two true boundary neighbors; each boundary link degree1 gains
one circle edge, all other true degrees stay2. Connectedness was produced
from the real clipped frontier. No ring-link cycle assumption. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualAugmentedRingLinkCycles
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementLinkDegrees
open ActualRefinementLocalLinks ActualRefinementVertexLinks ActualHubLinkCycles
open ActualRingLinkBoundaryData ActualAugmentedRingLinkConnected
open ActualRefinementInteriorFacetCount ActualRingDirectionOrder

instance (i : Fin 9) (j : Fin 11) : Decidable (BoundaryNeighbor i j) := by
  unfold BoundaryNeighbor
  infer_instance

theorem boundary_labels_fixed_ring : ∀ i : Fin 9, ∀ j : Fin 11,
    BoundaryLabels (ringSite i) j ↔ BoundaryNeighbor i j := by
  decide +kernel

theorem circle_degree_two {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9) :
    ((augmentedLink R i).neighborSet none).ncard = 2 := by
  have he : (augmentedLink R i).neighborSet none =
      ({some (prevSite i),some (nextSite i)} : Set (Option (Fin 11))) := by
    ext j
    cases j
    · change False ↔ none ∈ ({some (prevSite i),some (nextSite i)} : Set (Option (Fin 11)))
      simp
    · change BoundaryNeighbor i _ ↔ _ ∈ ({some (prevSite i),some (nextSite i)} : Set (Option (Fin 11)))
      simp [BoundaryNeighbor]
  rw [he]
  exact Set.ncard_pair ((Option.some_injective (Fin 11)).ne (boundary_sites_distinct i).2.2)

theorem augmented_real_neighborSet {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 9) {j : Fin 11} (hij : ringSite i ≠ j) :
    (augmentedLink R i).neighborSet (some j) =
      ((if BoundaryNeighbor i j then
        insert none ((linkNeighbors R (ringSite i) j hij).image Option.some)
      else (linkNeighbors R (ringSite i) j hij).image Option.some) :
        Finset (Option (Fin 11))) := by
  classical
  ext k
  by_cases hb : BoundaryNeighbor i j
  · rw [if_pos hb]
    cases k with
    | none =>
      change BoundaryNeighbor i j ↔ (none : Option (Fin 11)) ∈
        (insert none ((linkNeighbors R (ringSite i) j hij).image Option.some) : Finset (Option (Fin 11)))
      simp [hb]
    | some k =>
      have hh : (linkGraph R (ringSite i)).Adj j k ↔
          k ∈ linkNeighbors R (ringSite i) j hij := by
        change k ∈ (linkGraph R (ringSite i)).neighborSet j ↔
          k ∈ (linkNeighbors R (ringSite i) j hij : Set (Fin 11))
        rw [link_neighborSet_eq R hij]
      change (linkGraph R (ringSite i)).Adj j k ↔ (some k : Option (Fin 11)) ∈
        (insert none ((linkNeighbors R (ringSite i) j hij).image Option.some) : Finset (Option (Fin 11)))
      simpa [Finset.mem_image] using hh
  · rw [if_neg hb]
    cases k with
    | none =>
      change BoundaryNeighbor i j ↔ (none : Option (Fin 11)) ∈
        (linkNeighbors R (ringSite i) j hij).image Option.some
      simp [hb,Finset.mem_image]
    | some k =>
      have hh : (linkGraph R (ringSite i)).Adj j k ↔
          k ∈ linkNeighbors R (ringSite i) j hij := by
        change k ∈ (linkGraph R (ringSite i)).neighborSet j ↔
          k ∈ (linkNeighbors R (ringSite i) j hij : Set (Fin 11))
        rw [link_neighborSet_eq R hij]
      change (linkGraph R (ringSite i)).Adj j k ↔ (some k : Option (Fin 11)) ∈
        (linkNeighbors R (ringSite i) j hij).image Option.some
      simpa [Finset.mem_image] using hh

theorem augmented_real_degree_two {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {j : Fin 11} (hj : Neighbor R (ringSite i) j) :
    ((augmentedLink R i).neighborSet (some j)).ncard = 2 := by
  classical
  obtain ⟨a,hai,haj⟩ := hj.2
  have hdeg := actual_link_degree h hr R hj.1.symm hai haj
  rw [augmented_real_neighborSet R i hj.1.symm,Set.ncard_coe_finset]
  have hn : none ∉ (linkNeighbors R (ringSite i) j hj.1.symm).image Option.some := by
    simp [Finset.mem_image]
  by_cases hb : BoundaryNeighbor i j
  · rw [if_pos hb,Finset.card_insert_of_notMem hn,
      Finset.card_image_of_injective _ (Option.some_injective (Fin 11))]
    rw [if_pos ((boundary_labels_fixed_ring i j).mpr hb)] at hdeg
    omega
  · rw [if_neg hb,Finset.card_image_of_injective _ (Option.some_injective (Fin 11))]
    have hnb : ¬ BoundaryLabels (ringSite i) j := fun hh => hb ((boundary_labels_fixed_ring i j).mp hh)
    rwa [if_neg hnb] at hdeg

theorem included_of_augmented_adj {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {j k : Option (Fin 11)} (hjk : (augmentedLink R i).Adj j k) : Included R i j := by
  cases j with
  | none => exact True.intro
  | some j =>
    cases k with
    | some k => exact neighbor_of_link_adj R hjk
    | none =>
      have hn := actual_boundary_neighbors h hr R i
      rcases hjk with rfl | rfl
      · exact hn.1
      · exact hn.2

theorem augmented_isCycles {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    (augmentedLink R i).IsCycles := by
  intro j hj
  obtain ⟨k,hjk⟩ := hj
  have hJ := included_of_augmented_adj h hr R i hjk
  cases j
  · exact circle_degree_two R i
  · exact augmented_real_degree_two h hr R i hJ

theorem actual_augmented_ring_cycle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    ∃ p : (augmentedLink R i).Walk none none, p.IsCycle ∧
      p.toSubgraph.verts = {j : Option (Fin 11) | Included R i j} := by
  classical
  let G := augmentedLink R i
  let C := G.connectedComponentMk none
  have hc : G.IsCycles := augmented_isCycles h hr R i
  have hne : (G.neighborSet none).Nonempty := ⟨some (prevSite i),Or.inl rfl⟩
  have hC : C.supp = {j : Option (Fin 11) | Included R i j} := by
    ext j
    constructor
    · intro hj
      by_cases hjnone : j = none
      · subst j
        exact True.intro
      have hreach : G.Reachable j none :=
        C.reachable_of_mem_supp hj SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hsupp := SimpleGraph.mem_support_of_reachable hjnone hreach
      obtain ⟨k,hjk⟩ := SimpleGraph.mem_support G |>.mp hsupp
      exact included_of_augmented_adj h hr R i hjk
    · intro hj
      change G.connectedComponentMk j = G.connectedComponentMk none
      exact SimpleGraph.ConnectedComponent.sound (actual_augmented_ring_link_reachable h hr R i hj).symm
  obtain ⟨p,hp,hv⟩ := hc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C) SimpleGraph.ConnectedComponent.connectedComponentMk_mem hne
  exact ⟨p,hp,hv.trans hC⟩

end N11Formalization.ActualAugmentedRingLinkCycles
#check @N11Formalization.ActualAugmentedRingLinkCycles.actual_augmented_ring_cycle
#print axioms N11Formalization.ActualAugmentedRingLinkCycles.augmented_real_degree_two
#print axioms N11Formalization.ActualAugmentedRingLinkCycles.actual_augmented_ring_cycle
