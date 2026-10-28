import N11Formalization.ActualRingLinkBoundaryData

/-! The ACTUAL ring link plus one circle node is connected on ALL selected
neighbors. The circle node joins exactly the two produced boundary neighbors.
Real clipped-cell frontier connectedness pays the global closed-cut argument,
including points with a single nearest site onS1. No ring-link path premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualAugmentedRingLinkConnected
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementLocalLinks ActualRefinementVertexLinks ActualRingLinkBoundaryData
open ActualClippedCellPartition ActualClippedCellFrontiers ActualHubLinkConnected
open ActualRingDirectionOrder

def BoundaryNeighbor (i : Fin 9) (j : Fin 11) : Prop :=
  j = prevSite i ∨ j = nextSite i

def augmentedLink {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9) :
    SimpleGraph (Option (Fin 11)) where
  Adj
    | some j, some k => (linkGraph R (ringSite i)).Adj j k
    | none, some j => BoundaryNeighbor i j
    | some j, none => BoundaryNeighbor i j
    | none, none => False
  symm := ⟨by
    intro j k hjk
    cases j <;> cases k
    · exact hjk
    · exact hjk
    · exact hjk
    · exact SimpleGraph.Adj.symm hjk⟩
  loopless := ⟨by
    intro j hj
    cases j
    · exact hj
    · exact SimpleGraph.irrefl _ hj⟩

def Included {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9) :
    Option (Fin 11) → Prop
  | none => True
  | some j => Neighbor R (ringSite i) j

def tagCell (c : Fin 11 → Point) : Option (Fin 11) → Set Point
  | none => {x : Point | ‖x‖ = 1}
  | some j => Cell c j

theorem tagCell_closed (c : Fin 11 → Point) (j : Option (Fin 11)) :
    IsClosed (tagCell c j) := by
  cases j
  · exact isClosed_eq continuous_norm continuous_const
  · exact cell_closed _ _

def someLinkHom {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9) :
    linkGraph R (ringSite i) →g augmentedLink R i where
  toFun := Option.some
  map_rel' := by
    intro j k h
    exact h

theorem common_frontier_tags_reachable {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {x : Point} (hx : x ∈ frontier (ClippedCell c (ringSite i)))
    {j k : Option (Fin 11)} (hJ : Included R i j) (hK : Included R i k)
    (hxj : x ∈ tagCell c j) (hxk : x ∈ tagCell c k) :
    (augmentedLink R i).Reachable j k := by
  have hmem := clipped_frontier_mem hx
  cases j with
  | none =>
    cases k with
    | none => exact SimpleGraph.Reachable.rfl
    | some k =>
      have hn := other_circle_label_boundary_neighbor h hr i hK.1 hxj hmem.2 hxk
      have hadj : (augmentedLink R i).Adj none (some k) := hn
      exact hadj.reachable
  | some j =>
    cases k with
    | none =>
      have hn := other_circle_label_boundary_neighbor h hr i hJ.1 hxk hmem.2 hxj
      have hadj : (augmentedLink R i).Adj (some j) none := hn
      exact hadj.reachable
    | some k =>
      exact (shared_nearest_neighbors_reachable h.injective R hmem.1 hmem.2 hxj hxk hJ hK).map
        (someLinkHom R i)

def tagUnion (c : Fin 11 → Point) (s : Finset (Option (Fin 11))) : Set Point :=
  ⋃ j ∈ s, tagCell c j

theorem tagUnion_closed (c : Fin 11 → Point) (s : Finset (Option (Fin 11))) :
    IsClosed (tagUnion c s) := isClosed_biUnion_finset (fun j _ => tagCell_closed c j)

theorem actual_augmented_ring_link_reachable {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {v : Option (Fin 11)} (hv : Included R i v) :
    (augmentedLink R i).Reachable none v := by
  classical
  by_contra hnot
  let N := Finset.univ.filter (Included R i)
  let s := N.filter (fun j => (augmentedLink R i).Reachable none j)
  let A := tagUnion c s
  let B := tagUnion c (N \ s)
  let X := frontier (ClippedCell c (ringSite i))
  have hconn : IsPreconnected X :=
    (actual_clipped_frontier_pathConnected h (ringSite i)).isConnected.isPreconnected
  have hvN : v ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
  have hvnot : v ∉ s := fun hs => hnot (Finset.mem_filter.mp hs).2
  have hpoint (j : Option (Fin 11)) (hJ : Included R i j) :
      ∃ x : Point, x ∈ X ∧ x ∈ tagCell c j := by
    cases j with
    | none => exact actual_circle_frontier_point h hr i
    | some j =>
      obtain ⟨a,hai,haj⟩ := hJ.2
      have hpair : R.witness a ∈ Cell c (ringSite i) ∩ Cell c j :=
        ⟨ActualRefinementSideMultiplicity.nearest_of_label_mem R hai,
          ActualRefinementSideMultiplicity.nearest_of_label_mem R haj⟩
      exact ⟨R.witness a,clipped_pair_frontier h.injective hJ.1.symm
        (mem_unitDisk.mpr (Refinement.real_triangle R a).1.le) hpair,hpair.2⟩
  have htag (x : Point) (hx : x ∈ X) :
      ∃ j : Option (Fin 11), Included R i j ∧ x ∈ tagCell c j := by
    by_cases hxn : ‖x‖ = 1
    · exact ⟨none,True.intro,hxn⟩
    · have hinside : ‖x‖ < 1 := lt_of_le_of_ne (mem_unitDisk.mp (clipped_frontier_mem hx).1) hxn
      obtain ⟨j,hNj,hxj⟩ := selected_neighbor_at_inside_frontier h hr R hx hinside
      exact ⟨some j,hNj,hxj⟩
  have hcover : X ⊆ A ∪ B := by
    intro x hx
    obtain ⟨j,hJ,hxj⟩ := htag x hx
    have hjN : j ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hJ⟩
    by_cases hjs : j ∈ s
    · exact Or.inl (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hjs,hxj⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hjN,hjs⟩,hxj⟩⟩)
  have hdis : X ∩ (A ∩ B) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hA,hB⟩
    obtain ⟨j,hJa⟩ := Set.mem_iUnion.mp hA
    obtain ⟨hjs,hxj⟩ := Set.mem_iUnion.mp hJa
    obtain ⟨k,hKb⟩ := Set.mem_iUnion.mp hB
    obtain ⟨hkns,hxk⟩ := Set.mem_iUnion.mp hKb
    have hjN := (Finset.mem_filter.mp hjs).1
    have hkN := (Finset.mem_sdiff.mp hkns).1
    have hJ := (Finset.mem_filter.mp hjN).2
    have hK := (Finset.mem_filter.mp hkN).2
    have hreach := common_frontier_tags_reachable h hr R i hx hJ hK hxj hxk
    exact (Finset.mem_sdiff.mp hkns).2 (Finset.mem_filter.mpr
      ⟨hkN,((Finset.mem_filter.mp hjs).2).trans hreach⟩)
  have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hconn A B
    (tagUnion_closed c s) (tagUnion_closed c (N \ s)) hcover hdis
  rcases hsplit with hA | hB
  · obtain ⟨x,hx,hxv⟩ := hpoint v hv
    obtain ⟨j,hJ⟩ := Set.mem_iUnion.mp (hA hx)
    obtain ⟨hjs,hxj⟩ := Set.mem_iUnion.mp hJ
    have hjInc := (Finset.mem_filter.mp (Finset.mem_filter.mp hjs).1).2
    have hjv := common_frontier_tags_reachable h hr R i hx hjInc hv hxj hxv
    exact hnot (((Finset.mem_filter.mp hjs).2).trans hjv)
  · obtain ⟨x,hx,hxnone⟩ := hpoint none True.intro
    obtain ⟨j,hJ⟩ := Set.mem_iUnion.mp (hB hx)
    obtain ⟨hjns,hxj⟩ := Set.mem_iUnion.mp hJ
    have hjN := (Finset.mem_sdiff.mp hjns).1
    have hjInc := (Finset.mem_filter.mp hjN).2
    have hnonej := common_frontier_tags_reachable h hr R i hx
      (j := none) (k := j) True.intro hjInc hxnone hxj
    exact (Finset.mem_sdiff.mp hjns).2 (Finset.mem_filter.mpr ⟨hjN,hnonej⟩)

end N11Formalization.ActualAugmentedRingLinkConnected
#check @N11Formalization.ActualAugmentedRingLinkConnected.actual_augmented_ring_link_reachable
#print axioms N11Formalization.ActualAugmentedRingLinkConnected.common_frontier_tags_reachable
#print axioms N11Formalization.ActualAugmentedRingLinkConnected.actual_augmented_ring_link_reachable
