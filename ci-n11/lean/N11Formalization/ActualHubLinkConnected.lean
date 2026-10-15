import N11Formalization.ActualRefinementVertexLinks
import N11Formalization.ActualClippedCellFrontiers
import N11Formalization.ActualHubPositiveDegree

/-! Actual hub links are connected on ALL selected neighbors, including
artificial diagonal neighbors. The connected true hub-cell frontier and
local vertex links rule out every closed-cell cut. No cyclic-link, planar
disk, Euler or two-fan premise is introduced. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubLinkConnected
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementVertexLinks ActualRefinementLocalLinks ActualClippedCellFrontiers
open ActualPositiveFacetGraph ActualRefinementFacetRetention ActualHubPositiveDegree
open ActualClippedMeshVertices ActualClippedFacetIntervals

theorem pair_point_cell_frontier {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) {x : Point}
    (hx : x ∈ Cell c i ∩ Cell c j) : x ∈ frontier (Cell c i) := by
  rw [frontier,(cell_closed c i).closure_eq]
  refine ⟨hx.1,?_⟩
  intro hxint
  have hs := ActualClippedCellPartition.interior_cell_strict hc hxint
  exact not_lt_of_ge (hx.2 i) (hs j hij.symm)

theorem shared_nearest_neighbors_reachable {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {x : Point} (hx : x ∈ unitDisk) {i j k : Fin 11}
    (hi : x ∈ Cell c i) (hj : x ∈ Cell c j) (hk : x ∈ Cell c k)
    (hNj : Neighbor R i j) (hNk : Neighbor R i k) :
    (linkGraph R i).Reachable j k := by
  by_cases hjk : j = k
  · rw [hjk]
  have hv : x ∈ ClippedVertices c :=
    ⟨hx,triple_mem_vertices hNj.1.symm hNk.1 (Ne.symm hjk) hi hj hk⟩
  let V : R.vertices := ⟨x,(R.exact_vertices x).mpr hv⟩
  have hbase : (R.face V).point = x := R.base V
  apply common_vertex_link_reachable hc R V
  · rwa [hbase]
  · rwa [hbase]
  · rwa [hbase]
  · exact hNj
  · exact hNk

theorem selected_neighbor_at_hub_frontier {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 11} (hi : 9 ≤ i.val) {x : Point} (hx : x ∈ frontier (Cell c i)) :
    ∃ j : Fin 11, Neighbor R i j ∧ x ∈ Cell c j := by
  have hg := actual_hub_frontier_geometry h hi hx
  obtain ⟨j,hji,hxj⟩ := hg.2.2.2
  have hpos : ∃ k : Fin 11, k ≠ i ∧ x ∈ Cell c k ∧ PositivePair c i k := by
    by_cases hv : x ∈ ClippedVertices c
    · obtain ⟨F,hF⟩ := clipped_vertex_face h hr hv
      have hFi : F.point ∈ Cell c i := by rw [hF]; exact hg.2.2.1
      have hFj : F.point ∈ Cell c j := by rwa [hF]
      obtain ⟨k,hki,_,hk,hik⟩ := true_vertex_other_positive_neighbor h F hji.symm
        (mem_incident.mpr hFi) (mem_incident.mpr hFj)
      refine ⟨k,hki,?_,hik⟩
      have hnear := mem_incident.mp hk
      rwa [hF] at hnear
    · exact ⟨j,hji,hxj,vertex_free_pair_positive h.injective h.cover hji.symm
        hg.1 hv ⟨hg.2.2.1,hxj⟩⟩
  obtain ⟨k,hki,hxk,hik⟩ := hpos
  obtain ⟨a,hai,hak⟩ := Refinement.positive_pair_retained R h hr hik
  exact ⟨k,⟨hki,a,mem_labelSet.mpr hai,mem_labelSet.mpr hak⟩,hxk⟩

theorem actual_hub_link_reachable {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 11} (hi : 9 ≤ i.val) {u v : Fin 11}
    (hu : Neighbor R i u) (hv : Neighbor R i v) :
    (linkGraph R i).Reachable u v := by
  classical
  by_contra hnot
  let N := Finset.univ.filter (Neighbor R i)
  let s := N.filter (fun j => (linkGraph R i).Reachable u j)
  let A := CellUnion c s
  let B := CellUnion c (N \ s)
  let X := frontier (Cell c i)
  have hconn : IsPreconnected X :=
    (actual_hub_frontier_pathConnected h hi).isConnected.isPreconnected
  have huS : u ∈ s := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,SimpleGraph.Reachable.rfl⟩
  have hvN : v ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
  have hvnot : v ∉ s := fun hh => hnot (Finset.mem_filter.mp hh).2
  have hcover : X ⊆ A ∪ B := by
    intro x hx
    obtain ⟨j,hNj,hxj⟩ := selected_neighbor_at_hub_frontier h hr R hi hx
    have hjN : j ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hNj⟩
    by_cases hjS : j ∈ s
    · exact Or.inl (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hjS,hxj⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hjN,hjS⟩,hxj⟩⟩)
  have hdis : X ∩ (A ∩ B) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hA,hB⟩
    obtain ⟨j,hJ⟩ := Set.mem_iUnion.mp hA
    obtain ⟨hjS,hxj⟩ := Set.mem_iUnion.mp hJ
    obtain ⟨k,hK⟩ := Set.mem_iUnion.mp hB
    obtain ⟨hkNS,hxk⟩ := Set.mem_iUnion.mp hK
    have hjN := (Finset.mem_filter.mp hjS).1
    have hkN := (Finset.mem_sdiff.mp hkNS).1
    have hjreach := (Finset.mem_filter.mp hjS).2
    have hNj := (Finset.mem_filter.mp hjN).2
    have hNk := (Finset.mem_filter.mp hkN).2
    have hg := actual_hub_frontier_geometry h hi hx
    have hJK := shared_nearest_neighbors_reachable h.injective R
      (mem_unitDisk.mpr hg.1.le) hg.2.2.1 hxj hxk hNj hNk
    exact (Finset.mem_sdiff.mp hkNS).2 (Finset.mem_filter.mpr ⟨hkN,hjreach.trans hJK⟩)
  have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hconn A B
    (cellUnion_closed c s) (cellUnion_closed c (N \ s)) hcover hdis
  have hpoint (j : Fin 11) (hNj : Neighbor R i j) :
      ∃ x : Point, x ∈ X ∧ x ∈ Cell c j := by
    obtain ⟨a,hai,haj⟩ := hNj.2
    have hpair : R.witness a ∈ Cell c i ∩ Cell c j :=
      ⟨ActualRefinementSideMultiplicity.nearest_of_label_mem R hai,
       ActualRefinementSideMultiplicity.nearest_of_label_mem R haj⟩
    exact ⟨R.witness a,pair_point_cell_frontier h.injective hNj.1.symm hpair,hpair.2⟩
  rcases hsplit with hA | hB
  · obtain ⟨x,hx,hxv⟩ := hpoint v hv
    obtain ⟨j,hJ⟩ := Set.mem_iUnion.mp (hA hx)
    obtain ⟨hjS,hxj⟩ := Set.mem_iUnion.mp hJ
    have hNj := (Finset.mem_filter.mp (Finset.mem_filter.mp hjS).1).2
    have hg := actual_hub_frontier_geometry h hi hx
    have hJV := shared_nearest_neighbors_reachable h.injective R
      (mem_unitDisk.mpr hg.1.le) hg.2.2.1 hxj hxv hNj hv
    exact hnot (((Finset.mem_filter.mp hjS).2).trans hJV)
  · obtain ⟨x,hx,hxu⟩ := hpoint u hu
    obtain ⟨j,hJ⟩ := Set.mem_iUnion.mp (hB hx)
    obtain ⟨hjNS,hxj⟩ := Set.mem_iUnion.mp hJ
    have hjN := (Finset.mem_sdiff.mp hjNS).1
    have hNj := (Finset.mem_filter.mp hjN).2
    have hg := actual_hub_frontier_geometry h hi hx
    have hUJ := shared_nearest_neighbors_reachable h.injective R
      (mem_unitDisk.mpr hg.1.le) hg.2.2.1 hxu hxj hu hNj
    exact (Finset.mem_sdiff.mp hjNS).2 (Finset.mem_filter.mpr ⟨hjN,hUJ⟩)

end N11Formalization.ActualHubLinkConnected
#check @N11Formalization.ActualHubLinkConnected.actual_hub_link_reachable
#print axioms N11Formalization.ActualHubLinkConnected.selected_neighbor_at_hub_frontier
#print axioms N11Formalization.ActualHubLinkConnected.actual_hub_link_reachable
