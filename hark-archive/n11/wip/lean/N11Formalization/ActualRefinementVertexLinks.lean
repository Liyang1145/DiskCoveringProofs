import N11Formalization.ActualRefinementLocalLinks

/-! At every true actual clipped vertex, ANY globally selected neighbors
which are nearest there are joined in the global site link. If their original
triangle witness differs, actual two-witness rigidity forces a positive
polygon side and the local fan still retains it. No local-neighbor premise
is silently assumed from mere nearest incidence. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementVertexLinks
open ActualVoronoiCells ActualVoronoiIncidence ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementSideMultiplicity
open ActualIncidentFanRefinement ActualIncidentFacetAdjacency ActualNearestPairRigidity
open ActualRefinementLocalLinks ActualLocalRefinementPairCounts

def Neighbor {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i j : Fin 11) : Prop :=
  j ≠ i ∧ ∃ a : R.Index, i ∈ labelSet R a ∧ j ∈ labelSet R a

theorem neighbor_local_at_vertex {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} (R : Refinement c r) (v : R.vertices)
    (I J : Fin (incident c (R.face v).point).card) {i j : Fin 11}
    (hI : ((R.order v).order I).val = i) (hJ : ((R.order v).order J).val = j)
    (hn : Neighbor R i j) :
    localNeighbor (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) I J := by
  have hJI : J ≠ I := by
    intro he
    apply hn.1
    rw [← hI,← hJ,he]
  obtain ⟨a,hai,haj⟩ := hn.2
  by_cases hw : R.witness a = (R.face v).point
  · have hv : a.1 = v := by
      apply Subtype.ext
      simpa only [Refinement.witness,R.base] using hw
    rcases a with ⟨w,k⟩
    dsimp only at hv
    subst w
    refine ⟨hJI,k.val,k.property,?_,?_⟩
    · apply (local_label_mem R v k I).mp
      rwa [hI]
    · apply (local_label_mem R v k J).mp
      rwa [hJ]
  · have hp := shared_pair_two_polygons_adjacent hc (R.order v) hJI.symm (Ne.symm hw)
      (by rw [hI,hJ]; exact ⟨nearest_of_label_mem R hai,nearest_of_label_mem R haj⟩)
    have hc1 := adjacent_pair_count (R.face v).at_least_three (R.face v).at_most_five I J hJI.symm hp
    have hne : (pairIndices (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) I J).Nonempty :=
      Finset.card_pos.mp (by rw [hc1]; decide)
    obtain ⟨k,hk⟩ := hne
    have hK := (Finset.mem_filter.mp hk).2
    exact ⟨hJI,k,hK⟩

theorem common_vertex_link_reachable {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} (R : Refinement c r) (v : R.vertices) {i j k : Fin 11}
    (hi : (R.face v).point ∈ Cell c i)
    (hj : (R.face v).point ∈ Cell c j) (hk : (R.face v).point ∈ Cell c k)
    (hnj : Neighbor R i j) (hnk : Neighbor R i k) : (linkGraph R i).Reachable j k := by
  let o := R.order v
  let I := o.order.symm ⟨i,mem_incident.mpr hi⟩
  let J := o.order.symm ⟨j,mem_incident.mpr hj⟩
  let K := o.order.symm ⟨k,mem_incident.mpr hk⟩
  have hI : (o.order I).val = i := congrArg Subtype.val (o.order.apply_symm_apply ⟨i,mem_incident.mpr hi⟩)
  have hJ : (o.order J).val = j := congrArg Subtype.val (o.order.apply_symm_apply ⟨j,mem_incident.mpr hj⟩)
  have hK : (o.order K).val = k := congrArg Subtype.val (o.order.apply_symm_apply ⟨k,mem_incident.mpr hk⟩)
  have hlocJ := neighbor_local_at_vertex hc R v I J hI hJ hnj
  have hlocK := neighbor_local_at_vertex hc R v I K hI hK hnk
  have hh := actual_local_link_reachable R v I J K hlocJ hlocK
  rwa [hI,hJ,hK] at hh

end N11Formalization.ActualRefinementVertexLinks
#check @N11Formalization.ActualRefinementVertexLinks.common_vertex_link_reachable
#print axioms N11Formalization.ActualRefinementVertexLinks.neighbor_local_at_vertex
#print axioms N11Formalization.ActualRefinementVertexLinks.common_vertex_link_reachable
