import N11Formalization.ActualIncidentFacetAdjacency
import N11Formalization.ActualPositiveFacetGraph

/-! Two different genuine common-nearest witnesses force the shared site
chord to be a STRICT supporting side at each incident polygon. Conversely
a nonadjacent incident polygon diagonal has exactly ONE common-nearest
point in the entire plane, not just inD. No genericity or facet assumption. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualNearestPairRigidity
open ActualVoronoiCells ActualVoronoiIncidence ActualIncidentFacetGerms
open ActualVoronoiLocalFan ActualHubEdgeEndpointGeometry ActualIncidentPolygonOrder
open ActualIncidentFacetAdjacency ActualPositiveFacetGraph

theorem two_witnesses_pairCone {c : Fin 11 → Point} (hc : Function.Injective c)
    {u v : Point} (huv : u ≠ v) {i j : Fin 11} (hij : i ≠ j)
    (hu : u ∈ Cell c i ∩ Cell c j) (hv : v ∈ Cell c i ∩ Cell c j) :
    v-u ∈ PairCone c u i j := by
  refine ⟨?_,?_⟩
  · have hdiff := tied_distance_difference (x := v) (le_antisymm (hu.1 j) (hu.2 i))
    have htie := le_antisymm (hv.1 j) (hv.2 i)
    rw [htie,sub_self] at hdiff
    linarith
  · intro k hk hki hkj
    have hnearK := mem_incident.mp hk
    have hle := (tied_le_iff (le_antisymm (hu.1 k) (hnearK i))).mp (hv.1 k)
    apply lt_of_le_of_ne hle
    intro he
    have hdiff := tied_distance_difference (x := v) (le_antisymm (hu.1 k) (hnearK i))
    rw [he,mul_zero] at hdiff
    have hvtie : dist v (c k) = dist v (c i) := by
      nlinarith [dist_nonneg (x := v) (y := c k),dist_nonneg (x := v) (y := c i)]
    rcases two_points_three_sites (fun he => hij (hc he)) huv
      (le_antisymm (hu.1 j) (hu.2 i)) (le_antisymm (hv.1 j) (hv.2 i))
      (le_antisymm (hnearK i) (hu.1 k)) hvtie with he | he
    · exact hki (hc he)
    · exact hkj (hc he)

theorem shared_pair_two_polygons_adjacent {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} {F : InteriorFace c r} (o : OrderedCircle c r F)
    {i j : Fin (incident c F.point).card} (hij : i ≠ j) {v : Point}
    (hFv : F.point ≠ v)
    (hv : v ∈ Cell c (o.order i).val ∩ Cell c (o.order j).val) :
    j = finRotate (incident c F.point).card i ∨
      i = finRotate (incident c F.point).card j := by
  have hlabels := (OrderedCircle.label_injective o).ne hij
  exact OrderedCircle.pairCone_adjacent o hc hij (two_witnesses_pairCone hc hFv hlabels
    ⟨mem_incident.mp (o.order i).property,mem_incident.mp (o.order j).property⟩ hv)

theorem nonadjacent_diagonal_unique_witness {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} {F : InteriorFace c r} (o : OrderedCircle c r F)
    {i j : Fin (incident c F.point).card} (hij : i ≠ j)
    (hn1 : j ≠ finRotate (incident c F.point).card i)
    (hn2 : i ≠ finRotate (incident c F.point).card j) {v : Point}
    (hv : v ∈ Cell c (o.order i).val ∩ Cell c (o.order j).val) : v = F.point := by
  by_contra hvF
  have hcases := shared_pair_two_polygons_adjacent hc o hij (Ne.symm hvF) hv
  exact hcases.elim hn1 hn2

end N11Formalization.ActualNearestPairRigidity
#check @N11Formalization.ActualNearestPairRigidity.two_witnesses_pairCone
#check @N11Formalization.ActualNearestPairRigidity.nonadjacent_diagonal_unique_witness
#print axioms N11Formalization.ActualNearestPairRigidity.two_witnesses_pairCone
#print axioms N11Formalization.ActualNearestPairRigidity.nonadjacent_diagonal_unique_witness
