import N11Formalization.ActualPositiveFacetGraph
import N11Formalization.ActualHubFacetComplete
import N11Formalization.ActualIncidentPolygonFacets

/-! Each ACTUAL hub has at least two distinct positive ring neighbors,
in addition to the positive hub edge. Produced from the two true hub-edge
endpoints and actual incident polygon sides; no triangulated-disk/degree
classification premise and no guessed canonical ring labels. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubPositiveDegree
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualHubFacetComplete ActualClippedMeshVertices ActualClippedFacetIntervals
open ActualPositiveFacetGraph ActualIncidentPolygonOrder ActualIncidentPolygonFacets
open ActualIncidentFacetGerms ActualVoronoiRadialExit ActualHubEdgeEndpointGeometry

theorem rotation_neighbors_distinct {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i : Fin n, finRotate n i ≠ (finRotate n).symm i := by
  interval_cases n <;> decide

theorem facetGerm_positivePair {c : Fin 11 → Point} {r : ℝ}
    {v : Point} {i j : Fin 11} (hij : i ≠ j) (g : FacetGerm c r v i j) :
    PositivePair c i j := by
  have hh : 0 < g.time/2 := by linarith [g.positive]
  have hle : g.time/2 ≤ g.time := by linarith [g.positive]
  exact ⟨hij,ray v g.direction (g.time/2),
    ⟨mem_unitDisk.mpr (g.inside _ hh hle).le,g.nearest _ hh hle⟩,
    ray v g.direction g.time,
    ⟨mem_unitDisk.mpr (g.inside _ g.positive le_rfl).le,g.nearest _ g.positive le_rfl⟩,
    ActualIncidentFacetGerms.FacetGerm.positive_segment g⟩

theorem true_vertex_other_positive_neighbor {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (F : InteriorFace c r)
    {i j : Fin 11} (hij : i ≠ j)
    (hi : i ∈ incident c F.point) (hj : j ∈ incident c F.point) :
    ∃ k : Fin 11, k ≠ i ∧ k ≠ j ∧ k ∈ incident c F.point ∧ PositivePair c i k := by
  obtain ⟨o⟩ := ActualIncidentPolygonOrder.InteriorFace.orderedCircle F h.injective
  let I := o.order.symm ⟨i,hi⟩
  have hI : (o.order I).val = i := congrArg Subtype.val (o.order.apply_symm_apply ⟨i,hi⟩)
  let N := finRotate (incident c F.point).card I
  let P := (finRotate (incident c F.point).card).symm I
  have hNne : N ≠ I := (rotate_ne (by have h := F.at_least_three; omega) I).symm
  have hPne : P ≠ I := by
    intro he
    have hh := congrArg (finRotate (incident c F.point).card) he
    rw [(finRotate _).apply_symm_apply] at hh
    exact hNne hh.symm
  have hNP : N ≠ P := rotation_neighbors_distinct F.at_least_three F.at_most_five I
  have hln : (o.order N).val ≠ i := by
    rw [← hI]
    exact (ActualIncidentFacetAdjacency.OrderedCircle.label_injective o).ne hNne
  have hlp : (o.order P).val ≠ i := by
    rw [← hI]
    exact (ActualIncidentFacetAdjacency.OrderedCircle.label_injective o).ne hPne
  by_cases hNj : (o.order N).val = j
  · have hPj : (o.order P).val ≠ j := by
      intro he
      have hh := (ActualIncidentFacetAdjacency.OrderedCircle.label_injective o) (hNj.trans he.symm)
      exact hNP hh
    obtain ⟨g⟩ := OrderedCircle.adjacent_facets o h.cover P
    have hback : finRotate (incident c F.point).card P = I := (finRotate _).apply_symm_apply I
    have hp := facetGerm_positivePair
      ((ActualIncidentFacetAdjacency.OrderedCircle.label_injective o).ne (rotate_ne
        (by have h := F.at_least_three; omega) P)) g
    rw [hback,hI] at hp
    exact ⟨(o.order P).val,hlp,hPj,(o.order P).property,PositivePair.symm hp⟩
  · obtain ⟨g⟩ := OrderedCircle.adjacent_facets o h.cover I
    have hp := facetGerm_positivePair
      ((ActualIncidentFacetAdjacency.OrderedCircle.label_injective o).ne (rotate_ne
        (by have h := F.at_least_three; omega) I)) g
    rw [hI] at hp
    exact ⟨(o.order N).val,hln,hNj,(o.order N).property,hp⟩

theorem actual_hub_two_ring_neighbors {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 11}
    (hij : i ≠ j) (hubs : (i = 9 ∧ j = 10) ∨ (i = 10 ∧ j = 9)) :
    ∃ k l : Fin 11, k.val < 9 ∧ l.val < 9 ∧ k ≠ l ∧
      PositivePair c i k ∧ PositivePair c i l ∧ PositivePair c i j := by
  obtain ⟨H⟩ := ActualHubFacetComplete.Representative.hubFacet h hr
  obtain ⟨F,hF⟩ := clipped_vertex_face h hr H.left_vertex
  obtain ⟨G,hG⟩ := clipped_vertex_face h hr H.right_vertex
  have hFG : F.point ≠ G.point := by
    rw [hF,hG]
    exact ActualClippedFacetInterior.FacetInterval.endpoints_ne H.interval H.positive
  have hhubnear (V : Point) (hV : V ∈ Cell c 9 ∩ Cell c 10) :
      V ∈ Cell c i ∩ Cell c j := by
    rcases hubs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hV
    · exact ⟨hV.2,hV.1⟩
  have hFn : F.point ∈ Cell c i ∩ Cell c j := by rw [hF]; exact hhubnear _ H.interval.left_mem.2
  have hGn : G.point ∈ Cell c i ∩ Cell c j := by rw [hG]; exact hhubnear _ H.interval.right_mem.2
  obtain ⟨k,hki,hkj,hk,hik⟩ := true_vertex_other_positive_neighbor h F hij
    (mem_incident.mpr hFn.1) (mem_incident.mpr hFn.2)
  obtain ⟨l,hli,hlj,hl,hil⟩ := true_vertex_other_positive_neighbor h G hij
    (mem_incident.mpr hGn.1) (mem_incident.mpr hGn.2)
  have hrings (a : Fin 11) (hai : a ≠ i) (haj : a ≠ j) : a.val < 9 := by
    have ha := a.isLt
    rcases hubs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have h9 : a.val ≠ 9 := fun he => hai (Fin.ext he)
      have h10 : a.val ≠ 10 := fun he => haj (Fin.ext he)
      omega
    · have h9 : a.val ≠ 9 := fun he => haj (Fin.ext he)
      have h10 : a.val ≠ 10 := fun he => hai (Fin.ext he)
      omega
  have hkl : k ≠ l := by
    intro he
    rw [← he] at hl
    rcases two_points_three_sites (fun he => hij (h.injective he)) hFG
      (le_antisymm (hFn.1 j) (hFn.2 i)) (le_antisymm (hGn.1 j) (hGn.2 i))
      (le_antisymm ((mem_incident.mp hk) i) (hFn.1 k))
      (le_antisymm ((mem_incident.mp hl) i) (hGn.1 k)) with he | he
    · exact hki (h.injective he)
    · exact hkj (h.injective he)
  have hpos910 : PositivePair c 9 10 :=
    ⟨by decide,_,H.interval.left_mem,_,H.interval.right_mem,
      ActualClippedFacetInterior.FacetInterval.endpoints_ne H.interval H.positive⟩
  have hposij : PositivePair c i j := by
    rcases hubs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hpos910
    · exact PositivePair.symm hpos910
  exact ⟨k,l,hrings k hki hkj,hrings l hli hlj,hkl,hik,hil,hposij⟩

end N11Formalization.ActualHubPositiveDegree
#check @N11Formalization.ActualHubPositiveDegree.actual_hub_two_ring_neighbors
#print axioms N11Formalization.ActualHubPositiveDegree.true_vertex_other_positive_neighbor
#print axioms N11Formalization.ActualHubPositiveDegree.actual_hub_two_ring_neighbors
