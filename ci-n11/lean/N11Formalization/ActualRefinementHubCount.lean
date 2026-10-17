import N11Formalization.ActualRefinementSideMultiplicity

/-! EXACTLY two selected actual refinement triangles contain both hubs.
This is actual face-count, not just cardinality of primal witnesses. Local
side multiplicity excludes duplicate triangles at each true endpoint; the
two retained endpoint triangles prove the lower count. No disk/Euler premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementHubCount
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementSideMultiplicity ActualRefinementFacetRetention
open ActualHubFacetComplete ActualClippedFacetInterior ActualClippedMeshVertices

def hubTriangles {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) : Finset R.Index := by
  classical
  exact Finset.univ.filter (fun a => 9 ∈ labelSet R a ∧ 10 ∈ labelSet R a)

theorem hub_triangle_witness {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {a : R.Index} (ha : a ∈ hubTriangles R) : R.witness a ∈ HubVertices c := by
  classical
  have hm := (Finset.mem_filter.mp ha).2
  exact ⟨Refinement.witness_exact_vertex R a,nearest_of_label_mem R hm.1,nearest_of_label_mem R hm.2⟩

theorem hub_triangle_witness_injective {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (h : Representative c r) (hr : r < 19/50) :
    Set.InjOn R.witness (hubTriangles R : Set R.Index) := by
  classical
  obtain ⟨F⟩ := ActualHubFacetComplete.Representative.hubFacet h hr
  intro a ha b hb hw
  have hwa := hub_triangle_witness R ha
  rw [F.exactly_two] at hwa
  have hA := (Finset.mem_filter.mp ha).2
  have hB := (Finset.mem_filter.mp hb).2
  exact same_witness_positive_side_unique R h.injective (by decide) F.interval F.positive
    hwa hw hA.1 hA.2 hB.1 hB.2

theorem actual_hub_triangle_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (hubTriangles R).card = 2 := by
  classical
  obtain ⟨F⟩ := ActualHubFacetComplete.Representative.hubFacet h hr
  have himage : (hubTriangles R).image R.witness ⊆
      {ActualVoronoiRadialExit.ray F.interval.base F.interval.direction F.interval.lo,
       ActualVoronoiRadialExit.ray F.interval.base F.interval.direction F.interval.hi} := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    have hw := hub_triangle_witness R ha
    rw [F.exactly_two] at hw
    exact Finset.mem_insert.mpr (hw.imp_right Finset.mem_singleton.mpr)
  have hle := Finset.card_le_card himage
  rw [Finset.card_image_of_injOn (hub_triangle_witness_injective R h hr)] at hle
  have htwo : ({ActualVoronoiRadialExit.ray F.interval.base F.interval.direction F.interval.lo,
       ActualVoronoiRadialExit.ray F.interval.base F.interval.direction F.interval.hi} : Finset Point).card = 2 := by
    simp [FacetInterval.endpoints_ne F.interval F.positive]
  rw [htwo] at hle
  obtain ⟨a,b,hab,_,ha9,ha10,hb9,hb10⟩ := Refinement.hub_edge_two_retained R h hr
  have ha : a ∈ hubTriangles R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    mem_labelSet.mpr ha9,mem_labelSet.mpr ha10⟩
  have hb : b ∈ hubTriangles R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    mem_labelSet.mpr hb9,mem_labelSet.mpr hb10⟩
  have hsub : ({a,b} : Finset R.Index) ⊆ hubTriangles R := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact ha
    · have he := Finset.mem_singleton.mp hk
      subst k
      exact hb
  have hge := Finset.card_le_card hsub
  have hcard : ({a,b} : Finset R.Index).card = 2 := by simp [hab]
  rw [hcard] at hge
  omega

end N11Formalization.ActualRefinementHubCount
#check @N11Formalization.ActualRefinementHubCount.actual_hub_triangle_count
#print axioms N11Formalization.ActualRefinementHubCount.hub_triangle_witness_injective
#print axioms N11Formalization.ActualRefinementHubCount.actual_hub_triangle_count
