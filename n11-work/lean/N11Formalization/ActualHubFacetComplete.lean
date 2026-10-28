import N11Formalization.ActualBoundaryFacetUniqueness

/-! Complete ACTUAL hub facet: a positive compact segment with two distinct
true interior nearest vertices, and NO other hub-containing primal vertices.
Endpoint ring labels remain unclassified; neither is renamed canonical0/4. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubFacetComplete
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedFacetIntervals
open ActualClippedFacetInterior ActualBoundaryFacetUniqueness ActualClippedMeshVertices
open ActualCoverStructuralReduction ActualVoronoiRadialExit

def HubVertices (c : Fin 11 → Point) : Set Point :=
  ClippedVertices c ∩ (Cell c 9 ∩ Cell c 10)

structure HubFacet (c : Fin 11 → Point) where
  interval : FacetInterval c 9 10
  positive : interval.lo < interval.hi
  left_vertex : ray interval.base interval.direction interval.lo ∈ ClippedVertices c
  right_vertex : ray interval.base interval.direction interval.hi ∈ ClippedVertices c
  exactly_two : HubVertices c =
    {ray interval.base interval.direction interval.lo,ray interval.base interval.direction interval.hi}

theorem Representative.hubFacet {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) : Nonempty (HubFacet c) := by
  obtain ⟨x,y,hx,hy,hxy⟩ := h.hub_edge
  have hxD : x ∈ unitDisk := mem_unitDisk.mpr (h.cells.inside 9 (by decide) x hx.1).le
  have hyD : y ∈ unitDisk := mem_unitDisk.mpr (h.cells.inside 9 (by decide) y hy.1).le
  obtain ⟨f⟩ := clippedCommon_interval h.injective (by decide : (9 : Fin 11) ≠ 10)
    ⟨x,hxD,hx⟩
  have hpos := (FacetInterval.positive_iff f).mpr ⟨x,⟨hxD,hx⟩,y,⟨hyD,hy⟩,hxy⟩
  have hleft : ray f.base f.direction f.lo ∈ ClippedVertices c := by
    rcases f.left_endpoint with hcircle | hv
    · have hi := h.cells.inside 9 (by decide) _ f.left_mem.2.1
      rw [hcircle] at hi
      exact (lt_irrefl 1 hi).elim
    · exact hv
  have hright : ray f.base f.direction f.hi ∈ ClippedVertices c := by
    rcases f.right_endpoint with hcircle | hv
    · have hi := h.cells.inside 9 (by decide) _ f.right_mem.2.1
      rw [hcircle] at hi
      exact (lt_irrefl 1 hi).elim
    · exact hv
  refine ⟨⟨f,hpos,hleft,hright,?_⟩⟩
  ext z
  constructor
  · intro hz
    exact FacetInterval.vertex_is_endpoint h hr (by decide) f hz.1 ⟨hz.1.1,hz.2⟩
  · rintro (he | he)
    · subst z
      exact ⟨hleft,f.left_mem.2⟩
    · subst z
      exact ⟨hright,f.right_mem.2⟩

theorem HubFacet.vertices_card {c : Fin 11 → Point} (f : HubFacet c) :
    (HubVertices c).ncard = 2 := by
  rw [f.exactly_two]
  exact Set.ncard_pair (FacetInterval.endpoints_ne f.interval f.positive)

theorem Representative.hub_vertices_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) : (HubVertices c).ncard = 2 := by
  obtain ⟨f⟩ := Representative.hubFacet h hr
  exact HubFacet.vertices_card f

theorem hub_containing_face_two_points {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    ∃ a b : Point, a ≠ b ∧ ‖a‖ < 1 ∧ ‖b‖ < 1 ∧
      ∀ F : InteriorFace c r, 9 ∈ incident c F.point → 10 ∈ incident c F.point →
        F.point = a ∨ F.point = b := by
  obtain ⟨f⟩ := Representative.hubFacet h hr
  refine ⟨ray f.interval.base f.interval.direction f.interval.lo,
    ray f.interval.base f.interval.direction f.interval.hi,
    FacetInterval.endpoints_ne f.interval f.positive,
    clipped_vertex_inside h hr f.left_vertex,clipped_vertex_inside h hr f.right_vertex,?_⟩
  intro F h9 h10
  have hFv : F.point ∈ ClippedVertices c := by
    have hthree := F.at_least_three
    obtain ⟨k,hk,hk9,hk10⟩ :
        ∃ k ∈ incident c F.point, k ≠ (9 : Fin 11) ∧ k ≠ 10 := by
      by_contra hnot
      have hsub : incident c F.point ⊆ ({9,10} : Finset (Fin 11)) := by
        intro k hk
        by_cases hk9 : k = 9
        · simp [hk9]
        by_cases hk10 : k = 10
        · simp [hk10]
        exact (hnot ⟨k,hk,hk9,hk10⟩).elim
      have hc := Finset.card_le_card hsub
      have ht : ({9,10} : Finset (Fin 11)).card = 2 := by decide
      rw [ht] at hc
      omega
    exact ⟨mem_unitDisk.mpr F.inside.le,triple_mem_vertices (by decide) hk9 hk10
      (mem_incident.mp h9) (mem_incident.mp h10) (mem_incident.mp hk)⟩
  have hmem : F.point ∈ HubVertices c :=
    ⟨hFv,mem_incident.mp h9,mem_incident.mp h10⟩
  rwa [f.exactly_two] at hmem

end N11Formalization.ActualHubFacetComplete
#check @N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#check @N11Formalization.ActualHubFacetComplete.hub_containing_face_two_points
#print axioms N11Formalization.ActualHubFacetComplete.Representative.hub_vertices_card
#print axioms N11Formalization.ActualHubFacetComplete.hub_containing_face_two_points
