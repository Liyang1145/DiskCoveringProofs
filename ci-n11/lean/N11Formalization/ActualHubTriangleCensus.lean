import N11Formalization.ActualLocalSurfaceData

/-! Exact hub-face census from the ACTUAL edge incidences.
The total face count is the two actual hub ring-neighbor counts plus q.
This is not Euler F=11: extra shared ring neighbors remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubTriangleCensus
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementInteriorFacetCount
open ActualRefinementVertexLinks ActualRefinementEarCount ActualRefinementHubCount
open ActualHubLinkCycles ActualHubRingPaths ActualCentralRingEndpoints

def siteTriangles {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i : Fin 11) : Finset R.Index := by
  classical
  exact Finset.univ.filter (fun a => i ∈ labelSet R a)

def neighbors {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i : Fin 11) : Finset (Fin 11) := by
  classical
  exact Finset.univ.filter (Neighbor R i)

def ringNeighbors {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i : Fin 11) : Finset (Fin 11) := by
  classical
  exact (neighbors R i).filter (fun j => j.val < 9)

@[simp] theorem mem_siteTriangles {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {i : Fin 11} {a : R.Index} :
    a ∈ siteTriangles R i ↔ i ∈ labelSet R a := by
  classical
  simp [siteTriangles]

@[simp] theorem mem_neighbors {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {i j : Fin 11} : j ∈ neighbors R i ↔ Neighbor R i j := by
  classical
  simp [neighbors]

@[simp] theorem mem_ringNeighbors {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {i j : Fin 11} : j ∈ ringNeighbors R i ↔ Neighbor R i j ∧ j.val < 9 := by
  classical
  simp [ringNeighbors]

theorem triangle_neighbors_above {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {i : Fin 11} {a : R.Index} (ha : a ∈ siteTriangles R i) :
    (neighbors R i).bipartiteAbove (fun t j => j ∈ labelSet R t) a =
      (labelSet R a).erase i := by
  classical
  ext j
  simp only [Finset.bipartiteAbove,Finset.mem_filter,mem_neighbors,Finset.mem_erase]
  constructor
  · rintro ⟨hj,hja⟩
    exact ⟨hj.1,hja⟩
  · rintro ⟨hji,hja⟩
    exact ⟨⟨hji,a,mem_siteTriangles R |>.mp ha,hja⟩,hja⟩

theorem neighbor_triangles_below {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i j : Fin 11) :
    (siteTriangles R i).bipartiteBelow (fun t k => k ∈ labelSet R t) j =
      pairTriangles R i j := by
  classical
  ext a
  simp [Finset.bipartiteBelow,siteTriangles,pairTriangles]

theorem actual_hub_face_neighbor_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 11} (hi : 9 ≤ i.val) :
    (siteTriangles R i).card = (neighbors R i).card := by
  classical
  have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun a j => j ∈ labelSet R a) (s := siteTriangles R i) (t := neighbors R i)
  have hA : ∀ a ∈ siteTriangles R i,
      ((neighbors R i).bipartiteAbove (fun t j => j ∈ labelSet R t) a).card = 2 := by
    intro a ha
    rw [triangle_neighbors_above R ha]
    have hh := Finset.card_erase_add_one ((mem_siteTriangles R).mp ha)
    rw [labelSet_card] at hh
    omega
  have hB : ∀ j ∈ neighbors R i,
      ((siteTriangles R i).bipartiteBelow (fun t k => k ∈ labelSet R t) j).card = 2 := by
    intro j hj
    have hn := (mem_neighbors R).mp hj
    obtain ⟨a,hai,haj⟩ := hn.2
    rw [neighbor_triangles_below]
    have hb : ¬ BoundaryLabels i j := by
      intro hb
      have hk := boundary_labels_ring i j hb
      omega
    simpa only [if_neg hb] using
      ActualSelectedEdgeIncidence.actual_selected_edge_incidence h hr R hn.1.symm hai haj
  rw [Finset.sum_congr rfl hA,Finset.sum_congr rfl hB] at hc
  simp only [Finset.sum_const,smul_eq_mul] at hc
  omega

theorem ringOnly_iff_no_hubs {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) :
    RingOnly R a ↔ 9 ∉ labelSet R a ∧ 10 ∉ labelSet R a := by
  constructor
  · intro ha
    constructor <;> intro hm
    · obtain ⟨v,hv⟩ := mem_labelSet.mp hm
      have hh := ha v
      rw [hv] at hh
      norm_num at hh
    · obtain ⟨v,hv⟩ := mem_labelSet.mp hm
      have hh := ha v
      rw [hv] at hh
      norm_num at hh
  · rintro ⟨h9,h10⟩ v
    have hmem : R.labels a v ∈ labelSet R a := mem_labelSet.mpr ⟨v,rfl⟩
    have hv := (R.labels a v).isLt
    by_contra hn
    have he : R.labels a v = 9 ∨ R.labels a v = 10 := by
      have hh : (R.labels a v).val = 9 ∨ (R.labels a v).val = 10 := by omega
      exact hh.imp (fun he => Fin.ext he) (fun he => Fin.ext he)
    rcases he with he | he
    · exact h9 (he ▸ hmem)
    · exact h10 (he ▸ hmem)

theorem actual_total_face_census {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    Fintype.card R.Index + 2 =
      (neighbors R 9).card + (neighbors R 10).card + (ringOnlyTriangles R).card := by
  classical
  have hi : siteTriangles R 9 ∩ siteTriangles R 10 = hubTriangles R := by
    ext a
    simp [siteTriangles,hubTriangles]
  have hq : ringOnlyTriangles R =
      Finset.univ \ (siteTriangles R 9 ∪ siteTriangles R 10) := by
    ext a
    simp [ringOnlyTriangles,siteTriangles,ringOnly_iff_no_hubs]
  have hsum := Finset.card_union_add_card_inter (siteTriangles R 9) (siteTriangles R 10)
  rw [hi,actual_hub_triangle_count h hr R,
    actual_hub_face_neighbor_count h hr R (by decide : 9 ≤ (9 : Fin 11).val),
    actual_hub_face_neighbor_count h hr R (by decide : 9 ≤ (10 : Fin 11).val)] at hsum
  have hpart := Finset.card_sdiff_add_card_eq_card
    (show siteTriangles R 9 ∪ siteTriangles R 10 ⊆ Finset.univ from Finset.subset_univ _)
  rw [← hq,Finset.card_univ] at hpart
  omega

theorem hub_neighbors_split {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {i u : Fin 11} (hh : (i = 9 ∧ u = 10) ∨ (i = 10 ∧ u = 9))
    (hu : Neighbor R i u) :
    neighbors R i = insert u (ringNeighbors R i) := by
  classical
  ext j
  simp only [mem_neighbors,Finset.mem_insert,mem_ringNeighbors]
  constructor
  · intro hj
    by_cases hju : j = u
    · exact Or.inl hju
    · exact Or.inr ⟨hj,hubs_exhaust i u j hh hj.1 hju⟩
  · rintro (rfl | ⟨hj,_⟩)
    · exact hu
    · exact hj

theorem actual_ring_neighbor_face_census {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    Fintype.card R.Index =
      (ringNeighbors R 9).card + (ringNeighbors R 10).card + (ringOnlyTriangles R).card := by
  classical
  obtain ⟨a,_,_,_,ha9,ha10,_,_⟩ :=
    ActualRefinementFacetRetention.Refinement.hub_edge_two_retained R h hr
  have h9 : Neighbor R 9 10 := ⟨by decide,a,mem_labelSet.mpr ha9,mem_labelSet.mpr ha10⟩
  have h10 : Neighbor R 10 9 := ⟨by decide,a,mem_labelSet.mpr ha10,mem_labelSet.mpr ha9⟩
  have hc := actual_total_face_census h hr R
  rw [hub_neighbors_split R (Or.inl ⟨rfl,rfl⟩) h9,
    hub_neighbors_split R (Or.inr ⟨rfl,rfl⟩) h10] at hc
  have hnot10 : (10 : Fin 11) ∉ ringNeighbors R 9 := by simp
  have hnot9 : (9 : Fin 11) ∉ ringNeighbors R 10 := by simp
  rw [Finset.card_insert_of_notMem hnot10,Finset.card_insert_of_notMem hnot9] at hc
  omega

theorem ring_path_vertices_eq {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {i u : Fin 11}
    (hh : (i = 9 ∧ u = 10) ∨ (i = 10 ∧ u = 9)) (P : RingPath R i u) :
    P.walk.support.toFinset = ringNeighbors R i := by
  classical
  ext j
  rw [List.mem_toFinset,P.exact_vertices,mem_ringNeighbors]
  constructor
  · rintro ⟨hj,hju⟩
    exact ⟨hj,hubs_exhaust i u j hh hj.1 hju⟩
  · rintro ⟨hj,hjr⟩
    refine ⟨hj,?_⟩
    rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> intro he <;> subst j <;> norm_num at hjr

end N11Formalization.ActualHubTriangleCensus
#check @N11Formalization.ActualHubTriangleCensus.actual_ring_neighbor_face_census
#check @N11Formalization.ActualHubTriangleCensus.ring_path_vertices_eq
#print axioms N11Formalization.ActualHubTriangleCensus.actual_hub_face_neighbor_count
#print axioms N11Formalization.ActualHubTriangleCensus.actual_ring_neighbor_face_census
