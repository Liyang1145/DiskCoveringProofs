import N11Formalization.ActualSelectedEarRemoval

/-! Exact productive coverage of ring labels by the two actual hub paths.
Only the selected ear's middle label is missing. Hence F=9+the number
of common hub ring neighbors, without an Euler/disk hypothesis.
The exclusion of extra common neighbors is deliberately NOT asserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubNeighborCoverage
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementEarCount
open ActualRefinementVertexLinks ActualHubTriangleCensus ActualSelectedEarRemoval
open ActualRingDirectionOrder ActualRingLinkBoundaryData

theorem neighbor_symm {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {i j : Fin 11} (h : Neighbor R i j) : Neighbor R j i := by
  obtain ⟨a,hi,hj⟩ := h.2
  exact ⟨h.1.symm,a,hj,hi⟩

theorem ear_center_set_injective : ∀ i j : Fin 9,
    ({prevSite i,ringSite i,nextSite i} : Finset (Fin 11)) =
      {prevSite j,ringSite j,nextSite j} → i = j := by decide +kernel

theorem ringOnly_of_no_hub_neighbor {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {i : Fin 9} {a : R.Index}
    (hi : ringSite i ∈ labelSet R a)
    (h9 : ¬ Neighbor R (ringSite i) 9) (h10 : ¬ Neighbor R (ringSite i) 10) :
    RingOnly R a := by
  apply (ringOnly_iff_no_hubs R a).mpr
  constructor
  · intro ha9
    exact h9 ⟨by intro he; have hh := congrArg Fin.val he; simp [ringSite] at hh; omega,
      a,hi,ha9⟩
  · intro ha10
    exact h10 ⟨by intro he; have hh := congrArg Fin.val he; simp [ringSite] at hh; omega,
      a,hi,ha10⟩

theorem no_hub_neighbor_produces_ear {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    (h9 : ¬ Neighbor R (ringSite i) 9) (h10 : ¬ Neighbor R (ringSite i) 10) :
    ∃ a : R.Index, RingOnly R a ∧
      labelSet R a = {prevSite i,ringSite i,nextSite i} := by
  classical
  obtain ⟨hp,hn⟩ := actual_boundary_neighbors h hr R i
  obtain ⟨a,hai,han⟩ := hn.2
  obtain ⟨b,hbi,hbp⟩ := hp.2
  have hA := ringOnly_of_no_hub_neighbor R hai h9 h10
  have hB := ringOnly_of_no_hub_neighbor R hbi h9 h10
  have hba : b = a := ring_only_indices_unique h hr R hB hA
  rw [hba] at hbp
  refine ⟨a,hA,?_⟩
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hbp
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hai
    · exact Finset.mem_singleton.mp hj ▸ han
  · rw [labelSet_card]
    have hd := boundary_sites_distinct i
    simp [hd.1,hd.2.1,hd.2.2,hd.2.1.symm]

def missingRings {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    Finset (Fin 9) := by
  classical
  exact Finset.univ.filter (fun i =>
    ¬ Neighbor R (ringSite i) 9 ∧ ¬ Neighbor R (ringSite i) 10)

@[simp] theorem mem_missingRings {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {i : Fin 9} :
    i ∈ missingRings R ↔
      ¬ Neighbor R (ringSite i) 9 ∧ ¬ Neighbor R (ringSite i) 10 := by
  classical
  simp [missingRings]

theorem actual_missing_rings_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (missingRings R).card = (ringOnlyTriangles R).card := by
  classical
  have hle : (missingRings R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hI := (mem_missingRings R).mp hi
    have hJ := (mem_missingRings R).mp hj
    obtain ⟨a,ha,hAi⟩ := no_hub_neighbor_produces_ear h hr R i hI.1 hI.2
    obtain ⟨b,hb,hBj⟩ := no_hub_neighbor_produces_ear h hr R j hJ.1 hJ.2
    have hab := ring_only_indices_unique h hr R ha hb
    exact ear_center_set_injective i j (hAi.symm.trans (by rw [hab]; exact hBj))
  have hq := actual_selected_ear_count h hr R
  have hn : (missingRings R).Nonempty ↔ (ringOnlyTriangles R).Nonempty := by
    constructor
    · rintro ⟨i,hi⟩
      have hI := (mem_missingRings R).mp hi
      obtain ⟨a,ha,_⟩ := no_hub_neighbor_produces_ear h hr R i hI.1 hI.2
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
    · rintro ⟨a,ha⟩
      have hA := (Finset.mem_filter.mp ha).2
      obtain ⟨i,hi⟩ := selected_ring_triangle_ear h hr R hA
      exact ⟨i,(mem_missingRings R).mpr (actual_ear_center_no_hub h hr R hi)⟩
  have hn' : 0 < (missingRings R).card ↔ 0 < (ringOnlyTriangles R).card := by
    simpa only [Finset.card_pos] using hn
  omega

def ringSites : Finset (Fin 11) := Finset.univ.filter (fun j => j.val < 9)

theorem ring_sites_card : ringSites.card = 9 := by decide +kernel

@[simp] theorem mem_ringSites {j : Fin 11} : j ∈ ringSites ↔ j.val < 9 := by
  simp [ringSites]

theorem hub_ring_union_subset {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    ringNeighbors R 9 ∪ ringNeighbors R 10 ⊆ ringSites := by
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · exact mem_ringSites.mpr ((mem_ringNeighbors R).mp hj).2
  · exact mem_ringSites.mpr ((mem_ringNeighbors R).mp hj).2

theorem missing_ring_sites_eq {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    ringSites \ (ringNeighbors R 9 ∪ ringNeighbors R 10) =
      (missingRings R).image ringSite := by
  classical
  ext j
  constructor
  · intro hj
    have hJ := Finset.mem_sdiff.mp hj
    let i : Fin 9 := ⟨j.val,mem_ringSites.mp hJ.1⟩
    have hi : ringSite i = j := Fin.ext rfl
    refine Finset.mem_image.mpr ⟨i,(mem_missingRings R).mpr ⟨?_,?_⟩,hi⟩
    · intro hn
      apply hJ.2
      apply Finset.mem_union_left
      exact (mem_ringNeighbors R).mpr ⟨hi ▸ neighbor_symm hn,mem_ringSites.mp hJ.1⟩
    · intro hn
      apply hJ.2
      apply Finset.mem_union_right
      exact (mem_ringNeighbors R).mpr ⟨hi ▸ neighbor_symm hn,mem_ringSites.mp hJ.1⟩
  · rintro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have hI := (mem_missingRings R).mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_ringSites.mpr i.isLt,?_⟩
    intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hI.1 (neighbor_symm ((mem_ringNeighbors R).mp hj).1)
    · exact hI.2 (neighbor_symm ((mem_ringNeighbors R).mp hj).1)

theorem actual_hub_paths_cover_ring_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (ringNeighbors R 9 ∪ ringNeighbors R 10).card + (ringOnlyTriangles R).card = 9 := by
  classical
  have hc := Finset.card_sdiff_add_card_eq_card (hub_ring_union_subset R)
  rw [missing_ring_sites_eq,Finset.card_image_of_injective _ (show Function.Injective ringSite from
    fun i j he => Fin.ext (congrArg (fun k : Fin 11 => k.val) he)),
    actual_missing_rings_card h hr R,ring_sites_card] at hc
  omega

theorem actual_faces_eq_nine_add_common_neighbors {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    Fintype.card R.Index = 9 + (ringNeighbors R 9 ∩ ringNeighbors R 10).card := by
  have hc := actual_ring_neighbor_face_census h hr R
  have hu := actual_hub_paths_cover_ring_count h hr R
  have hs := Finset.card_union_add_card_inter (ringNeighbors R 9) (ringNeighbors R 10)
  omega

end N11Formalization.ActualHubNeighborCoverage
#check @N11Formalization.ActualHubNeighborCoverage.actual_hub_paths_cover_ring_count
#check @N11Formalization.ActualHubNeighborCoverage.actual_faces_eq_nine_add_common_neighbors
#print axioms N11Formalization.ActualHubNeighborCoverage.actual_missing_rings_card
#print axioms N11Formalization.ActualHubNeighborCoverage.actual_faces_eq_nine_add_common_neighbors
