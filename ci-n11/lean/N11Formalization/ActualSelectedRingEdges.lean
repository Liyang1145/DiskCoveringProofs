import N11Formalization.ActualSelectedSkipChordEar

/-! Actual selected ring edges are exactly the nine boundary sides plus
the selected ears' short chords. Their exact count is9+q.
This depends on the productive no-ear skip-chord exclusion, not on Euler. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSelectedRingEdges
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementDoubleCounting
open ActualRefinementEarCount ActualSelectedEarRemoval ActualSelectedSkipChordEar
open ActualHubTriangleCensus
open ActualShortChordHubData ActualHubNeighborCoverage
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualRingLocality
open ActualRefinementSideMultiplicity ActualVoronoiCells

def ringEdges {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    Finset (Finset (Fin 11)) := by
  classical
  exact (edges R).filter (fun e => ∀ j ∈ e, j.val < 9)

def earCenters {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) : Finset (Fin 9) := by
  classical
  exact Finset.univ.filter (SelectedEarAt R)

def chord (i : Fin 9) : Finset (Fin 11) := {prevSite i,nextSite i}

theorem chord_injective : Function.Injective chord := by decide +kernel

theorem ear_set_no_hubs : ∀ i : Fin 9,
    (9 : Fin 11) ∉ ({prevSite i,ringSite i,nextSite i} : Finset (Fin 11)) ∧
      (10 : Fin 11) ∉ ({prevSite i,ringSite i,nextSite i} : Finset (Fin 11)) := by
  decide +kernel

theorem ear_only_rings {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {i : Fin 9} {a : R.Index}
    (ha : labelSet R a = {prevSite i,ringSite i,nextSite i}) : RingOnly R a := by
  rw [ringOnly_iff_no_hubs,ha]
  exact ear_set_no_hubs i

theorem actual_ear_centers_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (earCenters R).card = (ringOnlyTriangles R).card := by
  classical
  have hle : (earCenters R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨A,hA⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨B,hB⟩ := (Finset.mem_filter.mp hj).2
    have hAB := ring_only_indices_unique h hr R (ear_only_rings R hA) (ear_only_rings R hB)
    exact ear_center_set_injective i j (hA.symm.trans (by rw [hAB]; exact hB))
  have hq := actual_selected_ear_count h hr R
  have hn : (earCenters R).Nonempty ↔ (ringOnlyTriangles R).Nonempty := by
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ear_only_rings R ha⟩⟩
    · rintro ⟨a,ha⟩
      obtain ⟨i,hi⟩ := selected_ring_triangle_ear h hr R (Finset.mem_filter.mp ha).2
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,hi⟩⟩
  have hn' : 0 < (earCenters R).card ↔ 0 < (ringOnlyTriangles R).card := by
    simpa only [Finset.card_pos] using hn
  omega

theorem local_pair_boundary_or_skip : ∀ i j : Fin 9, i ≠ j →
    ((j-i).val ≤ 2 ∨ (i-j).val ≤ 2) →
    ActualRefinementInteriorFacetCount.BoundaryLabels (ringSite i) (ringSite j) ∨
      ∃ k : Fin 9, ({ringSite i,ringSite j} : Finset (Fin 11)) = chord k := by
  decide +kernel

theorem selected_edge_card_two {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {e : Finset (Fin 11)} (he : e ∈ edges R) : e.card = 2 := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_powersetCard.mp ha).2

theorem actual_ring_edges_eq {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ringEdges R = boundaryEdges ∪ (earCenters R).image chord := by
  classical
  ext e
  constructor
  · intro he
    have hE := Finset.mem_filter.mp he
    obtain ⟨a,_,hA⟩ := Finset.mem_biUnion.mp hE.1
    have hsub := (Finset.mem_powersetCard.mp hA).1
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
    have hi : i.val < 9 := hE.2 i (by simp)
    have hj : j.val < 9 := hE.2 j (by simp)
    let I : Fin 9 := ⟨i.val,hi⟩
    let J : Fin 9 := ⟨j.val,hj⟩
    have hI : ringSite I = i := Fin.ext rfl
    have hJ : ringSite J = j := Fin.ext rfl
    have hIJ : I ≠ J := fun he => hij (Fin.ext (congrArg (fun k : Fin 9 => k.val) he))
    have hai : i ∈ labelSet R a := hsub (by simp)
    have haj : j ∈ labelSet R a := hsub (by simp)
    have hradI := nearest_le_radius h.cover
      (mem_unitDisk.mpr (Refinement.real_triangle R a).1.le) (nearest_of_label_mem R hai)
    have hradJ := nearest_le_radius h.cover
      (mem_unitDisk.mpr (Refinement.real_triangle R a).1.le) (nearest_of_label_mem R haj)
    have hloc := intersection_local h.cover hr h.labels h.midpoint_order
      (show dist (R.witness a) (c (ringSite I)) ≤ r by rwa [hI])
      (show dist (R.witness a) (c (ringSite J)) ≤ r by rwa [hJ])
    rcases local_pair_boundary_or_skip I J hIJ hloc with hb | ⟨k,hk⟩
    · apply Finset.mem_union_left
      exact (boundary_pair_iff i j hij).mpr (by rwa [hI,hJ] at hb)
    · rw [hI,hJ] at hk
      have hps : prevSite k ∈ labelSet R a := hsub (by rw [hk]; simp [chord])
      have hns : nextSite k ∈ labelSet R a := hsub (by rw [hk]; simp [chord])
      have hear := actual_selected_skip_chord_ear h hr R k
        ⟨(boundary_sites_distinct k).2.2.symm,a,hps,hns⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hear⟩,hk.symm⟩)
  · intro he
    rcases Finset.mem_union.mp he with hb | hc
    · apply Finset.mem_filter.mpr
      refine ⟨boundary_edges_subset h hr R hb,?_⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
      intro j hj
      rcases Finset.mem_insert.mp hj with he | hj
      · subst j
        exact i.isLt
      · have he := Finset.mem_singleton.mp hj
        subst j
        exact (ActualBoundaryCyclicOrder.nextRing i).isLt
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_biUnion.mpr
        refine ⟨a,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩
        · rw [ha]
          intro j hj
          rcases Finset.mem_insert.mp hj with he | hj
          · subst j
            simp
          · have he := Finset.mem_singleton.mp hj
            subst j
            simp
        · simp [chord,(boundary_sites_distinct i).2.2]
      · intro j hj
        rcases Finset.mem_insert.mp hj with he | hj
        · subst j
          exact (i-1).isLt
        · have he := Finset.mem_singleton.mp hj
          subst j
          exact (ActualBoundaryCyclicOrder.nextRing i).isLt

theorem actual_ring_edges_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (ringEdges R).card = 9 + (ringOnlyTriangles R).card := by
  classical
  have hd : Disjoint boundaryEdges ((earCenters R).image chord) := by
    apply Finset.disjoint_left.mpr
    intro e hb hc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    have hp := (boundary_pair_iff (prevSite i) (nextSite i)
      (boundary_sites_distinct i).2.2).mp hb
    exact skip_pair_not_boundary i hp
  rw [actual_ring_edges_eq h hr R,Finset.card_union_of_disjoint hd,
    boundary_edges_card,Finset.card_image_of_injective _ chord_injective,
    actual_ear_centers_card h hr R]

end N11Formalization.ActualSelectedRingEdges
#check @N11Formalization.ActualSelectedRingEdges.actual_ring_edges_card
#print axioms N11Formalization.ActualSelectedRingEdges.actual_ring_edges_card
