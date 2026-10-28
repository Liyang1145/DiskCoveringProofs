import N11Formalization.ActualBoundaryFacetUniqueness
import N11Formalization.ActualEarCapacity

/-! ACTUAL nearest ears: the missing adjacent-ear exclusion is produced
without assuming an embedded refinement. Adjacent ears share a boundary
neighbor pair; uniqueness of its true interior nearest vertex forces four
ring disks through that point, contradicting the paid three-ring capacity.
Mere disk-intersection Ear is deliberately NOT strengthened to this claim. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualNearestEarExclusion
open ActualVoronoiCells ActualVoronoiIncidence ActualBoundaryFacetUniqueness
open ActualClippedFacetIntervals ActualCoverStructuralReduction ActualRingDirectionOrder
open ActualBoundaryCyclicOrder ActualEarCapacity ActualRingCommonPoints

def NearestEar (c : Fin 11 → Point) (i : Fin 9) : Prop :=
  ∃ p : Point, p ∈ unitDisk ∧ ∀ j ∈ earSet i, p ∈ Cell c (ringSite j)

theorem ear_labels_distinct : ∀ i : Fin 9,
    ringSite (i-1) ≠ ringSite i ∧ ringSite (i+1) ≠ ringSite (i-1) ∧
      ringSite (i+1) ≠ ringSite i := by decide +kernel

theorem adjacent_ear_members : ∀ i : Fin 9,
    i ∈ earSet i ∧ i+1 ∈ earSet i ∧
      i ∈ earSet (i+1) ∧ i+1 ∈ earSet (i+1) := by decide +kernel

theorem adjacent_ear_union_card : ∀ i : Fin 9,
    ((earSet i) ∪ (earSet (i+1))).card = 4 := by decide +kernel

theorem nearestEar_point_vertex {c : Fin 11 → Point} {i : Fin 9} {p : Point}
    (hp : p ∈ unitDisk) (hnear : ∀ j ∈ earSet i, p ∈ Cell c (ringSite j)) :
    p ∈ ClippedVertices c := by
  have hd := ear_labels_distinct i
  exact ⟨hp,triple_mem_vertices hd.1 hd.2.1 hd.2.2
    (hnear (i-1) (by simp [earSet])) (hnear i (by simp [earSet]))
    (hnear (i+1) (by simp [earSet]))⟩

theorem NearestEar.toEar {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    {i : Fin 9} (hi : NearestEar c i) : Ear c r i := by
  obtain ⟨p,hp,hnear⟩ := hi
  exact ⟨p,fun j hj => nearest_le_radius hc hp (hnear j hj)⟩

theorem no_adjacent_nearest_ears {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) :
    ¬ (NearestEar c i ∧ NearestEar c (i+1)) := by
  rintro ⟨⟨p,hp,hnearP⟩,⟨q,hq,hnearQ⟩⟩
  have hm := adjacent_ear_members i
  have hpv := nearestEar_point_vertex hp hnearP
  have hqv := nearestEar_point_vertex hq hnearQ
  have he : p = q := neighbor_nearest_vertex_unique h hr i hpv hqv
    ⟨hnearP i hm.1,hnearP (i+1) hm.2.1⟩
    ⟨hnearQ i hm.2.2.1,hnearQ (i+1) hm.2.2.2⟩
  have hsub : (earSet i) ∪ (earSet (i+1)) ⊆ ringsAt c r p := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hj with hji | hjnext
    · exact nearest_le_radius h.cover hp (hnearP j hji)
    · rw [he]
      exact nearest_le_radius h.cover hq (hnearQ j hjnext)
  have hcard := Finset.card_le_card hsub
  rw [adjacent_ear_union_card] at hcard
  have hthree := ringsAt_card_le_three h.cover hr h.labels p
  omega

theorem nearest_ears_unique {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 9}
    (hi : NearestEar c i) (hj : NearestEar c j) : i = j := by
  by_contra hij
  have hadj := ear_pair_adjacent h.cover hr h.labels hij
    (NearestEar.toEar h.cover hi) (NearestEar.toEar h.cover hj)
  rcases hadj with hjleft | hjright
  · subst j
    apply no_adjacent_nearest_ears h hr (i-1)
    exact ⟨hj,by simpa only [sub_add_cancel] using hi⟩
  · subst j
    exact no_adjacent_nearest_ears h hr i ⟨hi,hj⟩

/-- No noAdjacent input remains for a family of TRUE nearest ear witnesses. -/
theorem nearest_ears_card_le_one {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (s : Finset (Fin 9)) (hactual : ∀ i ∈ s, NearestEar c i) : s.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact nearest_ears_unique h hr (hactual i hi) (hactual j hj)

end N11Formalization.ActualNearestEarExclusion
#check @N11Formalization.ActualNearestEarExclusion.no_adjacent_nearest_ears
#check @N11Formalization.ActualNearestEarExclusion.nearest_ears_card_le_one
#print axioms N11Formalization.ActualNearestEarExclusion.no_adjacent_nearest_ears
#print axioms N11Formalization.ActualNearestEarExclusion.nearest_ears_card_le_one
