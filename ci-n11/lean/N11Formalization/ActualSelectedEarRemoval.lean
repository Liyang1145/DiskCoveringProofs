import N11Formalization.ActualHubTriangleCensus

/-! Productive removal of an ACTUAL selected consecutive ring ear.
Its middle site has exactly the two boundary neighbors and belongs to
exactly this selected triangle, so it is not in either hub ring path.
No global disk, Euler or complementary two-fan premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSelectedEarRemoval
open ActualVoronoiCells ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementEarCount ActualNearestRingTriangles
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualRefinementLocalLinks ActualRefinementVertexLinks ActualRingLinkConnected
open ActualHubTriangleCensus ActualRefinementSideMultiplicity

theorem reachable_mem_closed {V : Type*} {G : SimpleGraph V} {s : Set V}
    (hclosed : ∀ u ∈ s, ∀ v, G.Adj u v → v ∈ s)
    {u v : V} (hu : u ∈ s) (h : G.Reachable u v) : v ∈ s := by
  obtain ⟨p⟩ := h
  revert hu
  induction p with
  | nil => exact id
  | cons hadj p ih =>
    intro hu
    exact ih (hclosed _ hu _ hadj)

theorem selected_ring_triangle_ear {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {a : R.Index} (ha : RingOnly R a) :
    ∃ i : Fin 9, labelSet R a = {prevSite i,ringSite i,nextSite i} := by
  have hinj := ringLabel_injective ha
  have hnear (v : Fin 3) : R.witness a ∈ Cell c (ringSite (ringLabel ha v)) := by
    rw [ringLabel_site]
    exact (Refinement.real_triangle R a).2.1 v |>.1
  obtain ⟨i,hi,_⟩ := nearest_ring_triangle_ear h hr
    (mem_unitDisk.mpr (Refinement.real_triangle R a).1.le)
    (hinj.ne (by decide : (0 : Fin 3) ≠ 1))
    (hinj.ne (by decide : (2 : Fin 3) ≠ 0))
    (hinj.ne (by decide : (2 : Fin 3) ≠ 1))
    (hnear 0) (hnear 1) (hnear 2)
  have hh := congrArg (Finset.image ringSite) hi
  simp only [ActualEarCapacity.earSet,Finset.image_insert,Finset.image_singleton,
    ringLabel_site] at hh
  exact ⟨i,hh.symm⟩

theorem ear_triangle_boundary_unique {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 9} {a b : R.Index}
    (ha : labelSet R a = {prevSite i,ringSite i,nextSite i})
    (hbi : ringSite i ∈ labelSet R b)
    (hbb : prevSite i ∈ labelSet R b ∨ nextSite i ∈ labelSet R b) :
    b = a := by
  rcases hbb with hbp | hbn
  · have hn : nextRing (i-1) = i := by
      change i-1+1 = i
      exact sub_add_cancel _ _
    apply boundary_pair_triangle_unique R h hr (i-1)
    · exact hbp
    · simpa only [hn] using hbi
    · rw [ha]
      simp [prevSite]
    · rw [hn,ha]
      simp
  · apply boundary_pair_triangle_unique R h hr i hbi
      (show ringSite (nextRing i) ∈ labelSet R b from hbn)
    · rw [ha]
      simp
    · rw [ha]
      simp [nextSite]

theorem actual_ear_center_neighbors {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 9} {a : R.Index}
    (ha : labelSet R a = {prevSite i,ringSite i,nextSite i}) :
    ∀ j : Fin 11, Neighbor R (ringSite i) j ↔
      j = prevSite i ∨ j = nextSite i := by
  have hd := boundary_sites_distinct i
  have hb := actual_boundary_neighbors h hr R i
  have hclosed : ∀ u ∈ ({prevSite i,nextSite i} : Set (Fin 11)), ∀ v,
      (linkGraph R (ringSite i)).Adj u v →
        v ∈ ({prevSite i,nextSite i} : Set (Fin 11)) := by
    intro u hu v huv
    obtain ⟨b,hbi,hbu,hbv⟩ := huv.2.2.2
    have hbb : prevSite i ∈ labelSet R b ∨ nextSite i ∈ labelSet R b := by
      rcases hu with rfl | hu
      · exact Or.inl hbu
      · have he : u = nextSite i := hu
        exact Or.inr (he ▸ hbu)
    have he := ear_triangle_boundary_unique h hr R ha hbi hbb
    rw [he,ha] at hbv
    rcases Finset.mem_insert.mp hbv with he | hbv
    · exact Or.inl he
    rcases Finset.mem_insert.mp hbv with he | hbv
    · exact (huv.2.2.1 he).elim
    · exact Or.inr (Finset.mem_singleton.mp hbv)
  intro j
  constructor
  · intro hj
    exact reachable_mem_closed hclosed (Or.inl rfl)
      (actual_all_site_links_reachable h hr R (ringSite i) hb.1 hj)
  · rintro (rfl | rfl)
    · exact hb.1
    · exact hb.2

theorem actual_ear_center_star {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 9} {a : R.Index}
    (ha : labelSet R a = {prevSite i,ringSite i,nextSite i}) :
    siteTriangles R (ringSite i) = {a} := by
  classical
  ext b
  rw [mem_siteTriangles,Finset.mem_singleton]
  constructor
  · intro hbi
    have hc := labelSet_card R b
    have hrem : ((labelSet R b).erase (ringSite i)).Nonempty := by
      apply Finset.card_pos.mp
      have ht := Finset.card_erase_add_one hbi
      omega
    obtain ⟨k,hk⟩ := hrem
    have hkn : Neighbor R (ringSite i) k :=
      ⟨(Finset.mem_erase.mp hk).1,b,hbi,(Finset.mem_erase.mp hk).2⟩
    rcases (actual_ear_center_neighbors h hr R ha k).mp hkn with he | he
    · exact ear_triangle_boundary_unique h hr R ha hbi
        (Or.inl (he ▸ (Finset.mem_erase.mp hk).2))
    · exact ear_triangle_boundary_unique h hr R ha hbi
        (Or.inr (he ▸ (Finset.mem_erase.mp hk).2))
  · rintro rfl
    rw [ha]
    simp

theorem actual_ear_center_no_hub {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i : Fin 9} {a : R.Index}
    (ha : labelSet R a = {prevSite i,ringSite i,nextSite i}) :
    ¬ Neighbor R (ringSite i) 9 ∧ ¬ Neighbor R (ringSite i) 10 := by
  constructor <;> intro hn
  · have hh := (actual_ear_center_neighbors h hr R ha 9).mp hn
    rcases hh with he | he <;> have hh := congrArg Fin.val he <;>
      simp [prevSite,nextSite,ringSite] at hh <;> omega
  · have hh := (actual_ear_center_neighbors h hr R ha 10).mp hn
    rcases hh with he | he <;> have hh := congrArg Fin.val he <;>
      simp [prevSite,nextSite,ringSite] at hh <;> omega

end N11Formalization.ActualSelectedEarRemoval
#check @N11Formalization.ActualSelectedEarRemoval.actual_ear_center_neighbors
#check @N11Formalization.ActualSelectedEarRemoval.actual_ear_center_star
#check @N11Formalization.ActualSelectedEarRemoval.actual_ear_center_no_hub
#print axioms N11Formalization.ActualSelectedEarRemoval.actual_ear_center_star
#print axioms N11Formalization.ActualSelectedEarRemoval.actual_ear_center_no_hub
