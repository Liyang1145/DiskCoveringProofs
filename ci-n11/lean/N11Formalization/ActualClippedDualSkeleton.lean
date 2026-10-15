import N11Formalization.ActualClippedFacetInterior
import N11Formalization.ActualClippedSpokeEmbedding

/-! ACTUAL positive facets produce two-spoke embedded dual edges. Distinct
unordered edges can meet ONLY at their common actual site, never at a facet
midpoint or in a cell interior. This is an embedding producer, not yet the
cellular-disk/facial-cycle/Euler theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualClippedDualSkeleton
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedFacetIntervals
open ActualClippedCellPartition ActualClippedFacetInterior ActualCoverStructuralReduction
open ActualClippedSpokeEmbedding ActualVoronoiRadialExit

structure Bridge (c : Fin 11 → Point) (i j : Fin 11) where
  point : Point
  distinct : i ≠ j
  inside : ‖point‖ < 1
  incident_pair : incident c point = {i,j}

theorem Bridge.cell_left {c : Fin 11 → Point} {i j : Fin 11} (b : Bridge c i j) :
    b.point ∈ ClippedCell c i := by
  refine ⟨mem_unitDisk.mpr b.inside.le,mem_incident.mp ?_⟩
  rw [b.incident_pair]
  simp

theorem Bridge.cell_right {c : Fin 11 → Point} {i j : Fin 11} (b : Bridge c i j) :
    b.point ∈ ClippedCell c j := by
  refine ⟨mem_unitDisk.mpr b.inside.le,mem_incident.mp ?_⟩
  rw [b.incident_pair]
  simp

theorem Bridge.cell_of_label {c : Fin 11 → Point} {i j k : Fin 11}
    (b : Bridge c i j) (hk : k = i ∨ k = j) : b.point ∈ ClippedCell c k := by
  rcases hk with rfl | rfl
  · exact Bridge.cell_left b
  · exact Bridge.cell_right b

theorem Bridge.not_any_interior {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (b : Bridge c i j) (k : Fin 11) :
    b.point ∉ interior (ClippedCell c k) := by
  intro hx
  have hs := interior_cell_strict hc (interior_mono Set.inter_subset_right hx)
  by_cases hik : i = k
  · subst k
    exact not_lt_of_ge ((Bridge.cell_right b).2 i) (hs j b.distinct.symm)
  · exact not_lt_of_ge ((Bridge.cell_left b).2 k) (hs i hik)

theorem Bridge.site_ne {c : Fin 11 → Point} {r : ℝ} (h : Representative c r)
    {i j : Fin 11} (b : Bridge c i j) (k : Fin 11) : b.point ≠ c k := by
  intro he
  apply Bridge.not_any_interior h.injective b k
  rw [he]
  exact Representative.clipped_center_interior h k

theorem bridge_of_positive_facet {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) (f : FacetInterval c i j) (hpos : f.lo < f.hi) :
    Nonempty (Bridge c i j) := by
  let t := (f.lo+f.hi)/2
  have hlo : f.lo < t := by dsimp [t]; linarith
  have hhi : t < f.hi := by dsimp [t]; linarith
  exact ⟨⟨ray f.base f.direction t,hij,(FacetInterval.open_point hc hij f hlo hhi).1,
    FacetInterval.open_incident hc hij f hlo hhi⟩⟩

theorem bridge_of_actual_positive_pair {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j)
    (hpos : ∃ x ∈ ClippedCommon c i j, ∃ y ∈ ClippedCommon c i j, x ≠ y) :
    Nonempty (Bridge c i j) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := hpos
  obtain ⟨f⟩ := clippedCommon_interval hc hij ⟨x,hx⟩
  exact bridge_of_positive_facet hc hij f (FacetInterval.positive_iff f |>.mpr ⟨x,hx,y,hy,hxy⟩)

theorem spoke_eq_site_time_zero {c : Fin 11 → Point} {i : Fin 11} {x : Point}
    (hx : x ≠ c i) {t : ℝ} (he : spoke c i x t = c i) : t = 0 := by
  have hz : t • (x-c i) = 0 := by
    have hh := congrArg (fun z : Point => z-c i) he
    simpa [spoke] using hh
  exact (smul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hx)

/-- Every intersection of two distinct dual edges is their shared site.
The actual site's index and the zero parameters are produced by the proof. -/
theorem distinct_bridge_spokes_intersection {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {a b k l i j : Fin 11}
    (B : Bridge c a b) (C : Bridge c k l)
    (hpairs : ({a,b} : Finset (Fin 11)) ≠ {k,l})
    (hi : i = a ∨ i = b) (hj : j = k ∨ j = l) {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (he : spoke c i B.point s = spoke c j C.point t) :
    i = j ∧ s = 0 ∧ t = 0 := by
  have hB := Bridge.cell_of_label B hi
  have hC := Bridge.cell_of_label C hj
  by_cases hs1 : s = 1
  · have heB : spoke c i B.point s = B.point := by simp [spoke,hs1]
    rw [heB] at he
    by_cases ht1 : t = 1
    · have heC : spoke c j C.point t = C.point := by simp [spoke,ht1]
      rw [heC] at he
      exact (hpairs (by rw [← B.incident_pair,← C.incident_pair,he])).elim
    · have htin : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hCI := spoke_interior h hC ht.1 htin
      rw [← he] at hCI
      exact (Bridge.not_any_interior h.injective B j hCI).elim
  have hsin : s < 1 := lt_of_le_of_ne hs.2 hs1
  by_cases ht1 : t = 1
  · have heC : spoke c j C.point t = C.point := by simp [spoke,ht1]
    rw [heC] at he
    have hBI := spoke_interior h hB hs.1 hsin
    rw [he] at hBI
    exact (Bridge.not_any_interior h.injective C i hBI).elim
  have htin : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hij : i = j := by
    by_contra hij
    exact different_cell_spokes_disjoint h hij hB hC hs.1 hsin ht.1 htin he
  subst j
  have hs0 : s = 0 := by
    by_contra hs0
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have htpos : 0 < t := by
      apply lt_of_le_of_ne ht.1
      intro ht0'
      have ht0 : t = 0 := ht0'.symm
      have hsite : spoke c i B.point s = c i := by simpa [spoke,ht0] using he
      exact hs0 (spoke_eq_site_time_zero (Bridge.site_ne h B i) hsite)
    have hBC := same_cell_spokes_unique h hB hC
      (Bridge.not_any_interior h.injective B i) (Bridge.not_any_interior h.injective C i)
      hspos htpos he
    exact hpairs (by rw [← B.incident_pair,← C.incident_pair,hBC])
  have ht0 : t = 0 := by
    have hsite : spoke c i C.point t = c i := by simpa [spoke,hs0] using he.symm
    exact spoke_eq_site_time_zero (Bridge.site_ne h C i) hsite
  exact ⟨rfl,hs0,ht0⟩

end N11Formalization.ActualClippedDualSkeleton
#check @N11Formalization.ActualClippedDualSkeleton.bridge_of_actual_positive_pair
#check @N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
#print axioms N11Formalization.ActualClippedDualSkeleton.bridge_of_actual_positive_pair
#print axioms N11Formalization.ActualClippedDualSkeleton.distinct_bridge_spokes_intersection
