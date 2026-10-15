import N11Formalization.ActualBoundaryFacetEndpoints
import N11Formalization.ActualRingCommonPoints
import N11Formalization.ActualDelaunaySupport

/-! Actual interior face-incidence data, including degenerate4/5-site circles.
No triangle is guessed. Boundary facets produce3..5 incident-site faces;
every incident site is genuinely within original r and strictly radially
exposed. Coherent polygon refinement/graph classification remains separate. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualVoronoiIncidence
open ActualVoronoiCells ActualRingDirectionOrder ActualRingCommonPoints
open ActualBoundaryCyclicOrder ActualBoundaryFacetEndpoints ActualDelaunaySupport
open ActualCoverStructuralReduction DSHTopologyInterior
open ActualHubEdgeEndpointGeometry

def incident (c : Fin 11 → Point) (v : Point) : Finset (Fin 11) := by
  classical
  exact Finset.univ.filter (fun i => v ∈ Cell c i)

theorem mem_incident {c : Fin 11 → Point} {v : Point} {i : Fin 11} :
    i ∈ incident c v ↔ v ∈ Cell c i := by simp [incident]

theorem incident_within_radius {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) {v : Point} (hv : ‖v‖ ≤ 1) {i : Fin 11} (hi : i ∈ incident c v) :
    dist v (c i) ≤ r := nearest_le_radius hc (mem_unitDisk.mpr hv) (mem_incident.mp hi)

theorem incident_card_le_five {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) {v : Point}
    (hv : ‖v‖ ≤ 1) : (incident c v).card ≤ 5 := by
  classical
  have hsub : incident c v ⊆ (ringsAt c r v).image ringSite ∪ {9,10} := by
    intro i hi
    apply Finset.mem_union.mpr
    by_cases hir : i.val < 9
    · left
      let I : Fin 9 := ⟨i.val,hir⟩
      apply Finset.mem_image.mpr
      refine ⟨I,?_,rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ I,incident_within_radius hc hv hi⟩
    · right
      have hin := i.isLt
      have he : i.val = 9 ∨ i.val = 10 := by omega
      rcases he with he | he
      · exact Finset.mem_insert.mpr (Or.inl (Fin.ext he))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext he)))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have himg := Finset.card_image_le (s := ringsAt c r v) (f := ringSite)
  have hsmall := ringsAt_card_le_three hc hr hR v
  have hhubs : ({9,10} : Finset (Fin 11)).card = 2 := by decide
  rw [hhubs] at hcard
  omega

structure InteriorFace (c : Fin 11 → Point) (r : ℝ) where
  point : Point
  inside : ‖point‖ < 1
  at_least_three : 3 ≤ (incident c point).card
  at_most_five : (incident c point).card ≤ 5
  radius : ∀ i ∈ incident c point, dist point (c i) ≤ r
  equal_radius : ∀ i ∈ incident c point, ∀ j ∈ incident c point,
    dist point (c i) = dist point (c j)
  exposed : ∀ i ∈ incident c point, ∀ j ∈ incident c point, i ≠ j →
    inner ℝ (c i-point) (c j-point) < inner ℝ (c i-point) (c i-point)

theorem BoundaryVertex.interiorFace {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i : Fin 9}
    (v : BoundaryVertex c r i) : Nonempty (InteriorFace c r) := by
  have hk : v.point ∈ Cell c v.third := by
    intro k
    rw [v.third_tie]
    exact v.nearest.1 k
  have hne : ringSite i ≠ ringSite (nextRing i) := by
    intro he
    exact next_ne i (Fin.ext (congrArg (fun q : Fin 11 => q.val) he))
  have hthree : 3 ≤ (incident c v.point).card := by
    have hsub : ({ringSite i,ringSite (nextRing i),v.third} : Finset (Fin 11)) ⊆
        incident c v.point := by
      intro k hkin
      rcases Finset.mem_insert.mp hkin with he | hkin
      · subst k
        exact mem_incident.mpr v.nearest.1
      rcases Finset.mem_insert.mp hkin with he | hkin
      · subst k
        exact mem_incident.mpr v.nearest.2
      have he := Finset.mem_singleton.mp hkin
      subst k
      exact mem_incident.mpr hk
    have hcard : ({ringSite i,ringSite (nextRing i),v.third} : Finset (Fin 11)).card = 3 := by
      simp [hne,v.third_ne_left,v.third_ne_right,Ne.symm v.third_ne_left,Ne.symm v.third_ne_right]
    rw [← hcard]
    exact Finset.card_le_card hsub
  refine ⟨⟨v.point,v.inside,hthree,incident_card_le_five h.cover hr h.labels v.inside.le,
    fun k hk => incident_within_radius h.cover v.inside.le hk,?_,?_⟩⟩
  · intro k hk l hl
    exact le_antisymm ((mem_incident.mp hk) l) ((mem_incident.mp hl) k)
  · intro k hk l hl hkl
    exact incident_sites_strictly_exposed h.injective hkl (mem_incident.mp hk) (mem_incident.mp hl)

def TripleFiber (c : Fin 11 → Point) (i j k : Fin 11) : Set Point :=
  {x | i ≠ j ∧ k ≠ i ∧ k ≠ j ∧ x ∈ Cell c i ∩ Cell c j ∩ Cell c k}

def Vertices (c : Fin 11 → Point) : Set Point :=
  ⋃ i : Fin 11, ⋃ j : Fin 11, ⋃ k : Fin 11, TripleFiber c i j k

def ClippedVertices (c : Fin 11 → Point) : Set Point := unitDisk ∩ Vertices c

theorem tripleFiber_subsingleton {c : Fin 11 → Point} (hc : Function.Injective c)
    (i j k : Fin 11) : (TripleFiber c i j k).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hij := hx.1
  have hki := hx.2.1
  have hkj := hx.2.2.1
  have hX := hx.2.2.2
  have hY := hy.2.2.2
  rcases two_points_three_sites (fun he => hij (hc he)) hxy
    (le_antisymm (hX.1.1 j) (hX.1.2 i)) (le_antisymm (hY.1.1 j) (hY.1.2 i))
    (le_antisymm (hX.2 i) (hX.1.1 k)) (le_antisymm (hY.2 i) (hY.1.1 k)) with he | he
  · exact hki (hc he)
  · exact hkj (hc he)

/-- All true3-or-more-site nearest vertices are finite even in degenerate
4/5-site circle cases. They need NOT all lie inD: clipping stays explicit. -/
theorem vertices_finite {c : Fin 11 → Point} (hc : Function.Injective c) : (Vertices c).Finite :=
  Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun k =>
    (tripleFiber_subsingleton hc i j k).finite

theorem clippedVertices_finite {c : Fin 11 → Point} (hc : Function.Injective c) :
    (ClippedVertices c).Finite := (vertices_finite hc).subset Set.inter_subset_right

theorem BoundaryVertex.mem_clippedVertices {c : Fin 11 → Point} {r : ℝ} {i : Fin 9}
    (v : BoundaryVertex c r i) : v.point ∈ ClippedVertices c := by
  refine ⟨mem_unitDisk.mpr v.inside.le,?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨ringSite i,Set.mem_iUnion.mpr ⟨ringSite (nextRing i),
    Set.mem_iUnion.mpr ⟨v.third,?_,v.third_ne_left,v.third_ne_right,v.nearest,?_⟩⟩⟩
  · intro he
    exact next_ne i (Fin.ext (congrArg (fun q : Fin 11 => q.val) he))
  · intro j
    rw [v.third_tie]
    exact v.nearest.1 j

end N11Formalization.ActualVoronoiIncidence
#check @N11Formalization.ActualVoronoiIncidence.BoundaryVertex.interiorFace
#print axioms N11Formalization.ActualVoronoiIncidence.BoundaryVertex.interiorFace
#check @N11Formalization.ActualVoronoiIncidence.clippedVertices_finite
#print axioms N11Formalization.ActualVoronoiIncidence.clippedVertices_finite
