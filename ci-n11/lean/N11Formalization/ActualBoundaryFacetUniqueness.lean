import N11Formalization.ActualClippedFacetInterior

/-! Each ACTUAL boundary-neighbor pair has at most one true nearest vertex
insideD. The unique circle tie is one end of the complete clipped facet; no
third-site vertex is in its open interior. This pays uniqueness directly
from actual facet geometry, without an embedded dual-disk premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryFacetUniqueness
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedFacetIntervals
open ActualClippedFacetInterior ActualClippedMeshVertices ActualCoverStructuralReduction
open ActualVoronoiRadialExit ActualRingDirectionOrder ActualBoundaryCyclicOrder
open ActualBoundaryNeighborTies

theorem FacetInterval.vertex_is_endpoint {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 11} (hij : i ≠ j)
    (f : FacetInterval c i j) {x : Point} (hx : x ∈ ClippedVertices c)
    (hpair : x ∈ ClippedCommon c i j) :
    x = ray f.base f.direction f.lo ∨ x = ray f.base f.direction f.hi := by
  have hmem := hpair
  rw [f.points] at hmem
  obtain ⟨t,ht,rfl⟩ := hmem
  by_cases hlo : t = f.lo
  · exact Or.inl (by rw [hlo])
  by_cases hhi : t = f.hi
  · exact Or.inr (by rw [hhi])
  have hlt : f.lo < t := lt_of_le_of_ne ht.1 (Ne.symm hlo)
  have hth : t < f.hi := lt_of_le_of_ne ht.2 hhi
  obtain ⟨F,hF⟩ := clipped_vertex_face h hr hx
  have hcard := F.at_least_three
  rw [hF,FacetInterval.open_incident h.injective hij f hlt hth] at hcard
  have htwo : ({i,j} : Finset (Fin 11)).card = 2 := by simp [hij]
  rw [htwo] at hcard
  omega

theorem FacetInterval.circle_is_endpoint {c : Fin 11 → Point}
    (hc : Function.Injective c) {i j : Fin 11} (hij : i ≠ j)
    (f : FacetInterval c i j) {x : Point} (hx : ‖x‖ = 1)
    (hpair : x ∈ ClippedCommon c i j) :
    x = ray f.base f.direction f.lo ∨ x = ray f.base f.direction f.hi := by
  rw [f.points] at hpair
  obtain ⟨t,ht,rfl⟩ := hpair
  by_cases hlo : t = f.lo
  · exact Or.inl (by rw [hlo])
  by_cases hhi : t = f.hi
  · exact Or.inr (by rw [hhi])
  have hinside := (FacetInterval.open_point hc hij f
    (lt_of_le_of_ne ht.1 (Ne.symm hlo)) (lt_of_le_of_ne ht.2 hhi)).1
  rw [hx] at hinside
  exact (lt_irrefl 1 hinside).elim

theorem vertex_unique_of_circle_point {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 11} (hij : i ≠ j)
    {x u v : Point} (hx : x ∈ ClippedCommon c i j) (hxn : ‖x‖ = 1)
    (hu : u ∈ ClippedVertices c) (hv : v ∈ ClippedVertices c)
    (hui : u ∈ ClippedCommon c i j) (hvi : v ∈ ClippedCommon c i j) : u = v := by
  obtain ⟨f⟩ := clippedCommon_interval h.injective hij ⟨x,hx⟩
  have hxend := FacetInterval.circle_is_endpoint h.injective hij f hxn hx
  have huend := FacetInterval.vertex_is_endpoint h hr hij f hu hui
  have hvend := FacetInterval.vertex_is_endpoint h hr hij f hv hvi
  have hux : u ≠ x := by
    intro he
    have hh := clipped_vertex_inside h hr hu
    rw [he,hxn] at hh
    exact lt_irrefl 1 hh
  have hvx : v ≠ x := by
    intro he
    have hh := clipped_vertex_inside h hr hv
    rw [he,hxn] at hh
    exact lt_irrefl 1 hh
  rcases hxend with hxend | hxend
  · rcases huend with huend | huend
    · exact (hux (huend.trans hxend.symm)).elim
    rcases hvend with hvend | hvend
    · exact (hvx (hvend.trans hxend.symm)).elim
    exact huend.trans hvend.symm
  · rcases huend with huend | huend
    · rcases hvend with hvend | hvend
      · exact huend.trans hvend.symm
      · exact (hvx (hvend.trans hxend.symm)).elim
    · exact (hux (huend.trans hxend.symm)).elim

theorem neighbor_nearest_vertex_unique {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) {u v : Point}
    (hu : u ∈ ClippedVertices c) (hv : v ∈ ClippedVertices c)
    (hui : u ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i)))
    (hvi : v ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i))) : u = v := by
  obtain ⟨z⟩ := neighbor_tie h.cover hr h.labels h.midpoint_order i
  have hij : ringSite i ≠ ringSite (nextRing i) := by
    intro he
    exact next_ne i (Fin.ext (congrArg (fun k : Fin 11 => k.val) he))
  exact vertex_unique_of_circle_point h hr hij
    ⟨mem_unitDisk.mpr (circleMap_norm z.angle).le,z.nearest⟩ (circleMap_norm z.angle)
    hu hv ⟨hu.1,hui⟩ ⟨hv.1,hvi⟩

end N11Formalization.ActualBoundaryFacetUniqueness
#check @N11Formalization.ActualBoundaryFacetUniqueness.neighbor_nearest_vertex_unique
#print axioms N11Formalization.ActualBoundaryFacetUniqueness.vertex_unique_of_circle_point
#print axioms N11Formalization.ActualBoundaryFacetUniqueness.neighbor_nearest_vertex_unique
