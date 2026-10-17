import N11Formalization.ActualClippedFacetIntervals
import N11Formalization.ActualBoundaryNineTies

/-! Finite ACTUAL clipped mesh vertex set. All true3-or-more-site vertices
are strictly insideD; all circle facet endpoints are among the actual nine
ties. Every positive facet has at least one true interior vertex. This pays
global endpoint finiteness, not yet the dual-disk/Euler/refinement theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualClippedMeshVertices
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedFacetIntervals
open ActualCoverStructuralReduction ActualBoundaryNineTies ActualBoundaryNearestPairs
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualDelaunaySupport
open ActualVoronoiRadialExit

def MeshVertices (c : Fin 11 → Point) : Set Point :=
  ClippedVertices c ∪ {x : Point | BoundaryTie c x}

theorem clipped_vertex_inside {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {x : Point}
    (hx : x ∈ ClippedVertices c) : ‖x‖ < 1 := by
  apply lt_of_le_of_ne (mem_unitDisk.mp hx.1)
  intro hn
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx.2
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hi
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hj
  have hX := hk.2.2.2
  rcases nearest_one_of_pair h.cover hr h.labels hn hk.1 hX.1.1 hX.1.2 hX.2 with he | he
  · exact hk.2.1 he
  · exact hk.2.2.1 he

theorem clipped_vertex_face {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {x : Point}
    (hx : x ∈ ClippedVertices c) :
    ∃ f : InteriorFace c r, f.point = x := by
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx.2
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hi
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hj
  have hX := hk.2.2.2
  have hcard : 3 ≤ (incident c x).card := by
    have hsub : ({i,j,k} : Finset (Fin 11)) ⊆ incident c x := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact mem_incident.mpr hX.1.1
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact mem_incident.mpr hX.1.2
      have he := Finset.mem_singleton.mp hl
      subst l
      exact mem_incident.mpr hX.2
    have ht : ({i,j,k} : Finset (Fin 11)).card = 3 := by
      simp [hk.1,hk.2.1,hk.2.2.1,Ne.symm hk.2.1,Ne.symm hk.2.2.1]
    rw [← ht]
    exact Finset.card_le_card hsub
  have hinside := clipped_vertex_inside h hr hx
  refine ⟨⟨x,hinside,hcard,incident_card_le_five h.cover hr h.labels hinside.le,
    fun l hl => incident_within_radius h.cover hinside.le hl,?_,?_⟩,rfl⟩
  · intro l hl m hm
    exact le_antisymm ((mem_incident.mp hl) m) ((mem_incident.mp hm) l)
  · intro l hl m hm hlm
    exact incident_sites_strictly_exposed h.injective hlm
      (mem_incident.mp hl) (mem_incident.mp hm)

theorem mesh_vertices_finite {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) : (MeshVertices c).Finite := by
  obtain ⟨v⟩ := nineTies_of_cover h.cover hr h.labels h.midpoint_order
  have hboundary : {x : Point | BoundaryTie c x}.Finite := by
    rw [NineTies.tie_set_eq_range h hr v]
    exact Set.finite_range _
  exact (clippedVertices_finite h.injective).union hboundary

theorem mesh_vertex_parts_disjoint {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    Disjoint (ClippedVertices c) {x : Point | BoundaryTie c x} := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hi := clipped_vertex_inside h hr hx
  rw [hy.1] at hi
  exact (lt_irrefl 1) hi

theorem FacetInterval.endpoints_in_mesh {c : Fin 11 → Point} {i j : Fin 11}
    (hij : i ≠ j) (f : FacetInterval c i j) :
    ray f.base f.direction f.lo ∈ MeshVertices c ∧
      ray f.base f.direction f.hi ∈ MeshVertices c := by
  constructor
  · rcases f.left_endpoint with hcircle | hv
    · exact Or.inr ⟨hcircle,i,j,hij,f.left_mem.2⟩
    · exact Or.inl hv
  · rcases f.right_endpoint with hcircle | hv
    · exact Or.inr ⟨hcircle,i,j,hij,f.right_mem.2⟩
    · exact Or.inl hv

/-- A particular two-site nearest facet has at most one circle point.
This includes hub pairs, where having a circle point is already impossible. -/
theorem pair_circle_point_unique {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 11} (hij : i ≠ j)
    {x y : Point} (hx : x ∈ ClippedCommon c i j) (hy : y ∈ ClippedCommon c i j)
    (hxn : ‖x‖ = 1) (hyn : ‖y‖ = 1) : x = y := by
  let I : Fin 9 := ⟨i.val,nearest_ring h.cover h.labels hxn hx.2.1⟩
  let J : Fin 9 := ⟨j.val,nearest_ring h.cover h.labels hxn hx.2.2⟩
  have hIJ : I ≠ J := by
    intro he
    exact hij (Fin.ext (congrArg (fun q : Fin 9 => q.val) he))
  have hxeq : dist x (c (ringSite I)) = dist x (c (ringSite J)) :=
    le_antisymm (hx.2.1 j) (hx.2.2 i)
  have hyeq : dist y (c (ringSite I)) = dist y (c (ringSite J)) :=
    le_antisymm (hy.2.1 j) (hy.2.2 i)
  exact ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie h
    (by linarith : r < 1) hIJ hxn hyn hxeq hyeq
    (nearest_le_radius h.cover hx.1 hx.2.1) (nearest_le_radius h.cover hy.1 hy.2.1)

theorem FacetInterval.positive_has_interior_vertex {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 11} (hij : i ≠ j)
    (f : FacetInterval c i j) (hpos : f.lo < f.hi) :
    ray f.base f.direction f.lo ∈ ClippedVertices c ∨
      ray f.base f.direction f.hi ∈ ClippedVertices c := by
  rcases f.left_endpoint with hl | hl
  · rcases f.right_endpoint with hh | hh
    · have he := pair_circle_point_unique h hr hij f.left_mem f.right_mem hl hh
      have hz : (f.lo-f.hi) • f.direction = 0 := by
        rw [sub_smul]
        exact sub_eq_zero.mpr (add_left_cancel he)
      have hd : f.direction ≠ 0 := norm_ne_zero_iff.mp (by rw [f.unit]; norm_num)
      exact (smul_ne_zero (sub_ne_zero.mpr hpos.ne) hd hz).elim
    · exact Or.inr hh
  · exact Or.inl hl

end N11Formalization.ActualClippedMeshVertices
#check @N11Formalization.ActualClippedMeshVertices.clipped_vertex_face
#check @N11Formalization.ActualClippedMeshVertices.mesh_vertices_finite
#check @N11Formalization.ActualClippedMeshVertices.FacetInterval.positive_has_interior_vertex
#print axioms N11Formalization.ActualClippedMeshVertices.clipped_vertex_face
#print axioms N11Formalization.ActualClippedMeshVertices.mesh_vertices_finite
#print axioms N11Formalization.ActualClippedMeshVertices.FacetInterval.positive_has_interior_vertex
