import N11Formalization.ActualIncidentFanInteriors
import N11Formalization.ActualClippedMeshVertices

/-! PRODUCED finite nearest-triangle family over ALL actual clipped primal
vertices, with one coherent selected fan per degenerate polygon. Every
triangle retains the original witness/radius; distinct indexed triangles
have disjoint interiors; each primal polygon is covered by its own triangles.
This does not assert that the global union is the required cellular disk. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualFiniteNearestRefinement
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedMeshVertices
open ActualCoverStructuralReduction ActualIncidentPolygonOrder ActualIncidentFanRefinement
open ActualIncidentFanInteriors ActualDelaunayPolygonSeparation FlashTiling

structure Refinement (c : Fin 11 → Point) (r : ℝ) where
  vertices : Finset Point
  exact_vertices : ∀ v : Point, v ∈ vertices ↔ v ∈ ClippedVertices c
  face : ∀ v : vertices, InteriorFace c r
  base : ∀ v : vertices, (face v).point = v.val
  order : ∀ v : vertices, OrderedCircle c r (face v)

theorem actual_refinement {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) : Nonempty (Refinement c r) := by
  classical
  let V := (clippedVertices_finite h.injective).toFinset
  have hV (v : Point) : v ∈ V ↔ v ∈ ClippedVertices c := Set.Finite.mem_toFinset _
  have hfaces (v : V) : ∃ F : InteriorFace c r, F.point = v.val :=
    clipped_vertex_face h hr ((hV v.val).mp v.property)
  let F := fun v : V => Classical.choose (hfaces v)
  have hbase (v : V) : (F v).point = v.val := Classical.choose_spec (hfaces v)
  let O := fun v : V => Classical.choice (ActualIncidentPolygonOrder.InteriorFace.orderedCircle (F v) h.injective)
  exact ⟨⟨V,hV,F,hbase,O⟩⟩

def Refinement.Index {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :=
  (v : R.vertices) × {k : Fin (incident c (R.face v).point).card // FanIndex k}

instance {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) : Fintype R.Index := by
  classical
  unfold Refinement.Index
  infer_instance

def Refinement.witness {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (a : R.Index) : Point := (R.face a.1).point

def Refinement.labels {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (a : R.Index) : Fin 3 → Fin 11 := triangleLabels (R.order a.1) a.2.val

def Refinement.hull {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (a : R.Index) : Set Point := TriangleHull (R.order a.1) a.2.val

theorem Refinement.real_triangle {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) :
    ‖R.witness a‖ < 1 ∧
      (∀ v : Fin 3, R.witness a ∈ Cell c (R.labels a v) ∧
        dist (R.witness a) (c (R.labels a v)) ≤ r) ∧
      0 < orient (c (R.labels a 0)) (c (R.labels a 1)) (c (R.labels a 2)) :=
  ⟨(R.face a.1).inside,fun v => OrderedCircle.selected_nearest (R.order a.1) a.2.val v,
    OrderedCircle.selected_positive_area (R.order a.1) a.2.property⟩

theorem Refinement.triangles_interior_disjoint {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {a b : R.Index} (hab : a ≠ b) :
    Disjoint (interior (R.hull a)) (interior (R.hull b)) := by
  rcases a with ⟨va,ka⟩
  rcases b with ⟨vb,kb⟩
  by_cases hbase : va = vb
  · subst vb
    have hkl : ka.val ≠ kb.val := by
      intro he
      have hk : ka = kb := Subtype.ext he
      exact hab (by rw [hk])
    exact OrderedCircle.selected_interiors_disjoint (R.order va) ka.property kb.property hkl
  · have hFG : (R.face va).point ≠ (R.face vb).point := by
      intro he
      apply hbase
      apply Subtype.ext
      simpa only [R.base] using he
    exact selected_triangles_coherent (R.order va) (R.order vb) hFG

theorem Refinement.polygon_covered {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (v : R.vertices) {p : Point}
    (hp : p ∈ convexHull ℝ (Set.range (fun i => c ((R.order v).order i).val))) :
    ∃ a : R.Index, a.1 = v ∧ p ∈ R.hull a := by
  obtain ⟨k,hk,hp⟩ := OrderedCircle.hull_selected_cover (R.order v) hp
  exact ⟨⟨v,⟨k,hk⟩⟩,rfl,hp⟩

theorem Refinement.witness_exact_vertex {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) : R.witness a ∈ ClippedVertices c := by
  rw [Refinement.witness,R.base]
  exact (R.exact_vertices a.1.val).mp a.1.property

/-- Every index is a genuine nondegenerate triangle; no duplicated-point
slack triangle is counted as a two-dimensional refinement face. -/
theorem Refinement.labels_injective {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) : Function.Injective (R.labels a) := by
  have hpos := (Refinement.real_triangle R a).2.2
  have h01 : R.labels a 0 ≠ R.labels a 1 := by
    intro he
    rw [he] at hpos
    simp [orient,det2] at hpos
  have h02 : R.labels a 0 ≠ R.labels a 2 := by
    intro he
    rw [← he] at hpos
    simp [orient,det2] at hpos
  have h12 : R.labels a 1 ≠ R.labels a 2 := by
    intro he
    rw [he] at hpos
    simp only [orient,det2_self] at hpos
    exact lt_irrefl 0 hpos
  intro i j he
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact (h01 he).elim
    | exact (h02 he).elim
    | exact (h12 he).elim
    | exact (h01 he.symm).elim
    | exact (h02 he.symm).elim
    | exact (h12 he.symm).elim

end N11Formalization.ActualFiniteNearestRefinement
#check @N11Formalization.ActualFiniteNearestRefinement.actual_refinement
#check @N11Formalization.ActualFiniteNearestRefinement.Refinement.real_triangle
#check @N11Formalization.ActualFiniteNearestRefinement.Refinement.triangles_interior_disjoint
#print axioms N11Formalization.ActualFiniteNearestRefinement.actual_refinement
#print axioms N11Formalization.ActualFiniteNearestRefinement.Refinement.triangles_interior_disjoint
#print axioms N11Formalization.ActualFiniteNearestRefinement.Refinement.labels_injective
