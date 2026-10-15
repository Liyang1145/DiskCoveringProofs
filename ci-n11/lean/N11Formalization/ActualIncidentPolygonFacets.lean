import N11Formalization.ActualIncidentPolygonOrder
import N11Formalization.ActualCyclicChordSupport
import N11Formalization.ActualIncidentFacetGerms

/-! ACTUAL incident polygon adjacent sides really are positive primal
facets. Every side is strictly supported away from all other incident sites,
and supplies a whole positive segment insideD with exactly its two nearest
labels. Four/five-site cocircular faces and the cyclic wrap are included. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentPolygonFacets
open ActualVoronoiCells ActualVoronoiIncidence ActualIncidentPolygonOrder
open ActualCyclicChordSupport ActualIncidentFacetGerms ActualCoverStructuralReduction

theorem cyclic_directions {n : ℕ} (hn : 1 < n) (theta : Fin n → ℝ)
    (hs : StrictMono theta) (hb : ∀ i, -Real.pi < theta i ∧ theta i ≤ Real.pi) :
    ∃ D : Fin n → Point, ∀ i : Fin n, ‖D i‖ = 1 ∧
      inner ℝ (D i) (circleMap (theta (finRotate n i))-circleMap (theta i)) = 0 ∧
      ∀ k : Fin n, k ≠ i → k ≠ finRotate n i →
        inner ℝ (D i) (circleMap (theta k)-circleMap (theta i)) < 0 := by
  cases n with
  | zero => omega
  | succ m =>
    have hm : 0 < m := by omega
    refine ⟨fun i => circleMap ((theta i+nextAngle theta i)/2),?_⟩
    intro i
    exact ⟨circleMap_norm _,ordered_chord_support hm theta hs hb i⟩

theorem rotate_ne {n : ℕ} (hn : 1 < n) (i : Fin n) : i ≠ finRotate n i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    by_cases hi : i = Fin.last m
    · subst i
      rw [finRotate_last]
      intro he
      have hh := congrArg Fin.val he
      change m = 0 at hh
      omega
    · exact ne_of_lt ((lt_finRotate_iff_ne_last i).mpr hi)

theorem OrderedCircle.supporting_sides {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) :
    ∃ D : Fin (incident c f.point).card → Point,
      ∀ i, ‖D i‖ = 1 ∧
        D i ∈ PairCone c f.point (o.order i).val
          (o.order (finRotate (incident c f.point).card i)).val := by
  let theta := fun j => siteAngle c f.point (o.order j).val
  obtain ⟨D,hD⟩ := cyclic_directions (by have h := f.at_least_three; omega)
    theta o.sorted (fun j => OrderedCircle.angle_bounds o j)
  have hdiff (i k : Fin (incident c f.point).card) :
      c (o.order k).val-c (o.order i).val =
        o.radius • (circleMap (theta k)-circleMap (theta i)) := by
    rw [o.coordinates k,o.coordinates i,smul_sub]
    abel
  refine ⟨D,?_⟩
  intro i
  refine ⟨(hD i).1,?_,?_⟩
  · rw [hdiff,real_inner_smul_right,(hD i).2.1,mul_zero]
  · intro k hk hki hkn
    let K : {k : Fin 11 // k ∈ incident c f.point} := ⟨k,hk⟩
    let q := o.order.symm K
    have hq : (o.order q).val = k := congrArg Subtype.val (o.order.apply_symm_apply K)
    have hqi : q ≠ i := by
      intro he
      apply hki
      rw [← hq,he]
    have hqn : q ≠ finRotate (incident c f.point).card i := by
      intro he
      apply hkn
      rw [← hq,he]
    rw [← hq,hdiff,real_inner_smul_right]
    exact mul_neg_of_pos_of_neg o.positive ((hD i).2.2 q hqi hqn)

theorem OrderedCircle.adjacent_facets {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) (hc : Covers c r) :
    ∀ i : Fin (incident c f.point).card,
      Nonempty (FacetGerm c r f.point (o.order i).val
        (o.order (finRotate (incident c f.point).card i)).val) := by
  obtain ⟨D,hD⟩ := OrderedCircle.supporting_sides o
  intro i
  apply facetGerm_of_pairCone hc f.inside (o.order i).property
    (o.order (finRotate (incident c f.point).card i)).property (hD i).2
  exact norm_ne_zero_iff.mp (by rw [(hD i).1]; norm_num)

/-- Consumer starting from actual representative+actual face, no polygon
existence or facet data is an additional premise. -/
theorem actual_incident_polygon_facets {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (f : InteriorFace c r) :
    ∃ o : OrderedCircle c r f,
      ∀ i : Fin (incident c f.point).card,
        Nonempty (FacetGerm c r f.point (o.order i).val
          (o.order (finRotate (incident c f.point).card i)).val) := by
  obtain ⟨o⟩ := InteriorFace.orderedCircle f h.injective
  exact ⟨o,OrderedCircle.adjacent_facets o h.cover⟩

end N11Formalization.ActualIncidentPolygonFacets
#check @N11Formalization.ActualIncidentPolygonFacets.actual_incident_polygon_facets
#print axioms N11Formalization.ActualIncidentPolygonFacets.OrderedCircle.supporting_sides
#print axioms N11Formalization.ActualIncidentPolygonFacets.actual_incident_polygon_facets
