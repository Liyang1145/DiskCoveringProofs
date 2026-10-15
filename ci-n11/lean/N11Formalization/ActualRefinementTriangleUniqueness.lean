import N11Formalization.ActualFiniteNearestRefinement

/-! No duplicate actual selected triangle is counted by the produced finite
refinement. Three distinct common-nearest site labels determine at most one
primal witness; within one true3/4/5-gon the selected fan index is unique.
No area/nonempty-interior counting assumption is needed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementTriangleUniqueness
open ActualVoronoiCells ActualVoronoiIncidence ActualFiniteNearestRefinement
open ActualIncidentFanRefinement ActualIncidentPolygonOrder ActualHubEdgeEndpointGeometry

def labelSet {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (a : R.Index) :
    Finset (Fin 11) := {R.labels a 0,R.labels a 1,R.labels a 2}

theorem mem_labelSet {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {a : R.Index} {i : Fin 11} : i ∈ labelSet R a ↔ ∃ v : Fin 3, R.labels a v = i := by
  simp only [labelSet,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (he | he | he)
    · exact ⟨0,he.symm⟩
    · exact ⟨1,he.symm⟩
    · exact ⟨2,he.symm⟩
  · rintro ⟨v,rfl⟩
    fin_cases v <;> simp

theorem labelSet_card {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (a : R.Index) :
    (labelSet R a).card = 3 := by
  have hi := Refinement.labels_injective R a
  simp [labelSet,hi.ne (by decide : (0 : Fin 3) ≠ 1),
    hi.ne (by decide : (0 : Fin 3) ≠ 2),hi.ne (by decide : (1 : Fin 3) ≠ 2)]

theorem local_fan_set_injective {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ k l : Fin n, FanIndex k → FanIndex l →
      indexTriangle (by omega : 0 < n) k = indexTriangle (by omega : 0 < n) l → k = l := by
  interval_cases n <;> decide +revert

theorem same_labels_same_witness {c : Fin 11 → Point} (hc : Function.Injective c) {r : ℝ}
    (R : Refinement c r) {a b : R.Index} (hab : labelSet R a = labelSet R b) :
    R.witness a = R.witness b := by
  have hnearB (v : Fin 3) : R.witness b ∈ Cell c (R.labels a v) := by
    have hm : R.labels a v ∈ labelSet R b := by rw [← hab]; exact mem_labelSet.mpr ⟨v,rfl⟩
    obtain ⟨w,hw⟩ := mem_labelSet.mp hm
    rw [← hw]
    exact (Refinement.real_triangle R b).2.1 w |>.1
  have hnearA := (Refinement.real_triangle R a).2.1
  have hinj := Refinement.labels_injective R a
  by_contra hw
  rcases two_points_three_sites
    (fun he => (by decide : (0 : Fin 3) ≠ 1) (hinj (hc he))) hw
    (le_antisymm ((hnearA 0).1 (R.labels a 1)) ((hnearA 1).1 (R.labels a 0)))
    (le_antisymm (hnearB 0 (R.labels a 1)) (hnearB 1 (R.labels a 0)))
    (le_antisymm ((hnearA 2).1 (R.labels a 0)) ((hnearA 0).1 (R.labels a 2)))
    (le_antisymm (hnearB 2 (R.labels a 0)) (hnearB 0 (R.labels a 2))) with he | he
  · exact (by decide : (2 : Fin 3) ≠ 0) (hinj (hc he))
  · exact (by decide : (2 : Fin 3) ≠ 1) (hinj (hc he))

theorem local_labelSet_image {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (v : R.vertices)
    (k : {k : Fin (incident c (R.face v).point).card // FanIndex k}) :
    labelSet R ⟨v,k⟩ =
      (indexTriangle (by have h := (R.face v).at_least_three; omega) k.val).image
        (fun j => ((R.order v).order j).val) := by
  simp only [labelSet,Refinement.labels,triangleLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,indexTriangle,Finset.image_insert,Finset.image_singleton]
  rfl

theorem labelSet_injective {c : Fin 11 → Point} (hc : Function.Injective c) {r : ℝ}
    (R : Refinement c r) : Function.Injective (labelSet R) := by
  intro a b hab
  have hw := same_labels_same_witness hc R hab
  have hv : a.1 = b.1 := by
    apply Subtype.ext
    simpa only [Refinement.witness,R.base] using hw
  rcases a with ⟨v,k⟩
  rcases b with ⟨w,l⟩
  dsimp only at hv
  subst w
  rw [local_labelSet_image,local_labelSet_image] at hab
  have hsets := (Finset.image_injective (ActualIncidentFacetAdjacency.OrderedCircle.label_injective (R.order v))) hab
  have hkl := local_fan_set_injective (R.face v).at_least_three (R.face v).at_most_five
    k.val l.val k.property l.property hsets
  have he : k = l := Subtype.ext hkl
  rw [he]

end N11Formalization.ActualRefinementTriangleUniqueness
#check @N11Formalization.ActualRefinementTriangleUniqueness.labelSet_injective
#print axioms N11Formalization.ActualRefinementTriangleUniqueness.same_labels_same_witness
#print axioms N11Formalization.ActualRefinementTriangleUniqueness.labelSet_injective
