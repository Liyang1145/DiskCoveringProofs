import N11Formalization.ActualNearestEarExclusion
import N11Formalization.ActualRingLocality

/-! Every true ring-only nearest triangle is a consecutive ear. Together
with the PRODUCED adjacent-ear exclusion, all actual nearest ring-only
triangles use at most one ear index. Applies also to selected cocircular
polygon refinement triangles, since they retain their true nearest witness. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualNearestRingTriangles
open ActualVoronoiCells ActualRingDirectionOrder ActualRingLocality
open ActualCoverStructuralReduction ActualEarCapacity ActualNearestEarExclusion

theorem local_ring_triples_are_ears : ∀ a b k : Fin 9,
    a ≠ b → k ≠ a → k ≠ b →
    ((b-a).val ≤ 2 ∨ (a-b).val ≤ 2) →
    ((k-a).val ≤ 2 ∨ (a-k).val ≤ 2) →
    ((k-b).val ≤ 2 ∨ (b-k).val ≤ 2) →
    ∃ i : Fin 9, earSet i = {a,b,k} := by decide +kernel

theorem nearest_ring_triangle_ear {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    {p : Point} (hp : p ∈ unitDisk) {a b k : Fin 9}
    (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (ha : p ∈ Cell c (ringSite a)) (hb : p ∈ Cell c (ringSite b))
    (hk : p ∈ Cell c (ringSite k)) :
    ∃ i : Fin 9, earSet i = {a,b,k} ∧ NearestEar c i := by
  have hradA := nearest_le_radius h.cover hp ha
  have hradB := nearest_le_radius h.cover hp hb
  have hradK := nearest_le_radius h.cover hp hk
  obtain ⟨i,hi⟩ := local_ring_triples_are_ears a b k hab hka hkb
    (intersection_local h.cover hr h.labels h.midpoint_order hradA hradB)
    (intersection_local h.cover hr h.labels h.midpoint_order hradA hradK)
    (intersection_local h.cover hr h.labels h.midpoint_order hradB hradK)
  refine ⟨i,hi,p,hp,?_⟩
  intro j hj
  rw [hi] at hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact ha
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact hb
  have he := Finset.mem_singleton.mp hj
  subst j
  exact hk

theorem earSet_injective : Function.Injective earSet := by decide +kernel

/-- Two actual ring-only nearest triples necessarily have the SAME ring set.
No planarity assumption and no noAdjacent interface remain in this theorem. -/
theorem nearest_ring_triangles_same_set {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    {p q : Point} (hp : p ∈ unitDisk) (hq : q ∈ unitDisk)
    {a b k A B K : Fin 9} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (hAB : A ≠ B) (hKA : K ≠ A) (hKB : K ≠ B)
    (ha : p ∈ Cell c (ringSite a)) (hb : p ∈ Cell c (ringSite b))
    (hk : p ∈ Cell c (ringSite k)) (hA : q ∈ Cell c (ringSite A))
    (hB : q ∈ Cell c (ringSite B)) (hK : q ∈ Cell c (ringSite K)) :
    ({a,b,k} : Finset (Fin 9)) = {A,B,K} := by
  obtain ⟨i,hi,heari⟩ := nearest_ring_triangle_ear h hr hp hab hka hkb ha hb hk
  obtain ⟨j,hj,hearj⟩ := nearest_ring_triangle_ear h hr hq hAB hKA hKB hA hB hK
  have he := nearest_ears_unique h hr heari hearj
  rw [← hi,← hj,he]

end N11Formalization.ActualNearestRingTriangles
#check @N11Formalization.ActualNearestRingTriangles.nearest_ring_triangle_ear
#check @N11Formalization.ActualNearestRingTriangles.nearest_ring_triangles_same_set
#print axioms N11Formalization.ActualNearestRingTriangles.local_ring_triples_are_ears
#print axioms N11Formalization.ActualNearestRingTriangles.nearest_ring_triangles_same_set
