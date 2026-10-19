import N11Formalization.ActualBoundaryFacetEndpoints
import N11Formalization.ActualRingLocality

/-! Genuine switch-adjacent primal vertices have only FOUR possible third
labels: the two hubs or the two flanking rings. This is an actual metric
consumer, not an assumed fan table; flanking ring ears are NOT excluded. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryVertexLocality
open ActualCoverStructuralReduction ActualBoundaryFacetEndpoints ActualRingLocality
open ActualRingDirectionOrder ActualBoundaryCyclicOrder

def Near (i j : Fin 9) : Prop := (j-i).val ≤ 2 ∨ (i-j).val ≤ 2

theorem flank_index : ∀ i k : Fin 9, k ≠ i → k ≠ nextRing i →
    Near i k → Near (nextRing i) k → k = i-1 ∨ k = i+2 := by
  unfold Near
  decide +kernel

theorem common_three_consecutive : ∀ i j k : Fin 9,
    i ≠ j → i ≠ k → j ≠ k → Near i j → Near i k → Near j k →
    ∃ a : Fin 9, ({i,j,k} : Finset (Fin 9)) = {a,a+1,a+2} := by
  unfold Near
  decide +kernel

theorem BoundaryVertex.third_local {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i : Fin 9}
    (v : BoundaryVertex c r i) :
    v.third = 9 ∨ v.third = 10 ∨
      v.third = ringSite (i-1) ∨ v.third = ringSite (i+2) := by
  by_cases hk : v.third.val < 9
  · let K : Fin 9 := ⟨v.third.val,hk⟩
    have hK : ringSite K = v.third := rfl
    have hKi : K ≠ i := by
      intro he
      apply v.third_ne_left
      rw [← hK,he]
    have hKn : K ≠ nextRing i := by
      intro he
      apply v.third_ne_right
      rw [← hK,he]
    have hkRad : dist v.point (c (ringSite K)) ≤ r := by rw [hK,v.third_tie]; exact v.radius
    have hnRad : dist v.point (c (ringSite (nextRing i))) ≤ r :=
      (v.nearest.2 (ringSite i)).trans v.radius
    have hnearI : Near i K := intersection_local h.cover hr h.labels h.midpoint_order v.radius hkRad
    have hnearN : Near (nextRing i) K := intersection_local h.cover hr h.labels h.midpoint_order hnRad hkRad
    rcases flank_index i K hKi hKn hnearI hnearN with he | he
    · exact Or.inr (Or.inr (Or.inl (by rw [← hK,he])))
    · exact Or.inr (Or.inr (Or.inr (by rw [← hK,he])))
  · have hv := v.third.isLt
    have he : v.third.val = 9 ∨ v.third.val = 10 := by omega
    rcases he with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Or.inl (Fin.ext he))

end N11Formalization.ActualBoundaryVertexLocality
#check @N11Formalization.ActualBoundaryVertexLocality.BoundaryVertex.third_local
#print axioms N11Formalization.ActualBoundaryVertexLocality.BoundaryVertex.third_local
