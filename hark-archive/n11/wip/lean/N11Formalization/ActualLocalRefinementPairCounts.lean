import N11Formalization.ActualRefinementSideMultiplicity
import N11Formalization.ActualNearestPairRigidity

/-! Complete local selected triangle incidence for actual3/4/5-gon fan
refinements. Adjacent polygon side: exactly1 selected triangle. A selected
nonadjacent diagonal: exactly2. Finite combinatorics uses kernel decide,
not native evaluation. This does NOT count global primal endpoints. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualLocalRefinementPairCounts
open ActualIncidentFanRefinement

def Adjacent {n : ℕ} (i j : Fin n) : Prop := j = finRotate n i ∨ i = finRotate n j
instance {n : ℕ} (i j : Fin n) : Decidable (Adjacent i j) := by unfold Adjacent; infer_instance

def pairIndices {n : ℕ} (hn : 0 < n) (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => FanIndex k ∧ i ∈ indexTriangle hn k ∧ j ∈ indexTriangle hn k)

theorem adjacent_pair_count {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i j : Fin n, i ≠ j → Adjacent i j →
      (pairIndices (by omega : 0 < n) i j).card = 1 := by
  interval_cases n <;> decide +revert

theorem selected_diagonal_count {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i j k : Fin n, i ≠ j → ¬ Adjacent i j → FanIndex k →
      i ∈ indexTriangle (by omega : 0 < n) k →
      j ∈ indexTriangle (by omega : 0 < n) k →
      (pairIndices (by omega : 0 < n) i j).card = 2 := by
  interval_cases n <;> decide +revert

theorem selected_pair_count_le_two {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i j : Fin n, i ≠ j → (pairIndices (by omega : 0 < n) i j).card ≤ 2 := by
  interval_cases n <;> decide +revert

theorem selected_diagonal_has_apex {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i j k : Fin n, i ≠ j → ¬ Adjacent i j → FanIndex k →
      i ∈ indexTriangle (by omega : 0 < n) k →
      j ∈ indexTriangle (by omega : 0 < n) k →
      i.val = 0 ∨ j.val = 0 := by
  interval_cases n <;> decide +revert

end N11Formalization.ActualLocalRefinementPairCounts
#check @N11Formalization.ActualLocalRefinementPairCounts.adjacent_pair_count
#check @N11Formalization.ActualLocalRefinementPairCounts.selected_diagonal_count
#print axioms N11Formalization.ActualLocalRefinementPairCounts.adjacent_pair_count
#print axioms N11Formalization.ActualLocalRefinementPairCounts.selected_diagonal_count
#print axioms N11Formalization.ActualLocalRefinementPairCounts.selected_pair_count_le_two
