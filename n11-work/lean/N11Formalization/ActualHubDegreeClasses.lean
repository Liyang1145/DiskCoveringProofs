import N11Formalization.ActualHubPathCounts

/-! Exhaustive ACTUAL unordered hub degree classes before metric exclusions.
q0:3/10,4/9,5/8,6/7. q1:3/9,4/8,5/7,6/6.
Degree3 is deliberately still present; no metric class is discarded. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubDegreeClasses
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementEarCount
open ActualHubTriangleCensus ActualHubPathCounts

theorem actual_hub_degrees_at_least_three {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    3 ≤ (neighbors R 9).card ∧ 3 ≤ (neighbors R 10).card := by
  classical
  have hc := actual_common_ring_neighbors_card h hr R
  have h9 := Finset.card_le_card (Finset.inter_subset_left :
    ringNeighbors R 9 ∩ ringNeighbors R 10 ⊆ ringNeighbors R 9)
  have h10 := Finset.card_le_card (Finset.inter_subset_right :
    ringNeighbors R 9 ∩ ringNeighbors R 10 ⊆ ringNeighbors R 10)
  rw [hc] at h9 h10
  obtain ⟨a,_,_,_,ha9,ha10,_,_⟩ :=
    ActualRefinementFacetRetention.Refinement.hub_edge_two_retained R h hr
  have hn9 : ActualRefinementVertexLinks.Neighbor R 9 10 :=
    ⟨by decide,a,mem_labelSet.mpr ha9,mem_labelSet.mpr ha10⟩
  have hn10 : ActualRefinementVertexLinks.Neighbor R 10 9 :=
    ⟨by decide,a,mem_labelSet.mpr ha10,mem_labelSet.mpr ha9⟩
  have hs9 := hub_neighbors_split R (Or.inl ⟨rfl,rfl⟩) hn9
  have hs10 := hub_neighbors_split R (Or.inr ⟨rfl,rfl⟩) hn10
  have he9 : (neighbors R 9).card = (ringNeighbors R 9).card+1 := by
    rw [hs9,Finset.card_insert_of_notMem]
    simp
  have he10 : (neighbors R 10).card = (ringNeighbors R 10).card+1 := by
    rw [hs10,Finset.card_insert_of_notMem]
    simp
  omega

def Q0Classes (d e : ℕ) : Prop :=
  (min d e=3 ∧ max d e=10) ∨ (min d e=4 ∧ max d e=9) ∨
    (min d e=5 ∧ max d e=8) ∨ (min d e=6 ∧ max d e=7)

def Q1Classes (d e : ℕ) : Prop :=
  (min d e=3 ∧ max d e=9) ∨ (min d e=4 ∧ max d e=8) ∨
    (min d e=5 ∧ max d e=7) ∨ (min d e=6 ∧ max d e=6)

theorem actual_q0_q1_degree_classes {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ((ringOnlyTriangles R).card=0 ∧ Q0Classes (neighbors R 9).card (neighbors R 10).card) ∨
      ((ringOnlyTriangles R).card=1 ∧ Q1Classes (neighbors R 9).card (neighbors R 10).card) := by
  have hs := actual_hub_degree_sum h hr R
  have hd := actual_hub_degrees_at_least_three h hr R
  have hq := actual_selected_ear_count h hr R
  unfold Q0Classes Q1Classes
  by_cases ho : (neighbors R 9).card ≤ (neighbors R 10).card
  · rw [min_eq_left ho,max_eq_right ho]
    omega
  · have ho' : (neighbors R 10).card ≤ (neighbors R 9).card := by omega
    rw [min_eq_right ho',max_eq_left ho']
    omega

end N11Formalization.ActualHubDegreeClasses
#check @N11Formalization.ActualHubDegreeClasses.actual_q0_q1_degree_classes
#print axioms N11Formalization.ActualHubDegreeClasses.actual_hub_degrees_at_least_three
#print axioms N11Formalization.ActualHubDegreeClasses.actual_q0_q1_degree_classes
