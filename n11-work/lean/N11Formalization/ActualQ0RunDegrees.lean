import N11Formalization.ActualQ0OrderedTwoFans
import N11Formalization.ActualQ0FacePartition

/-! Productive actual q0 run lengths agree with real hub degrees.
No metric exclusion or canonical4/5 run is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ0RunDegrees
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualHubTriangleCensus ActualQ0BoundaryFans ActualQ0OrderedTwoFans
open ActualQ0FacePartition

theorem shifted_color_count (f : Fin 9 → Bool) (b : Bool) (k : Fin 9) :
    (Finset.univ.filter (fun i : Fin 9 => f (i+k)=b)).card =
      (Finset.univ.filter (fun i : Fin 9 => f i=b)).card := by
  classical
  apply Finset.card_bij (fun i _ => i+k)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    exact add_right_cancel he
  · intro j hj
    refine ⟨j-k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,sub_add_cancel _ _⟩
    rw [sub_add_cancel]
    exact (Finset.mem_filter.mp hj).2

theorem prefix_card : ∀ m : Fin 9,
    (Finset.univ.filter (fun i : Fin 9 => i.val < m.val)).card=m.val := by decide +kernel

theorem suffix_card : ∀ m : Fin 9,
    (Finset.univ.filter (fun i : Fin 9 => ¬ i.val < m.val)).card=9-m.val := by decide +kernel

theorem bool_complement_ne : ∀ b : Bool, !b ≠ b := by decide +kernel

theorem OrderedData.first_color_count {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedData R) :
    (Finset.univ.filter (fun i : Fin 9 => O.fans.colors i=O.fans.colors O.cut)).card =
      O.run_length.val := by
  classical
  rw [← shifted_color_count O.fans.colors (O.fans.colors O.cut) O.cut]
  have he : Finset.univ.filter (fun i : Fin 9 => O.fans.colors (i+O.cut)=O.fans.colors O.cut) =
      Finset.univ.filter (fun i : Fin 9 => i.val < O.run_length.val) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,O.order]
    by_cases hi : i.val < O.run_length.val
    · simp [hi]
    · simp [hi,bool_complement_ne]
  rw [he,prefix_card]

theorem OrderedData.second_color_count {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedData R) :
    (Finset.univ.filter (fun i : Fin 9 => O.fans.colors i= !O.fans.colors O.cut)).card =
      9-O.run_length.val := by
  classical
  rw [← shifted_color_count O.fans.colors (!O.fans.colors O.cut) O.cut]
  have he : Finset.univ.filter (fun i : Fin 9 => O.fans.colors (i+O.cut)= !O.fans.colors O.cut) =
      Finset.univ.filter (fun i : Fin 9 => ¬ i.val < O.run_length.val) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,O.order]
    by_cases hi : i.val < O.run_length.val
    · simp [hi,(bool_complement_ne (O.fans.colors O.cut)).symm]
    · simp [hi]
  rw [he,suffix_card]

theorem actual_q0_run_degrees {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedData R) :
    (neighbors R (hubSite (O.fans.colors O.cut))).card = O.run_length.val+2 ∧
      (neighbors R (hubSite (!O.fans.colors O.cut))).card = (9-O.run_length.val)+2 := by
  constructor
  · rw [actual_q0_hub_degree_color_count h hr O.fans,
      OrderedData.first_color_count O]
  · rw [actual_q0_hub_degree_color_count h hr O.fans,
      OrderedData.second_color_count O]

theorem actual_q0_six_seven_run_lengths {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedData R)
    (hd : min (neighbors R 9).card (neighbors R 10).card = 6 ∧
      max (neighbors R 9).card (neighbors R 10).card = 7) :
    O.run_length.val=4 ∨ O.run_length.val=5 := by
  have hs := actual_q0_run_degrees h hr O
  have hm := O.run_length.isLt
  have hp := O.positive
  cases hB : O.fans.colors O.cut <;>
    simp only [hB,hubSite,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] at hs
  all_goals
    by_cases ho : (neighbors R 9).card ≤ (neighbors R 10).card
    · rw [min_eq_left ho,max_eq_right ho] at hd
      omega
    · have ho' : (neighbors R 10).card ≤ (neighbors R 9).card := by omega
      rw [min_eq_right ho',max_eq_left ho'] at hd
      omega

end N11Formalization.ActualQ0RunDegrees
#check @N11Formalization.ActualQ0RunDegrees.actual_q0_run_degrees
#check @N11Formalization.ActualQ0RunDegrees.actual_q0_six_seven_run_lengths
#print axioms N11Formalization.ActualQ0RunDegrees.actual_q0_run_degrees
#print axioms N11Formalization.ActualQ0RunDegrees.actual_q0_six_seven_run_lengths
