import N11Formalization.ActualQ1FacePartition

/-! Actual q1 ordered run lengths and real hub degrees.
First degree m+2; second degree10-m. Every original ring disk and ear
is retained; no q1 graph or closed metric class is excluded here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ1RunDegrees
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualHubTriangleCensus ActualQ0BoundaryFans ActualQ1OrderedCoreFans ActualQ1FacePartition

theorem shifted_owner_count (f : Fin 8 → Bool) (b : Bool) (k : Fin 8) :
    (Finset.univ.filter (fun i : Fin 8 => f (i+k)=b)).card =
      (Finset.univ.filter (fun i : Fin 8 => f i=b)).card := by
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

theorem prefix_card : ∀ m : Fin 8,
    (Finset.univ.filter (fun i : Fin 8 => i.val < m.val)).card=m.val := by decide +kernel
theorem suffix_card : ∀ m : Fin 8,
    (Finset.univ.filter (fun i : Fin 8 => ¬ i.val < m.val)).card=8-m.val := by decide +kernel

theorem OrderedCoreData.first_owner_count {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedCoreData R) :
    (Finset.univ.filter (fun i : Fin 8 => O.fans.colors i=O.fans.colors O.cut)).card =
      O.run_length.val := by
  classical
  rw [← shifted_owner_count O.fans.colors (O.fans.colors O.cut) O.cut]
  have he : Finset.univ.filter (fun i : Fin 8 => O.fans.colors (i+O.cut)=O.fans.colors O.cut) =
      Finset.univ.filter (fun i : Fin 8 => i.val < O.run_length.val) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,O.order]
    by_cases hi : i.val < O.run_length.val <;> simp [hi]
  rw [he,prefix_card]

theorem OrderedCoreData.second_owner_count {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedCoreData R) :
    (Finset.univ.filter (fun i : Fin 8 => O.fans.colors i= !O.fans.colors O.cut)).card =
      8-O.run_length.val := by
  classical
  rw [← shifted_owner_count O.fans.colors (!O.fans.colors O.cut) O.cut]
  have he : Finset.univ.filter (fun i : Fin 8 => O.fans.colors (i+O.cut)= !O.fans.colors O.cut) =
      Finset.univ.filter (fun i : Fin 8 => ¬ i.val < O.run_length.val) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,O.order]
    by_cases hi : i.val < O.run_length.val <;> simp [hi]
  rw [he,suffix_card]

theorem actual_q1_run_degrees {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedCoreData R) :
    (neighbors R (hubSite (O.fans.colors O.cut))).card=O.run_length.val+2 ∧
      (neighbors R (hubSite (!O.fans.colors O.cut))).card=(8-O.run_length.val)+2 := by
  constructor
  · rw [actual_q1_hub_degree_owner_count h hr O.fans,OrderedCoreData.first_owner_count O]
  · rw [actual_q1_hub_degree_owner_count h hr O.fans,OrderedCoreData.second_owner_count O]

theorem reverse_core_gap_sum : ∀ a b : Fin 8, a≠b → (b-a).val+(a-b).val=8 := by
  decide +kernel

def OrderedCoreData.swap {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedCoreData R) : OrderedCoreData R := by
  have hc : ∀ i : Fin 8, O.fans.colors (i-1) ≠ O.fans.colors i ↔ i=O.second ∨ i=O.cut := by
    intro i
    rw [O.changes,or_comm]
  have H := ActualFiniteBinaryCycleRuns.two_changes_runs O.endpoints_ne.symm hc
  exact ⟨O.fans,O.second,O.cut,O.endpoints_ne.symm,O.cut-O.second,
    Nat.pos_of_ne_zero H.1,rfl,hc,H.2.2,O.central_second,O.central_first⟩

theorem actual_q1_short_run_data {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ActualRefinementEarCount.ringOnlyTriangles R).card=1) :
    ∃ O : OrderedCoreData R, 1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4 := by
  obtain ⟨O⟩ := actual_q1_ordered_core_fans h hr R hq
  by_cases hm : O.run_length.val ≤ 4
  · exact ⟨O,Nat.succ_le_of_lt O.positive,hm⟩
  · refine ⟨OrderedCoreData.swap O,Nat.succ_le_of_lt (OrderedCoreData.swap O).positive,?_⟩
    have hh := reverse_core_gap_sum O.cut O.second O.endpoints_ne
    rw [← O.length_exact] at hh
    change (O.cut-O.second).val ≤ 4
    omega

end N11Formalization.ActualQ1RunDegrees
#check @N11Formalization.ActualQ1RunDegrees.actual_q1_run_degrees
#check @N11Formalization.ActualQ1RunDegrees.actual_q1_short_run_data
#print axioms N11Formalization.ActualQ1RunDegrees.actual_q1_run_degrees
#print axioms N11Formalization.ActualQ1RunDegrees.actual_q1_short_run_data
