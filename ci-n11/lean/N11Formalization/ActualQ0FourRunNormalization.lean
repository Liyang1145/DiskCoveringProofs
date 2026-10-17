import N11Formalization.ActualQ0RunDegrees

/-! Actual q0(6,7) has a legitimate four-edge first run after choosing
one of the two actual central endpoints. This does not prove the metric
exclusions needed to assert q0(6,7) for an arbitrary representative. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ0FourRunNormalization
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementEarCount ActualHubTriangleCensus
open ActualQ0OrderedTwoFans ActualQ0RunDegrees ActualBinaryCycleRuns

theorem reverse_gap_sum : ∀ a b : Fin 9, a ≠ b → (b-a).val+(a-b).val=9 := by
  decide +kernel

def OrderedData.swap {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedData R) : OrderedData R := by
  have hc : ∀ i : Fin 9, O.fans.colors (i-1) ≠ O.fans.colors i ↔ i=O.second ∨ i=O.cut := by
    intro i
    rw [O.changes,or_comm]
  have H := two_changes_runs O.endpoints_ne.symm hc
  exact ⟨O.fans,O.second,O.cut,O.endpoints_ne.symm,O.cut-O.second,
    Nat.pos_of_ne_zero H.1,rfl,hc,H.2.2,
    fun a ha => (O.central_labels a ha).elim Or.inr Or.inl,
    O.central_second,O.central_first⟩

theorem actual_q0_four_run_data {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0)
    (hd : min (neighbors R 9).card (neighbors R 10).card=6 ∧
      max (neighbors R 9).card (neighbors R 10).card=7) :
    ∃ O : OrderedData R, O.run_length.val=4 := by
  obtain ⟨O⟩ := actual_q0_ordered_two_fans h hr R hq
  rcases actual_q0_six_seven_run_lengths h hr O hd with h4 | h5
  · exact ⟨O,h4⟩
  · refine ⟨OrderedData.swap O,?_⟩
    have hh := reverse_gap_sum O.cut O.second O.endpoints_ne
    have hL : (O.second-O.cut).val=5 := by rw [← O.length_exact,h5]
    change (O.cut-O.second).val=4
    omega

theorem four_run_second {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedData R) (h4 : O.run_length.val=4) : O.second=(4 : Fin 9)+O.cut := by
  have hh : O.run_length=(4 : Fin 9) := Fin.ext h4
  have hL := O.length_exact
  rw [hh] at hL
  rw [hL,sub_add_cancel]

end N11Formalization.ActualQ0FourRunNormalization
#check @N11Formalization.ActualQ0FourRunNormalization.actual_q0_four_run_data
#print axioms N11Formalization.ActualQ0FourRunNormalization.actual_q0_four_run_data
