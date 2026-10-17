import N11Formalization.ActualQ1RunDegrees
import N11Formalization.ActualQ0FourRunNormalization

/-! Productive exhaustive ACTUAL finite fan families for every same-radius
representative. q0 has a four-or-shorter nine-cycle run; q1 has a four-or-
shorter eight-core run plus its real ninth ring ear. No metric class is
excluded. Permutations/cuts are produced, not a symmetry restriction. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualFiniteFanFamilies
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualRefinementEarCount
open ActualQ0OrderedTwoFans ActualQ0FourRunNormalization
open ActualQ1OrderedCoreFans ActualQ1RunDegrees

theorem actual_q0_short_run_data {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0) :
    ∃ O : OrderedData R, 1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4 := by
  obtain ⟨O⟩ := actual_q0_ordered_two_fans h hr R hq
  by_cases hm : O.run_length.val ≤ 4
  · exact ⟨O,Nat.succ_le_of_lt O.positive,hm⟩
  · refine ⟨ActualQ0FourRunNormalization.OrderedData.swap O,
      Nat.succ_le_of_lt (ActualQ0FourRunNormalization.OrderedData.swap O).positive,?_⟩
    have hh := reverse_gap_sum O.cut O.second O.endpoints_ne
    rw [← O.length_exact] at hh
    change (O.cut-O.second).val ≤ 4
    omega

theorem actual_exhaustive_ordered_families {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ((ringOnlyTriangles R).card=0 ∧
      ∃ O : OrderedData R, 1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4) ∨
    ((ringOnlyTriangles R).card=1 ∧
      ∃ O : OrderedCoreData R, 1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4) := by
  have hq := actual_selected_ear_count h hr R
  by_cases hz : (ringOnlyTriangles R).card=0
  · exact Or.inl ⟨hz,actual_q0_short_run_data h hr R hz⟩
  · have ho : (ringOnlyTriangles R).card=1 := by omega
    exact Or.inr ⟨ho,actual_q1_short_run_data h hr R ho⟩

theorem actual_cover_finite_family_producer {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    ∃ R : Refinement c r,
      ((ringOnlyTriangles R).card=0 ∧
        ∃ O : OrderedData R, 1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4) ∨
      ((ringOnlyTriangles R).card=1 ∧
        ∃ O : OrderedCoreData R, 1 ≤ O.run_length.val ∧ O.run_length.val ≤ 4) := by
  obtain ⟨R⟩ := actual_refinement h hr
  exact ⟨R,actual_exhaustive_ordered_families h hr R⟩

end N11Formalization.ActualFiniteFanFamilies
#check @N11Formalization.ActualFiniteFanFamilies.actual_cover_finite_family_producer
#print axioms N11Formalization.ActualFiniteFanFamilies.actual_cover_finite_family_producer
