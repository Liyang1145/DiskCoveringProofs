import N11Formalization.ActualFiniteFanFamilies
import N11Formalization.ActualQ0CanonicalNearestRows

/-! Actual exhaustive reduction of the remaining metric producer to
exactly seven uniform class exclusions. ALL seven are still UNPAID
proof inputs; defining these propositions does not certify their bounds.
Same original radius/root, arbitrary representatives and actual fans. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualMetricClassReduction
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualRefinementEarCount
open ActualHubTriangleCensus ActualQ0OrderedTwoFans ActualQ0RunDegrees ActualQ0BoundaryFans
open ActualQ1OrderedCoreFans ActualFiniteFanFamilies ActualQ0CanonicalNearestRows

def Q0RunExclusion (m : ℕ) : Prop :=
  ∀ (c : Fin 11 → Point) (r : ℝ), Representative c r → r < 19/50 →
    ∀ (R : Refinement c r) (O : OrderedData R), O.run_length.val=m → False

def Q1RunExclusion (m : ℕ) : Prop :=
  ∀ (c : Fin 11 → Point) (r : ℝ), Representative c r → r < 19/50 →
    ∀ (R : Refinement c r) (O : OrderedCoreData R), O.run_length.val=m → False

structure SevenClassExclusions : Prop where
  q0_degree3 : Q0RunExclusion 1
  q0_degree4 : Q0RunExclusion 2
  q0_degree5 : Q0RunExclusion 3
  q1_degree3 : Q1RunExclusion 1
  q1_degree4 : Q1RunExclusion 2
  q1_degree5 : Q1RunExclusion 3
  q1_balanced : Q1RunExclusion 4

theorem actual_metric_classification_of_seven (H : SevenClassExclusions) :
    RemainingMetricClassification := by
  intro c r h hr R
  have hr0 : r < 19/50 := hr.trans
    (SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real)
  rcases actual_exhaustive_ordered_families h hr0 R with
    ⟨hq,O,hlo,hhi⟩ | ⟨hq,O,hlo,hhi⟩
  · have hm : O.run_length.val=4 := by
      have h1 : O.run_length.val ≠ 1 := fun he => H.q0_degree3 c r h hr0 R O he
      have h2 : O.run_length.val ≠ 2 := fun he => H.q0_degree4 c r h hr0 R O he
      have h3 : O.run_length.val ≠ 3 := fun he => H.q0_degree5 c r h hr0 R O he
      omega
    have hd := actual_q0_run_degrees h hr0 O
    rw [hm] at hd
    refine ⟨hq,?_⟩
    cases hB : O.fans.colors O.cut <;>
      simp only [hB,hubSite,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] at hd
    all_goals rcases hd with ⟨h9,h10⟩
    all_goals rw [h9,h10]
    all_goals decide
  · have hm : O.run_length.val=1 ∨ O.run_length.val=2 ∨
        O.run_length.val=3 ∨ O.run_length.val=4 := by omega
    rcases hm with h1 | h2 | h3 | h4
    · exact (H.q1_degree3 c r h hr0 R O h1).elim
    · exact (H.q1_degree4 c r h hr0 R O h2).elim
    · exact (H.q1_degree5 c r h hr0 R O h3).elim
    · exact (H.q1_balanced c r h hr0 R O h4).elim

theorem actual_canonical_nearest_of_seven (H : SevenClassExclusions) :
    ActualMainRoute.CanonicalNearest33Obligation :=
  canonical_nearest_of_metric (actual_metric_classification_of_seven H)

theorem main_of_seven_class_certificates
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hclasses : SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  main_of_metric_remaining h450 henergy (actual_metric_classification_of_seven hclasses)

end N11Formalization.ActualMetricClassReduction
#print N11Formalization.ActualMetricClassReduction.SevenClassExclusions
#check @N11Formalization.ActualMetricClassReduction.actual_metric_classification_of_seven
#check @N11Formalization.ActualMetricClassReduction.actual_canonical_nearest_of_seven
#check @N11Formalization.ActualMetricClassReduction.main_of_seven_class_certificates
#print axioms N11Formalization.ActualMetricClassReduction.actual_metric_classification_of_seven
#print axioms N11Formalization.ActualMetricClassReduction.main_of_seven_class_certificates
