import N11Formalization.CanonicalSharedMomentFiniteCertificate
import N11Formalization.CanonicalSharedMomentOrbitTransport

/-! The balanced Q1 class consumes two complete finite certificates only.
Eight cuts and every actual face/slot arrangement are handled internally by
proved graph and factor transport. The other six finite class tables and
the original source/energy obligations remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CanonicalBalancedFiniteClassCertificate
open CanonicalSharedMomentFiniteCertificate CanonicalSharedMomentOrbitTransport
open ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport ActualOrderedMetricGraphs
open ActualMetricClassReduction ActualBoundaryNineTies

def RepresentativeFiniteTable (k : Fin 8) : Prop :=
  ∃ D : CanonicalCoeffQ (q1Faces k 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
    Nonempty (FiniteCanonicalCertificate D kap 0 eta sharpAlpha)

structure BalancedTwoFiniteTables : Prop where
  first : RepresentativeFiniteTable 7
  second : RepresentativeFiniteTable 1

theorem balanced_exclusion_of_two_finite (T : BalancedTwoFiniteTables) : Q1RunExclusion 4 := by
  have H7 : ∃ D : CanonicalCoeffQ (q1Faces 7 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta sharpAlpha) := by
    obtain ⟨D,kap,eta,⟨C⟩⟩ := T.first
    exact ⟨D,kap,eta,⟨C.toCanonical⟩⟩
  have H1 : ∃ D : CanonicalCoeffQ (q1Faces 1 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta sharpAlpha) := by
    obtain ⟨D,kap,eta,⟨C⟩⟩ := T.second
    exact ⟨D,kap,eta,⟨C.toCanonical⟩⟩
  have Hall := balanced_certificates_of_two sharpAlpha H7 H1
  intro c r h hr R O hm
  obtain ⟨v⟩ := nineTies_of_cover h.cover hr h.labels h.midpoint_order
  have he : O.run_length=(4 : Fin 8) := Fin.ext hm
  have hcut := Hall O.cut
  rw [← he] at hcut
  obtain ⟨D,kap,eta,⟨K⟩⟩ := hcut
  exact exclude_q1_ordered h hr R v O D kap eta sharpAlpha K

structure SixAndBalancedFiniteTables : Prop where
  q0_degree3 : Q0FiniteTable 1
  q0_degree4 : Q0FiniteTable 2
  q0_degree5 : Q0FiniteTable 3
  q1_degree3 : Q1FiniteTables 1
  q1_degree4 : Q1FiniteTables 2
  q1_degree5 : Q1FiniteTables 3
  balanced : BalancedTwoFiniteTables

theorem seven_classes_of_six_and_two (T : SixAndBalancedFiniteTables) : SevenClassExclusions :=
  ⟨q0_exclusion_of_table T.q0_degree3,q0_exclusion_of_table T.q0_degree4,
    q0_exclusion_of_table T.q0_degree5,q1_exclusion_of_tables T.q1_degree3,
    q1_exclusion_of_tables T.q1_degree4,q1_exclusion_of_tables T.q1_degree5,
    balanced_exclusion_of_two_finite T.balanced⟩

theorem full_disk_bound_of_six_and_two
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius) (T : SixAndBalancedFiniteTables) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_seven_class_certificates h450 henergy (seven_classes_of_six_and_two T))).bounds

end N11Formalization.CanonicalBalancedFiniteClassCertificate
#check @N11Formalization.CanonicalBalancedFiniteClassCertificate.BalancedTwoFiniteTables
#check @N11Formalization.CanonicalBalancedFiniteClassCertificate.SixAndBalancedFiniteTables
#print axioms N11Formalization.CanonicalBalancedFiniteClassCertificate.balanced_exclusion_of_two_finite
#print axioms N11Formalization.CanonicalBalancedFiniteClassCertificate.seven_classes_of_six_and_two
#print axioms N11Formalization.CanonicalBalancedFiniteClassCertificate.full_disk_bound_of_six_and_two
