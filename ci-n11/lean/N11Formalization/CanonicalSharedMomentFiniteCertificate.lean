import N11Formalization.SharedMomentEfficientFactorCertificate
import N11Formalization.ActualCanonicalSharedMomentConsumer
import N11Formalization.ActualMetricClassReduction

/-! Canonical class certificates containing rational tables and finite
factor trees only. Their semantic bounds are produced internally; actual
graph matching, slot order, metric identities and boundary ties are proved
from the original representative. No class is asserted without a complete
instantiation of its finite table and strict rational total check. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CanonicalSharedMomentFiniteCertificate
open ActualCanonicalMomentTransport ActualCanonicalSharedMomentConsumer
open SharedMomentFiniteFactorCertificate SharedMomentEfficientFactorCertificate ActualOrderedMetricGraphs
open ActualSharedMomentSharpConstant ActualRingLinkBoundaryData
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualBoundaryNineTies
open ActualMetricClassReduction

structure FiniteCanonicalCertificate {F : Finset (Finset (Fin 11))}
    (D : CanonicalCoeffQ F) (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta alpha : ℚ) where
  faceMax : F → ℚ
  switchMax : Fin 9 → ℚ
  sectorMax : Fin 9 → ℚ
  balance : CanonicalMaskBalancedQ D
  edge_nonnegative : ∀ e ∈ faceEdges F, 0 ≤ kap e
  eta_nonnegative : 0 ≤ eta
  bracket : EarAsinBracket alpha
  faces : ∀ f : F, EfficientFaceCertificate (canonicalFaceP D kap f)
    (canonicalFaceQ D f) (canonicalFaceB D f) (faceMax f)
  switches : ∀ i : Fin 9, SwitchCertificate (canonicalSwitchP D kap i)
    (canonicalSwitchQ D i) (canonicalSwitchB D i)
    (canonicalSwitchD2 D i) (canonicalSwitchD1 D i) (switchMax i)
  sectors : ∀ i : Fin 9, EfficientSectorCertificate (canonicalSectorC D ear eta i)
    (D.mu (nextSite i)) (D.leftSecond i) (D.rightSecond i)
    (D.leftFirst i) (D.rightFirst i) (sectorMax i)
  strict : canonicalTotalUpperQ D kap eta alpha faceMax switchMax sectorMax < RatInterval.piLo

def FiniteCanonicalCertificate.toCanonical {F : Finset (Finset (Fin 11))}
    {D : CanonicalCoeffQ F} {kap : Finset (Fin 11) → ℚ} {ear : Fin 9} {eta alpha : ℚ}
    (C : FiniteCanonicalCertificate D kap ear eta alpha) : CanonicalCertificate D kap ear eta alpha where
  faceMax := C.faceMax
  switchMax := C.switchMax
  sectorMax := C.sectorMax
  balance := C.balance
  edge_nonnegative := C.edge_nonnegative
  eta_nonnegative := C.eta_nonnegative
  bracket := C.bracket
  bounds := ⟨fun f => (C.faces f).sound,fun i => (C.switches i).sound,fun i => (C.sectors i).sound⟩
  strict := C.strict

theorem q0_run_exclusion_of_finite (m : Fin 9) (D : CanonicalCoeffQ (q0Faces m))
    (kap : Finset (Fin 11) → ℚ) (alpha : ℚ)
    (K : FiniteCanonicalCertificate D kap 0 0 alpha) : Q0RunExclusion m.val := by
  intro c r h hr R O hm
  obtain ⟨v⟩ := nineTies_of_cover h.cover hr h.labels h.midpoint_order
  have he : O.run_length=m := Fin.ext hm
  cases he
  exact exclude_q0_ordered h hr R v O D kap alpha K.toCanonical

theorem q1_run_exclusion_of_finite (m : Fin 8) (alpha : ℚ)
    (certificates : ∀ k : Fin 8,
      ∃ D : CanonicalCoeffQ (q1Faces k m), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
        Nonempty (FiniteCanonicalCertificate D kap 0 eta alpha)) : Q1RunExclusion m.val := by
  intro c r h hr R O hm
  obtain ⟨v⟩ := nineTies_of_cover h.cover hr h.labels h.midpoint_order
  have he : O.run_length=m := Fin.ext hm
  cases he
  obtain ⟨D,kap,eta,⟨K⟩⟩ := certificates O.cut
  exact exclude_q1_ordered h hr R v O D kap eta alpha K.toCanonical

def Q0FiniteTable (m : Fin 9) : Prop :=
  ∃ D : CanonicalCoeffQ (q0Faces m), ∃ kap : Finset (Fin 11) → ℚ,
    Nonempty (FiniteCanonicalCertificate D kap 0 0 sharpAlpha)

def Q1FiniteTables (m : Fin 8) : Prop :=
  ∀ k : Fin 8, ∃ D : CanonicalCoeffQ (q1Faces k m), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
    Nonempty (FiniteCanonicalCertificate D kap 0 eta sharpAlpha)

theorem q0_exclusion_of_table {m : Fin 9} (T : Q0FiniteTable m) : Q0RunExclusion m.val := by
  obtain ⟨D,kap,⟨K⟩⟩ := T
  exact q0_run_exclusion_of_finite m D kap sharpAlpha K

theorem q1_exclusion_of_tables {m : Fin 8} (T : Q1FiniteTables m) : Q1RunExclusion m.val :=
  q1_run_exclusion_of_finite m sharpAlpha T

structure SevenFiniteTables : Prop where
  q0_degree3 : Q0FiniteTable 1
  q0_degree4 : Q0FiniteTable 2
  q0_degree5 : Q0FiniteTable 3
  q1_degree3 : Q1FiniteTables 1
  q1_degree4 : Q1FiniteTables 2
  q1_degree5 : Q1FiniteTables 3
  q1_balanced : Q1FiniteTables 4

theorem seven_class_exclusions_of_finite (T : SevenFiniteTables) : SevenClassExclusions :=
  ⟨q0_exclusion_of_table T.q0_degree3,q0_exclusion_of_table T.q0_degree4,
    q0_exclusion_of_table T.q0_degree5,q1_exclusion_of_tables T.q1_degree3,
    q1_exclusion_of_tables T.q1_degree4,q1_exclusion_of_tables T.q1_degree5,
    q1_exclusion_of_tables T.q1_balanced⟩

theorem main_of_finite_class_tables
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius) (T : SevenFiniteTables) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  main_of_seven_class_certificates h450 henergy (seven_class_exclusions_of_finite T)

theorem full_disk_bound_of_finite_class_tables
    (h450 : C450Source11Segment.RemainingSourceObligation)
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius) (T : SevenFiniteTables) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main (main_of_finite_class_tables h450 henergy T)).bounds

end N11Formalization.CanonicalSharedMomentFiniteCertificate
#check @N11Formalization.CanonicalSharedMomentFiniteCertificate.FiniteCanonicalCertificate
#check @N11Formalization.CanonicalSharedMomentFiniteCertificate.SevenFiniteTables
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.FiniteCanonicalCertificate.toCanonical
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.q0_run_exclusion_of_finite
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.q1_run_exclusion_of_finite
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.seven_class_exclusions_of_finite
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.main_of_finite_class_tables
#print axioms N11Formalization.CanonicalSharedMomentFiniteCertificate.full_disk_bound_of_finite_class_tables
