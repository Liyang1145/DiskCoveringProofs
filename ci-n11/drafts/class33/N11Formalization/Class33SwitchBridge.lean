import N11Formalization.SharedMomentConcreteSwitchBatch
import N11Formalization.Class33RepData

/-! Class33 DRAFT (uncompiled): closes A25 gaps G1/G2 for the nine concrete switch certificates.
* G2 (structure): `switchCertificate_of_direct` turns a direct-leaf tree on `switchCell 0 (1571/1000)`
  into the consumer's `SwitchCertificate` (GradientSwitchLeaf, root containing `switchRoot`).
* G2 (coefficients): batch switch K is canonical switch j = K-1 (mod 9) of `rep7D` (q1Faces 7 4).
  The batch's "start0" is the historical label set; Lean labels are ring h -> h-1, so the index shifts.
* G1 (aggregation): `rep7SwitchMax` uses the PER-SWITCH batch bounds (no uniform 1/2000 or 141/1e6
  qualification is needed or possible: switches K=4,5,8 have bounds 51029/1e6, 4839/2e5, 14023/1e6);
  their sum is exactly `start0_switch_total_bound = 22523/250000`, which enters
  `canonicalTotalUpperQ` additively.
* G4: only `SharedMomentConcreteSwitchBatch.*` names are used, fully qualified; the
  `SharedMomentConcreteLeafControls.start0_switch0_bound = 1/2000` control is never opened. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33SwitchBridge
open RationalBoxSubdivision SharedMomentFiniteFactorCertificate SharedMomentFactorIntervalCertificate
open ActualSharedMomentAdaptiveCertificate ActualCanonicalMomentTransport ActualEdgeFlagSums Class33RepData
open ActualRingDirectionOrder ActualRingLinkBoundaryData

theorem certificate_mono {I : Type*} [DecidableEq I] {P Q : Cell I → Prop}
    (h : ∀ B, P B → Q B) {B : Cell I} (T : Certificate P B) : Certificate Q B := by
  induction T with
  | accept hp => exact Certificate.accept (h _ hp)
  | split i t hlo hhi _ _ ihl ihr => exact Certificate.split i t hlo hhi ihl ihr

theorem fullSwitchCell_contains :
    ContainsCell (SharedMomentConcreteLeafControls.switchCell 0 (1571/1000 : ℚ)) switchRoot := by
  intro i
  fin_cases i
  refine ⟨by simp [SharedMomentConcreteLeafControls.switchCell,switchRoot],?_⟩
  simp only [SharedMomentConcreteLeafControls.switchCell,switchRoot]
  norm_num [RatInterval.piHi]

/-- Structure bridge: a direct-leaf tree over the full switch cell is a consumer `SwitchCertificate`. -/
def switchCertificate_of_direct {p q b d2 d1 M : ℚ}
    (T : Certificate (fun B => switchDirectUpperQ p q b d2 d1 B ≤ M)
      (SharedMomentConcreteLeafControls.switchCell 0 (1571/1000 : ℚ))) :
    SwitchCertificate p q b d2 d1 M where
  root := SharedMomentConcreteLeafControls.switchCell 0 (1571/1000 : ℚ)
  contains := fullSwitchCell_contains
  tree := certificate_mono (fun _ h => Or.inl (Or.inr (Or.inl h))) T

def batchSwitch0 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_node_762
def batchSwitch1 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_node_760
def batchSwitch2 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_node_912
def batchSwitch3 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_node_854
def batchSwitch4 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_node_942
def batchSwitch5 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_node_996
def batchSwitch6 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_node_884
def batchSwitch7 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_node_878
def batchSwitch8 : SwitchCertificate N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_p N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_q N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_b
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_d2 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_d1 N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_bound :=
  switchCertificate_of_direct N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_node_926

/-- Per-switch maxima in Lean switch order j (batch switch K = j+1 mod 9). -/
def rep7SwitchMaxN : ℕ → ℚ
  | 0 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_bound
  | 1 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_bound
  | 2 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_bound
  | 3 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_bound
  | 4 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_bound
  | 5 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_bound
  | 6 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_bound
  | 7 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_bound
  | 8 => N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_bound
  | _ => 0
def rep7SwitchMax (i : Fin 9) : ℚ := rep7SwitchMaxN i.val

/-- G1: aggregation. The nine per-switch bounds sum exactly to `start0_switch_total_bound`. -/
theorem rep7_switch_aggregate :
    (∑ i : Fin 9, rep7SwitchMax i) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch_total_bound := by
  show (∑ i : Fin 9, rep7SwitchMaxN i.val) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.isValue]
  norm_num [rep7SwitchMaxN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_bound,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_bound,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_bound,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_bound,
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_bound,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_bound,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_bound,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_bound,
    N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_bound,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch_total_bound]

/-- G2 coefficient identity: canonical switch 0 of rep7 = batch switch 1. -/
theorem rep7_switch0_eq :
    canonicalSwitchP rep7D rep7Kap 0=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_p ∧ canonicalSwitchQ rep7D 0=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_q ∧
    canonicalSwitchB rep7D 0=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_b ∧ canonicalSwitchD2 rep7D 0=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_d2 ∧
    canonicalSwitchD1 rep7D 0=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_d1 := by
  have hc : cycleEdge 0 = ({(0 : Fin 11),(1 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(0 : Fin 11),(1 : Fin 11)} : Finset (Fin 11)) = 3 := by decide
  have hpred : (((0 : Fin 9) - 1 : Fin 9) : ℕ) = 8 := by decide
  have hj : ((0 : Fin 9) : ℕ) = 0 := rfl
  have hne : (0 : Fin 11) ≠ (1 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_d1]

/-- G2 coefficient identity: canonical switch 1 of rep7 = batch switch 2. -/
theorem rep7_switch1_eq :
    canonicalSwitchP rep7D rep7Kap 1=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_p ∧ canonicalSwitchQ rep7D 1=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_q ∧
    canonicalSwitchB rep7D 1=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_b ∧ canonicalSwitchD2 rep7D 1=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_d2 ∧
    canonicalSwitchD1 rep7D 1=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_d1 := by
  have hc : cycleEdge 1 = ({(1 : Fin 11),(2 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(1 : Fin 11),(2 : Fin 11)} : Finset (Fin 11)) = 6 := by decide
  have hpred : (((1 : Fin 9) - 1 : Fin 9) : ℕ) = 0 := by decide
  have hj : ((1 : Fin 9) : ℕ) = 1 := rfl
  have hne : (1 : Fin 11) ≠ (2 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_d1]

/-- G2 coefficient identity: canonical switch 2 of rep7 = batch switch 3. -/
theorem rep7_switch2_eq :
    canonicalSwitchP rep7D rep7Kap 2=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_p ∧ canonicalSwitchQ rep7D 2=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_q ∧
    canonicalSwitchB rep7D 2=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_b ∧ canonicalSwitchD2 rep7D 2=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_d2 ∧
    canonicalSwitchD1 rep7D 2=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_d1 := by
  have hc : cycleEdge 2 = ({(2 : Fin 11),(3 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(2 : Fin 11),(3 : Fin 11)} : Finset (Fin 11)) = 12 := by decide
  have hpred : (((2 : Fin 9) - 1 : Fin 9) : ℕ) = 1 := by decide
  have hj : ((2 : Fin 9) : ℕ) = 2 := rfl
  have hne : (2 : Fin 11) ≠ (3 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_d1]

/-- G2 coefficient identity: canonical switch 3 of rep7 = batch switch 4. -/
theorem rep7_switch3_eq :
    canonicalSwitchP rep7D rep7Kap 3=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_p ∧ canonicalSwitchQ rep7D 3=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_q ∧
    canonicalSwitchB rep7D 3=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_b ∧ canonicalSwitchD2 rep7D 3=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_d2 ∧
    canonicalSwitchD1 rep7D 3=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_d1 := by
  have hc : cycleEdge 3 = ({(3 : Fin 11),(4 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(3 : Fin 11),(4 : Fin 11)} : Finset (Fin 11)) = 24 := by decide
  have hpred : (((3 : Fin 9) - 1 : Fin 9) : ℕ) = 2 := by decide
  have hj : ((3 : Fin 9) : ℕ) = 3 := rfl
  have hne : (3 : Fin 11) ≠ (4 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_d1]

/-- G2 coefficient identity: canonical switch 4 of rep7 = batch switch 5. -/
theorem rep7_switch4_eq :
    canonicalSwitchP rep7D rep7Kap 4=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_p ∧ canonicalSwitchQ rep7D 4=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_q ∧
    canonicalSwitchB rep7D 4=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_b ∧ canonicalSwitchD2 rep7D 4=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_d2 ∧
    canonicalSwitchD1 rep7D 4=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_d1 := by
  have hc : cycleEdge 4 = ({(4 : Fin 11),(5 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(4 : Fin 11),(5 : Fin 11)} : Finset (Fin 11)) = 48 := by decide
  have hpred : (((4 : Fin 9) - 1 : Fin 9) : ℕ) = 3 := by decide
  have hj : ((4 : Fin 9) : ℕ) = 4 := rfl
  have hne : (4 : Fin 11) ≠ (5 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_d1]

/-- G2 coefficient identity: canonical switch 5 of rep7 = batch switch 6. -/
theorem rep7_switch5_eq :
    canonicalSwitchP rep7D rep7Kap 5=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_p ∧ canonicalSwitchQ rep7D 5=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_q ∧
    canonicalSwitchB rep7D 5=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_b ∧ canonicalSwitchD2 rep7D 5=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_d2 ∧
    canonicalSwitchD1 rep7D 5=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_d1 := by
  have hc : cycleEdge 5 = ({(5 : Fin 11),(6 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(5 : Fin 11),(6 : Fin 11)} : Finset (Fin 11)) = 96 := by decide
  have hpred : (((5 : Fin 9) - 1 : Fin 9) : ℕ) = 4 := by decide
  have hj : ((5 : Fin 9) : ℕ) = 5 := rfl
  have hne : (5 : Fin 11) ≠ (6 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_d1]

/-- G2 coefficient identity: canonical switch 6 of rep7 = batch switch 7. -/
theorem rep7_switch6_eq :
    canonicalSwitchP rep7D rep7Kap 6=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_p ∧ canonicalSwitchQ rep7D 6=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_q ∧
    canonicalSwitchB rep7D 6=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_b ∧ canonicalSwitchD2 rep7D 6=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_d2 ∧
    canonicalSwitchD1 rep7D 6=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_d1 := by
  have hc : cycleEdge 6 = ({(6 : Fin 11),(7 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(6 : Fin 11),(7 : Fin 11)} : Finset (Fin 11)) = 192 := by decide
  have hpred : (((6 : Fin 9) - 1 : Fin 9) : ℕ) = 5 := by decide
  have hj : ((6 : Fin 9) : ℕ) = 6 := rfl
  have hne : (6 : Fin 11) ≠ (7 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_d1]

/-- G2 coefficient identity: canonical switch 7 of rep7 = batch switch 8. -/
theorem rep7_switch7_eq :
    canonicalSwitchP rep7D rep7Kap 7=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_p ∧ canonicalSwitchQ rep7D 7=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_q ∧
    canonicalSwitchB rep7D 7=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_b ∧ canonicalSwitchD2 rep7D 7=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_d2 ∧
    canonicalSwitchD1 rep7D 7=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_d1 := by
  have hc : cycleEdge 7 = ({(7 : Fin 11),(8 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(7 : Fin 11),(8 : Fin 11)} : Finset (Fin 11)) = 384 := by decide
  have hpred : (((7 : Fin 9) - 1 : Fin 9) : ℕ) = 6 := by decide
  have hj : ((7 : Fin 9) : ℕ) = 7 := rfl
  have hne : (7 : Fin 11) ≠ (8 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_d1]

/-- G2 coefficient identity: canonical switch 8 of rep7 = batch switch 0. -/
theorem rep7_switch8_eq :
    canonicalSwitchP rep7D rep7Kap 8=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_p ∧ canonicalSwitchQ rep7D 8=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_q ∧
    canonicalSwitchB rep7D 8=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_b ∧ canonicalSwitchD2 rep7D 8=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_d2 ∧
    canonicalSwitchD1 rep7D 8=N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_d1 := by
  have hc : cycleEdge 8 = ({(8 : Fin 11),(0 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(8 : Fin 11),(0 : Fin 11)} : Finset (Fin 11)) = 257 := by decide
  have hpred : (((8 : Fin 9) - 1 : Fin 9) : ℕ) = 7 := by decide
  have hj : ((8 : Fin 9) : ℕ) = 8 := rfl
  have hne : (8 : Fin 11) ≠ (0 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep7D,rep7Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep7MuN,rep7SideFirstCode,rep7SideSecondCode,rep7KapCode,rep7LeftFirstN,rep7LeftSecondN,
      rep7RightFirstN,rep7RightSecondN,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_p,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_q,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_b,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_d2,N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_d1]

theorem sc_cast_aux {P P' Q Q' B B' D2 D2' D1 D1' M M' : ℚ}
    (h1 : P = P') (h2 : Q = Q') (h3 : B = B') (h4 : D2 = D2') (h5 : D1 = D1') (hm : M = M')
    (s : SwitchCertificate P' Q' B' D2' D1' M') : SwitchCertificate P Q B D2 D1 M := by
  subst h1 h2 h3 h4 h5 hm
  exact s

/-- The `switches` field of a `FiniteCanonicalCertificate rep7D rep7Kap 0 rep7Eta sharpAlpha`. -/
def rep7Switches : ∀ i : Fin 9, SwitchCertificate (canonicalSwitchP rep7D rep7Kap i)
    (canonicalSwitchQ rep7D i) (canonicalSwitchB rep7D i) (canonicalSwitchD2 rep7D i)
    (canonicalSwitchD1 rep7D i) (rep7SwitchMax i)
  := fun i => match i with
  | ⟨0, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch0_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨0, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch1_bound) batchSwitch1
  | ⟨1, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch1_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨1, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch2_bound) batchSwitch2
  | ⟨2, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch2_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨2, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch3_bound) batchSwitch3
  | ⟨3, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch3_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨3, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch4_bound) batchSwitch4
  | ⟨4, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch4_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨4, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch5_bound) batchSwitch5
  | ⟨5, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch5_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨5, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch6_bound) batchSwitch6
  | ⟨6, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch6_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨6, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch7_bound) batchSwitch7
  | ⟨7, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch7_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨7, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch8_bound) batchSwitch8
  | ⟨8, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep7_switch8_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by exact rfl : rep7SwitchMax (⟨8, by decide⟩ : Fin 9) = N11Formalization.SharedMomentConcreteSwitchBatch.start0_switch0_bound) batchSwitch0
  | ⟨n+9, h⟩ => absurd h (by omega)
end N11Formalization.Class33SwitchBridge
#print axioms N11Formalization.Class33SwitchBridge.certificate_mono
#print axioms N11Formalization.Class33SwitchBridge.switchCertificate_of_direct
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch_aggregate
#print axioms N11Formalization.Class33SwitchBridge.rep7Switches
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch0_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch1_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch2_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch3_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch4_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch5_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch6_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch7_eq
#print axioms N11Formalization.Class33SwitchBridge.rep7_switch8_eq
