import N11Formalization.Class33SwitchBridge
import N11Formalization.Class33SwitchTreeRep1S0
import N11Formalization.Class33SwitchTreeRep1S1
import N11Formalization.Class33SwitchTreeRep1S2
import N11Formalization.Class33SwitchTreeRep1S3
import N11Formalization.Class33SwitchTreeRep1S4
import N11Formalization.Class33SwitchTreeRep1S5
import N11Formalization.Class33SwitchTreeRep1S6
import N11Formalization.Class33SwitchTreeRep1S7
import N11Formalization.Class33SwitchTreeRep1S8
import N11Formalization.Class33SwitchTreeQ0M2S0
import N11Formalization.Class33SwitchTreeQ0M2S1
import N11Formalization.Class33SwitchTreeQ0M2S2
import N11Formalization.Class33SwitchTreeQ0M2S3
import N11Formalization.Class33SwitchTreeQ0M2S4
import N11Formalization.Class33SwitchTreeQ0M2S5
import N11Formalization.Class33SwitchTreeQ0M2S6
import N11Formalization.Class33SwitchTreeQ0M2S7
import N11Formalization.Class33SwitchTreeQ0M2S8

/-! Class33 DRAFT (uncompiled): `switches` fields and switch maxima for rep1 and q0m2. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33SwitchFields
open RationalBoxSubdivision SharedMomentFiniteFactorCertificate ActualCanonicalMomentTransport
open ActualEdgeFlagSums Class33RepData Class33SwitchBridge ActualRingDirectionOrder ActualRingLinkBoundaryData

def rep1SwitchMaxN : ℕ → ℚ
  | 0 => (3/50000 : ℚ)
  | 1 => (5309/25000 : ℚ)
  | 2 => (30833/125000 : ℚ)
  | 3 => (3/50000 : ℚ)
  | 4 => (1007/500000 : ℚ)
  | 5 => (275777/1000000 : ℚ)
  | 6 => (132957/500000 : ℚ)
  | 7 => (12301/1000000 : ℚ)
  | 8 => (3/50000 : ℚ)
  | _ => 0
def rep1SwitchMax (i : Fin 9) : ℚ := rep1SwitchMaxN i.val
theorem rep1_switch_aggregate : (∑ i : Fin 9, rep1SwitchMax i) = (101521/100000 : ℚ) := by
  show (∑ i : Fin 9, rep1SwitchMaxN i.val) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.isValue, rep1SwitchMaxN]
  norm_num

theorem rep1_switch0_eq :
    canonicalSwitchP rep1D rep1Kap 0=N11Formalization.Class33SwitchTreeRep1S0.sw_p ∧ canonicalSwitchQ rep1D 0=N11Formalization.Class33SwitchTreeRep1S0.sw_q ∧
    canonicalSwitchB rep1D 0=N11Formalization.Class33SwitchTreeRep1S0.sw_b ∧ canonicalSwitchD2 rep1D 0=N11Formalization.Class33SwitchTreeRep1S0.sw_d2 ∧
    canonicalSwitchD1 rep1D 0=N11Formalization.Class33SwitchTreeRep1S0.sw_d1 := by
  have hc : cycleEdge 0 = ({(0 : Fin 11),(1 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(0 : Fin 11),(1 : Fin 11)} : Finset (Fin 11)) = 3 := by decide
  have hpred : (((0 : Fin 9) - 1 : Fin 9) : ℕ) = 8 := by decide
  have hj : ((0 : Fin 9) : ℕ) = 0 := rfl
  have hne : (0 : Fin 11) ≠ (1 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S0.sw_p,N11Formalization.Class33SwitchTreeRep1S0.sw_q,N11Formalization.Class33SwitchTreeRep1S0.sw_b,N11Formalization.Class33SwitchTreeRep1S0.sw_d2,N11Formalization.Class33SwitchTreeRep1S0.sw_d1]

theorem rep1_switch1_eq :
    canonicalSwitchP rep1D rep1Kap 1=N11Formalization.Class33SwitchTreeRep1S1.sw_p ∧ canonicalSwitchQ rep1D 1=N11Formalization.Class33SwitchTreeRep1S1.sw_q ∧
    canonicalSwitchB rep1D 1=N11Formalization.Class33SwitchTreeRep1S1.sw_b ∧ canonicalSwitchD2 rep1D 1=N11Formalization.Class33SwitchTreeRep1S1.sw_d2 ∧
    canonicalSwitchD1 rep1D 1=N11Formalization.Class33SwitchTreeRep1S1.sw_d1 := by
  have hc : cycleEdge 1 = ({(1 : Fin 11),(2 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(1 : Fin 11),(2 : Fin 11)} : Finset (Fin 11)) = 6 := by decide
  have hpred : (((1 : Fin 9) - 1 : Fin 9) : ℕ) = 0 := by decide
  have hj : ((1 : Fin 9) : ℕ) = 1 := rfl
  have hne : (1 : Fin 11) ≠ (2 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S1.sw_p,N11Formalization.Class33SwitchTreeRep1S1.sw_q,N11Formalization.Class33SwitchTreeRep1S1.sw_b,N11Formalization.Class33SwitchTreeRep1S1.sw_d2,N11Formalization.Class33SwitchTreeRep1S1.sw_d1]

theorem rep1_switch2_eq :
    canonicalSwitchP rep1D rep1Kap 2=N11Formalization.Class33SwitchTreeRep1S2.sw_p ∧ canonicalSwitchQ rep1D 2=N11Formalization.Class33SwitchTreeRep1S2.sw_q ∧
    canonicalSwitchB rep1D 2=N11Formalization.Class33SwitchTreeRep1S2.sw_b ∧ canonicalSwitchD2 rep1D 2=N11Formalization.Class33SwitchTreeRep1S2.sw_d2 ∧
    canonicalSwitchD1 rep1D 2=N11Formalization.Class33SwitchTreeRep1S2.sw_d1 := by
  have hc : cycleEdge 2 = ({(2 : Fin 11),(3 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(2 : Fin 11),(3 : Fin 11)} : Finset (Fin 11)) = 12 := by decide
  have hpred : (((2 : Fin 9) - 1 : Fin 9) : ℕ) = 1 := by decide
  have hj : ((2 : Fin 9) : ℕ) = 2 := rfl
  have hne : (2 : Fin 11) ≠ (3 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S2.sw_p,N11Formalization.Class33SwitchTreeRep1S2.sw_q,N11Formalization.Class33SwitchTreeRep1S2.sw_b,N11Formalization.Class33SwitchTreeRep1S2.sw_d2,N11Formalization.Class33SwitchTreeRep1S2.sw_d1]

theorem rep1_switch3_eq :
    canonicalSwitchP rep1D rep1Kap 3=N11Formalization.Class33SwitchTreeRep1S3.sw_p ∧ canonicalSwitchQ rep1D 3=N11Formalization.Class33SwitchTreeRep1S3.sw_q ∧
    canonicalSwitchB rep1D 3=N11Formalization.Class33SwitchTreeRep1S3.sw_b ∧ canonicalSwitchD2 rep1D 3=N11Formalization.Class33SwitchTreeRep1S3.sw_d2 ∧
    canonicalSwitchD1 rep1D 3=N11Formalization.Class33SwitchTreeRep1S3.sw_d1 := by
  have hc : cycleEdge 3 = ({(3 : Fin 11),(4 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(3 : Fin 11),(4 : Fin 11)} : Finset (Fin 11)) = 24 := by decide
  have hpred : (((3 : Fin 9) - 1 : Fin 9) : ℕ) = 2 := by decide
  have hj : ((3 : Fin 9) : ℕ) = 3 := rfl
  have hne : (3 : Fin 11) ≠ (4 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S3.sw_p,N11Formalization.Class33SwitchTreeRep1S3.sw_q,N11Formalization.Class33SwitchTreeRep1S3.sw_b,N11Formalization.Class33SwitchTreeRep1S3.sw_d2,N11Formalization.Class33SwitchTreeRep1S3.sw_d1]

theorem rep1_switch4_eq :
    canonicalSwitchP rep1D rep1Kap 4=N11Formalization.Class33SwitchTreeRep1S4.sw_p ∧ canonicalSwitchQ rep1D 4=N11Formalization.Class33SwitchTreeRep1S4.sw_q ∧
    canonicalSwitchB rep1D 4=N11Formalization.Class33SwitchTreeRep1S4.sw_b ∧ canonicalSwitchD2 rep1D 4=N11Formalization.Class33SwitchTreeRep1S4.sw_d2 ∧
    canonicalSwitchD1 rep1D 4=N11Formalization.Class33SwitchTreeRep1S4.sw_d1 := by
  have hc : cycleEdge 4 = ({(4 : Fin 11),(5 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(4 : Fin 11),(5 : Fin 11)} : Finset (Fin 11)) = 48 := by decide
  have hpred : (((4 : Fin 9) - 1 : Fin 9) : ℕ) = 3 := by decide
  have hj : ((4 : Fin 9) : ℕ) = 4 := rfl
  have hne : (4 : Fin 11) ≠ (5 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S4.sw_p,N11Formalization.Class33SwitchTreeRep1S4.sw_q,N11Formalization.Class33SwitchTreeRep1S4.sw_b,N11Formalization.Class33SwitchTreeRep1S4.sw_d2,N11Formalization.Class33SwitchTreeRep1S4.sw_d1]

theorem rep1_switch5_eq :
    canonicalSwitchP rep1D rep1Kap 5=N11Formalization.Class33SwitchTreeRep1S5.sw_p ∧ canonicalSwitchQ rep1D 5=N11Formalization.Class33SwitchTreeRep1S5.sw_q ∧
    canonicalSwitchB rep1D 5=N11Formalization.Class33SwitchTreeRep1S5.sw_b ∧ canonicalSwitchD2 rep1D 5=N11Formalization.Class33SwitchTreeRep1S5.sw_d2 ∧
    canonicalSwitchD1 rep1D 5=N11Formalization.Class33SwitchTreeRep1S5.sw_d1 := by
  have hc : cycleEdge 5 = ({(5 : Fin 11),(6 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(5 : Fin 11),(6 : Fin 11)} : Finset (Fin 11)) = 96 := by decide
  have hpred : (((5 : Fin 9) - 1 : Fin 9) : ℕ) = 4 := by decide
  have hj : ((5 : Fin 9) : ℕ) = 5 := rfl
  have hne : (5 : Fin 11) ≠ (6 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S5.sw_p,N11Formalization.Class33SwitchTreeRep1S5.sw_q,N11Formalization.Class33SwitchTreeRep1S5.sw_b,N11Formalization.Class33SwitchTreeRep1S5.sw_d2,N11Formalization.Class33SwitchTreeRep1S5.sw_d1]

theorem rep1_switch6_eq :
    canonicalSwitchP rep1D rep1Kap 6=N11Formalization.Class33SwitchTreeRep1S6.sw_p ∧ canonicalSwitchQ rep1D 6=N11Formalization.Class33SwitchTreeRep1S6.sw_q ∧
    canonicalSwitchB rep1D 6=N11Formalization.Class33SwitchTreeRep1S6.sw_b ∧ canonicalSwitchD2 rep1D 6=N11Formalization.Class33SwitchTreeRep1S6.sw_d2 ∧
    canonicalSwitchD1 rep1D 6=N11Formalization.Class33SwitchTreeRep1S6.sw_d1 := by
  have hc : cycleEdge 6 = ({(6 : Fin 11),(7 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(6 : Fin 11),(7 : Fin 11)} : Finset (Fin 11)) = 192 := by decide
  have hpred : (((6 : Fin 9) - 1 : Fin 9) : ℕ) = 5 := by decide
  have hj : ((6 : Fin 9) : ℕ) = 6 := rfl
  have hne : (6 : Fin 11) ≠ (7 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S6.sw_p,N11Formalization.Class33SwitchTreeRep1S6.sw_q,N11Formalization.Class33SwitchTreeRep1S6.sw_b,N11Formalization.Class33SwitchTreeRep1S6.sw_d2,N11Formalization.Class33SwitchTreeRep1S6.sw_d1]

theorem rep1_switch7_eq :
    canonicalSwitchP rep1D rep1Kap 7=N11Formalization.Class33SwitchTreeRep1S7.sw_p ∧ canonicalSwitchQ rep1D 7=N11Formalization.Class33SwitchTreeRep1S7.sw_q ∧
    canonicalSwitchB rep1D 7=N11Formalization.Class33SwitchTreeRep1S7.sw_b ∧ canonicalSwitchD2 rep1D 7=N11Formalization.Class33SwitchTreeRep1S7.sw_d2 ∧
    canonicalSwitchD1 rep1D 7=N11Formalization.Class33SwitchTreeRep1S7.sw_d1 := by
  have hc : cycleEdge 7 = ({(7 : Fin 11),(8 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(7 : Fin 11),(8 : Fin 11)} : Finset (Fin 11)) = 384 := by decide
  have hpred : (((7 : Fin 9) - 1 : Fin 9) : ℕ) = 6 := by decide
  have hj : ((7 : Fin 9) : ℕ) = 7 := rfl
  have hne : (7 : Fin 11) ≠ (8 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S7.sw_p,N11Formalization.Class33SwitchTreeRep1S7.sw_q,N11Formalization.Class33SwitchTreeRep1S7.sw_b,N11Formalization.Class33SwitchTreeRep1S7.sw_d2,N11Formalization.Class33SwitchTreeRep1S7.sw_d1]

theorem rep1_switch8_eq :
    canonicalSwitchP rep1D rep1Kap 8=N11Formalization.Class33SwitchTreeRep1S8.sw_p ∧ canonicalSwitchQ rep1D 8=N11Formalization.Class33SwitchTreeRep1S8.sw_q ∧
    canonicalSwitchB rep1D 8=N11Formalization.Class33SwitchTreeRep1S8.sw_b ∧ canonicalSwitchD2 rep1D 8=N11Formalization.Class33SwitchTreeRep1S8.sw_d2 ∧
    canonicalSwitchD1 rep1D 8=N11Formalization.Class33SwitchTreeRep1S8.sw_d1 := by
  have hc : cycleEdge 8 = ({(8 : Fin 11),(0 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(8 : Fin 11),(0 : Fin 11)} : Finset (Fin 11)) = 257 := by decide
  have hpred : (((8 : Fin 9) - 1 : Fin 9) : ℕ) = 7 := by decide
  have hj : ((8 : Fin 9) : ℕ) = 8 := rfl
  have hne : (8 : Fin 11) ≠ (0 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      rep1D,rep1Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [rep1MuN,rep1SideFirstCode,rep1SideSecondCode,rep1KapCode,rep1LeftFirstN,rep1LeftSecondN,
      rep1RightFirstN,rep1RightSecondN,N11Formalization.Class33SwitchTreeRep1S8.sw_p,N11Formalization.Class33SwitchTreeRep1S8.sw_q,N11Formalization.Class33SwitchTreeRep1S8.sw_b,N11Formalization.Class33SwitchTreeRep1S8.sw_d2,N11Formalization.Class33SwitchTreeRep1S8.sw_d1]

def rep1Switches : ∀ i : Fin 9, SwitchCertificate (canonicalSwitchP rep1D rep1Kap i)
    (canonicalSwitchQ rep1D i) (canonicalSwitchB rep1D i) (canonicalSwitchD2 rep1D i)
    (canonicalSwitchD1 rep1D i) (rep1SwitchMax i) :=
  fun i => match i with
  | ⟨0, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch0_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S0.sw_bound] : rep1SwitchMax (⟨0, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S0.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S0.root)
  | ⟨1, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch1_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S1.sw_bound] : rep1SwitchMax (⟨1, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S1.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S1.root)
  | ⟨2, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch2_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S2.sw_bound] : rep1SwitchMax (⟨2, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S2.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S2.root)
  | ⟨3, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch3_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S3.sw_bound] : rep1SwitchMax (⟨3, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S3.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S3.root)
  | ⟨4, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch4_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S4.sw_bound] : rep1SwitchMax (⟨4, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S4.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S4.root)
  | ⟨5, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch5_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S5.sw_bound] : rep1SwitchMax (⟨5, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S5.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S5.root)
  | ⟨6, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch6_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S6.sw_bound] : rep1SwitchMax (⟨6, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S6.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S6.root)
  | ⟨7, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch7_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S7.sw_bound] : rep1SwitchMax (⟨7, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S7.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S7.root)
  | ⟨8, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := rep1_switch8_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [rep1SwitchMax,rep1SwitchMaxN,N11Formalization.Class33SwitchTreeRep1S8.sw_bound] : rep1SwitchMax (⟨8, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeRep1S8.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeRep1S8.root)
  | ⟨n+9, h⟩ => absurd h (by omega)

def q0m2SwitchMaxN : ℕ → ℚ
  | 0 => (84031/1000000 : ℚ)
  | 1 => (84031/1000000 : ℚ)
  | 2 => (11693/50000 : ℚ)
  | 3 => (6143/31250 : ℚ)
  | 4 => (24639/125000 : ℚ)
  | 5 => (104811/500000 : ℚ)
  | 6 => (24639/125000 : ℚ)
  | 7 => (6143/31250 : ℚ)
  | 8 => (11693/50000 : ℚ)
  | _ => 0
def q0m2SwitchMax (i : Fin 9) : ℚ := q0m2SwitchMaxN i.val
theorem q0m2_switch_aggregate : (∑ i : Fin 9, q0m2SwitchMax i) = (81639/50000 : ℚ) := by
  show (∑ i : Fin 9, q0m2SwitchMaxN i.val) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.isValue, q0m2SwitchMaxN]
  norm_num

theorem q0m2_switch0_eq :
    canonicalSwitchP q0m2D q0m2Kap 0=N11Formalization.Class33SwitchTreeQ0M2S0.sw_p ∧ canonicalSwitchQ q0m2D 0=N11Formalization.Class33SwitchTreeQ0M2S0.sw_q ∧
    canonicalSwitchB q0m2D 0=N11Formalization.Class33SwitchTreeQ0M2S0.sw_b ∧ canonicalSwitchD2 q0m2D 0=N11Formalization.Class33SwitchTreeQ0M2S0.sw_d2 ∧
    canonicalSwitchD1 q0m2D 0=N11Formalization.Class33SwitchTreeQ0M2S0.sw_d1 := by
  have hc : cycleEdge 0 = ({(0 : Fin 11),(1 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(0 : Fin 11),(1 : Fin 11)} : Finset (Fin 11)) = 3 := by decide
  have hpred : (((0 : Fin 9) - 1 : Fin 9) : ℕ) = 8 := by decide
  have hj : ((0 : Fin 9) : ℕ) = 0 := rfl
  have hne : (0 : Fin 11) ≠ (1 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S0.sw_p,N11Formalization.Class33SwitchTreeQ0M2S0.sw_q,N11Formalization.Class33SwitchTreeQ0M2S0.sw_b,N11Formalization.Class33SwitchTreeQ0M2S0.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S0.sw_d1]

theorem q0m2_switch1_eq :
    canonicalSwitchP q0m2D q0m2Kap 1=N11Formalization.Class33SwitchTreeQ0M2S1.sw_p ∧ canonicalSwitchQ q0m2D 1=N11Formalization.Class33SwitchTreeQ0M2S1.sw_q ∧
    canonicalSwitchB q0m2D 1=N11Formalization.Class33SwitchTreeQ0M2S1.sw_b ∧ canonicalSwitchD2 q0m2D 1=N11Formalization.Class33SwitchTreeQ0M2S1.sw_d2 ∧
    canonicalSwitchD1 q0m2D 1=N11Formalization.Class33SwitchTreeQ0M2S1.sw_d1 := by
  have hc : cycleEdge 1 = ({(1 : Fin 11),(2 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(1 : Fin 11),(2 : Fin 11)} : Finset (Fin 11)) = 6 := by decide
  have hpred : (((1 : Fin 9) - 1 : Fin 9) : ℕ) = 0 := by decide
  have hj : ((1 : Fin 9) : ℕ) = 1 := rfl
  have hne : (1 : Fin 11) ≠ (2 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S1.sw_p,N11Formalization.Class33SwitchTreeQ0M2S1.sw_q,N11Formalization.Class33SwitchTreeQ0M2S1.sw_b,N11Formalization.Class33SwitchTreeQ0M2S1.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S1.sw_d1]

theorem q0m2_switch2_eq :
    canonicalSwitchP q0m2D q0m2Kap 2=N11Formalization.Class33SwitchTreeQ0M2S2.sw_p ∧ canonicalSwitchQ q0m2D 2=N11Formalization.Class33SwitchTreeQ0M2S2.sw_q ∧
    canonicalSwitchB q0m2D 2=N11Formalization.Class33SwitchTreeQ0M2S2.sw_b ∧ canonicalSwitchD2 q0m2D 2=N11Formalization.Class33SwitchTreeQ0M2S2.sw_d2 ∧
    canonicalSwitchD1 q0m2D 2=N11Formalization.Class33SwitchTreeQ0M2S2.sw_d1 := by
  have hc : cycleEdge 2 = ({(2 : Fin 11),(3 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(2 : Fin 11),(3 : Fin 11)} : Finset (Fin 11)) = 12 := by decide
  have hpred : (((2 : Fin 9) - 1 : Fin 9) : ℕ) = 1 := by decide
  have hj : ((2 : Fin 9) : ℕ) = 2 := rfl
  have hne : (2 : Fin 11) ≠ (3 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S2.sw_p,N11Formalization.Class33SwitchTreeQ0M2S2.sw_q,N11Formalization.Class33SwitchTreeQ0M2S2.sw_b,N11Formalization.Class33SwitchTreeQ0M2S2.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S2.sw_d1]

theorem q0m2_switch3_eq :
    canonicalSwitchP q0m2D q0m2Kap 3=N11Formalization.Class33SwitchTreeQ0M2S3.sw_p ∧ canonicalSwitchQ q0m2D 3=N11Formalization.Class33SwitchTreeQ0M2S3.sw_q ∧
    canonicalSwitchB q0m2D 3=N11Formalization.Class33SwitchTreeQ0M2S3.sw_b ∧ canonicalSwitchD2 q0m2D 3=N11Formalization.Class33SwitchTreeQ0M2S3.sw_d2 ∧
    canonicalSwitchD1 q0m2D 3=N11Formalization.Class33SwitchTreeQ0M2S3.sw_d1 := by
  have hc : cycleEdge 3 = ({(3 : Fin 11),(4 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(3 : Fin 11),(4 : Fin 11)} : Finset (Fin 11)) = 24 := by decide
  have hpred : (((3 : Fin 9) - 1 : Fin 9) : ℕ) = 2 := by decide
  have hj : ((3 : Fin 9) : ℕ) = 3 := rfl
  have hne : (3 : Fin 11) ≠ (4 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S3.sw_p,N11Formalization.Class33SwitchTreeQ0M2S3.sw_q,N11Formalization.Class33SwitchTreeQ0M2S3.sw_b,N11Formalization.Class33SwitchTreeQ0M2S3.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S3.sw_d1]

theorem q0m2_switch4_eq :
    canonicalSwitchP q0m2D q0m2Kap 4=N11Formalization.Class33SwitchTreeQ0M2S4.sw_p ∧ canonicalSwitchQ q0m2D 4=N11Formalization.Class33SwitchTreeQ0M2S4.sw_q ∧
    canonicalSwitchB q0m2D 4=N11Formalization.Class33SwitchTreeQ0M2S4.sw_b ∧ canonicalSwitchD2 q0m2D 4=N11Formalization.Class33SwitchTreeQ0M2S4.sw_d2 ∧
    canonicalSwitchD1 q0m2D 4=N11Formalization.Class33SwitchTreeQ0M2S4.sw_d1 := by
  have hc : cycleEdge 4 = ({(4 : Fin 11),(5 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(4 : Fin 11),(5 : Fin 11)} : Finset (Fin 11)) = 48 := by decide
  have hpred : (((4 : Fin 9) - 1 : Fin 9) : ℕ) = 3 := by decide
  have hj : ((4 : Fin 9) : ℕ) = 4 := rfl
  have hne : (4 : Fin 11) ≠ (5 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S4.sw_p,N11Formalization.Class33SwitchTreeQ0M2S4.sw_q,N11Formalization.Class33SwitchTreeQ0M2S4.sw_b,N11Formalization.Class33SwitchTreeQ0M2S4.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S4.sw_d1]

theorem q0m2_switch5_eq :
    canonicalSwitchP q0m2D q0m2Kap 5=N11Formalization.Class33SwitchTreeQ0M2S5.sw_p ∧ canonicalSwitchQ q0m2D 5=N11Formalization.Class33SwitchTreeQ0M2S5.sw_q ∧
    canonicalSwitchB q0m2D 5=N11Formalization.Class33SwitchTreeQ0M2S5.sw_b ∧ canonicalSwitchD2 q0m2D 5=N11Formalization.Class33SwitchTreeQ0M2S5.sw_d2 ∧
    canonicalSwitchD1 q0m2D 5=N11Formalization.Class33SwitchTreeQ0M2S5.sw_d1 := by
  have hc : cycleEdge 5 = ({(5 : Fin 11),(6 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(5 : Fin 11),(6 : Fin 11)} : Finset (Fin 11)) = 96 := by decide
  have hpred : (((5 : Fin 9) - 1 : Fin 9) : ℕ) = 4 := by decide
  have hj : ((5 : Fin 9) : ℕ) = 5 := rfl
  have hne : (5 : Fin 11) ≠ (6 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S5.sw_p,N11Formalization.Class33SwitchTreeQ0M2S5.sw_q,N11Formalization.Class33SwitchTreeQ0M2S5.sw_b,N11Formalization.Class33SwitchTreeQ0M2S5.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S5.sw_d1]

theorem q0m2_switch6_eq :
    canonicalSwitchP q0m2D q0m2Kap 6=N11Formalization.Class33SwitchTreeQ0M2S6.sw_p ∧ canonicalSwitchQ q0m2D 6=N11Formalization.Class33SwitchTreeQ0M2S6.sw_q ∧
    canonicalSwitchB q0m2D 6=N11Formalization.Class33SwitchTreeQ0M2S6.sw_b ∧ canonicalSwitchD2 q0m2D 6=N11Formalization.Class33SwitchTreeQ0M2S6.sw_d2 ∧
    canonicalSwitchD1 q0m2D 6=N11Formalization.Class33SwitchTreeQ0M2S6.sw_d1 := by
  have hc : cycleEdge 6 = ({(6 : Fin 11),(7 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(6 : Fin 11),(7 : Fin 11)} : Finset (Fin 11)) = 192 := by decide
  have hpred : (((6 : Fin 9) - 1 : Fin 9) : ℕ) = 5 := by decide
  have hj : ((6 : Fin 9) : ℕ) = 6 := rfl
  have hne : (6 : Fin 11) ≠ (7 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S6.sw_p,N11Formalization.Class33SwitchTreeQ0M2S6.sw_q,N11Formalization.Class33SwitchTreeQ0M2S6.sw_b,N11Formalization.Class33SwitchTreeQ0M2S6.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S6.sw_d1]

theorem q0m2_switch7_eq :
    canonicalSwitchP q0m2D q0m2Kap 7=N11Formalization.Class33SwitchTreeQ0M2S7.sw_p ∧ canonicalSwitchQ q0m2D 7=N11Formalization.Class33SwitchTreeQ0M2S7.sw_q ∧
    canonicalSwitchB q0m2D 7=N11Formalization.Class33SwitchTreeQ0M2S7.sw_b ∧ canonicalSwitchD2 q0m2D 7=N11Formalization.Class33SwitchTreeQ0M2S7.sw_d2 ∧
    canonicalSwitchD1 q0m2D 7=N11Formalization.Class33SwitchTreeQ0M2S7.sw_d1 := by
  have hc : cycleEdge 7 = ({(7 : Fin 11),(8 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(7 : Fin 11),(8 : Fin 11)} : Finset (Fin 11)) = 384 := by decide
  have hpred : (((7 : Fin 9) - 1 : Fin 9) : ℕ) = 6 := by decide
  have hj : ((7 : Fin 9) : ℕ) = 7 := rfl
  have hne : (7 : Fin 11) ≠ (8 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S7.sw_p,N11Formalization.Class33SwitchTreeQ0M2S7.sw_q,N11Formalization.Class33SwitchTreeQ0M2S7.sw_b,N11Formalization.Class33SwitchTreeQ0M2S7.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S7.sw_d1]

theorem q0m2_switch8_eq :
    canonicalSwitchP q0m2D q0m2Kap 8=N11Formalization.Class33SwitchTreeQ0M2S8.sw_p ∧ canonicalSwitchQ q0m2D 8=N11Formalization.Class33SwitchTreeQ0M2S8.sw_q ∧
    canonicalSwitchB q0m2D 8=N11Formalization.Class33SwitchTreeQ0M2S8.sw_b ∧ canonicalSwitchD2 q0m2D 8=N11Formalization.Class33SwitchTreeQ0M2S8.sw_d2 ∧
    canonicalSwitchD1 q0m2D 8=N11Formalization.Class33SwitchTreeQ0M2S8.sw_d1 := by
  have hc : cycleEdge 8 = ({(8 : Fin 11),(0 : Fin 11)} : Finset (Fin 11)) := by decide
  have hcode : edgeCode ({(8 : Fin 11),(0 : Fin 11)} : Finset (Fin 11)) = 257 := by decide
  have hpred : (((8 : Fin 9) - 1 : Fin 9) : ℕ) = 7 := by decide
  have hj : ((8 : Fin 9) : ℕ) = 8 := rfl
  have hne : (8 : Fin 11) ≠ (0 : Fin 11) := by decide
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [canonicalSwitchP,canonicalSwitchQ,canonicalSwitchB,canonicalSwitchD2,canonicalSwitchD1,
      q0m2D,q0m2Kap,hc,hcode,hpred,hj,Finset.sum_pair hne] <;>
    norm_num [q0m2MuN,q0m2SideFirstCode,q0m2SideSecondCode,q0m2KapCode,q0m2LeftFirstN,q0m2LeftSecondN,
      q0m2RightFirstN,q0m2RightSecondN,N11Formalization.Class33SwitchTreeQ0M2S8.sw_p,N11Formalization.Class33SwitchTreeQ0M2S8.sw_q,N11Formalization.Class33SwitchTreeQ0M2S8.sw_b,N11Formalization.Class33SwitchTreeQ0M2S8.sw_d2,N11Formalization.Class33SwitchTreeQ0M2S8.sw_d1]

def q0m2Switches : ∀ i : Fin 9, SwitchCertificate (canonicalSwitchP q0m2D q0m2Kap i)
    (canonicalSwitchQ q0m2D i) (canonicalSwitchB q0m2D i) (canonicalSwitchD2 q0m2D i)
    (canonicalSwitchD1 q0m2D i) (q0m2SwitchMax i) :=
  fun i => match i with
  | ⟨0, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch0_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S0.sw_bound] : q0m2SwitchMax (⟨0, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S0.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S0.root)
  | ⟨1, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch1_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S1.sw_bound] : q0m2SwitchMax (⟨1, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S1.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S1.root)
  | ⟨2, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch2_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S2.sw_bound] : q0m2SwitchMax (⟨2, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S2.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S2.root)
  | ⟨3, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch3_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S3.sw_bound] : q0m2SwitchMax (⟨3, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S3.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S3.root)
  | ⟨4, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch4_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S4.sw_bound] : q0m2SwitchMax (⟨4, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S4.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S4.root)
  | ⟨5, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch5_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S5.sw_bound] : q0m2SwitchMax (⟨5, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S5.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S5.root)
  | ⟨6, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch6_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S6.sw_bound] : q0m2SwitchMax (⟨6, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S6.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S6.root)
  | ⟨7, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch7_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S7.sw_bound] : q0m2SwitchMax (⟨7, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S7.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S7.root)
  | ⟨8, _⟩ =>
    let ⟨h1,h2,h3,h4,h5⟩ := q0m2_switch8_eq
    sc_cast_aux h1 h2 h3 h4 h5 (by simp [q0m2SwitchMax,q0m2SwitchMaxN,N11Formalization.Class33SwitchTreeQ0M2S8.sw_bound] : q0m2SwitchMax (⟨8, by decide⟩ : Fin 9) = N11Formalization.Class33SwitchTreeQ0M2S8.sw_bound) (switchCertificate_of_direct N11Formalization.Class33SwitchTreeQ0M2S8.root)
  | ⟨n+9, h⟩ => absurd h (by omega)

end N11Formalization.Class33SwitchFields
#print axioms N11Formalization.Class33SwitchFields.rep1Switches
#print axioms N11Formalization.Class33SwitchFields.rep1_switch_aggregate
#print axioms N11Formalization.Class33SwitchFields.q0m2Switches
#print axioms N11Formalization.Class33SwitchFields.q0m2_switch_aggregate
