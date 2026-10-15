import N11Formalization.Class33SwitchFields
import N11Formalization.Class33Labels
import N11Formalization.CanonicalBalancedFiniteClassCertificate
import N11Formalization.Class33FaceTreeQ0M2F0_1_9
import N11Formalization.Class33FaceTreeQ0M2F0_8_10
import N11Formalization.Class33FaceTreeQ0M2F0_9_10
import N11Formalization.Class33FaceTreeQ0M2F1_2_9
import N11Formalization.Class33FaceTreeQ0M2F2_3_10
import N11Formalization.Class33FaceTreeQ0M2F2_9_10
import N11Formalization.Class33FaceTreeQ0M2F3_4_10
import N11Formalization.Class33FaceTreeQ0M2F4_5_10
import N11Formalization.Class33FaceTreeQ0M2F5_6_10
import N11Formalization.Class33FaceTreeQ0M2F6_7_10
import N11Formalization.Class33FaceTreeQ0M2F7_8_10

/-! Class33 DRAFT (uncompiled): class q0_degree4 (q0Faces 2, hub degrees (4,9)).
Faces: 11 plane trees (Class33FaceTreeQ0M2F*); switches: `q0m2Switches`.
`q0m2_table_of_sectors` reduces `Q0FiniteTable 2` to the 9 sector certificates and the strict total. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33Q0M2Assembly
open CanonicalSharedMomentFiniteCertificate ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport
open ActualOrderedMetricGraphs ActualCanonicalFaceCoordinates SharedMomentFiniteFactorCertificate
open SharedMomentEfficientFactorCertificate Class33RepData Class33SwitchBridge Class33Labels
open Class33SwitchFields

theorem q0m2_face_cases : ∀ f ∈ q0Faces 2, f = ({0,1,9} : Finset (Fin 11)) ∨ f = ({0,8,10} : Finset (Fin 11)) ∨ f = ({0,9,10} : Finset (Fin 11)) ∨ f = ({1,2,9} : Finset (Fin 11)) ∨ f = ({2,3,10} : Finset (Fin 11)) ∨ f = ({2,9,10} : Finset (Fin 11)) ∨ f = ({3,4,10} : Finset (Fin 11)) ∨ f = ({4,5,10} : Finset (Fin 11)) ∨ f = ({5,6,10} : Finset (Fin 11)) ∨ f = ({6,7,10} : Finset (Fin 11)) ∨ f = ({7,8,10} : Finset (Fin 11)) := by
  decide
def q0m2FaceMaxCode : ℕ → ℚ
  | 515 => N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_bound
  | 1281 => N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_bound
  | 1537 => N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_bound
  | 518 => N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_bound
  | 1036 => N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_bound
  | 1540 => N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_bound
  | 1048 => N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_bound
  | 1072 => N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_bound
  | 1120 => N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_bound
  | 1216 => N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_bound
  | 1408 => N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_bound
  | _ => 0
def q0m2FaceMax (f : q0Faces 2) : ℚ := q0m2FaceMaxCode (edgeCode f.val)

theorem face0_1_9_coeff (h : ({0,1,9} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({0,1,9} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({0,1,9} : Finset (Fin 11)) h3 0 = 0 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({0,1,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({0,1,9} : Finset (Fin 11)) h3 1 = 1 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({0,1,9} : Finset (Fin 11)).erase 0) = 514 := by decide
  have e1 : edgeCode (({0,1,9} : Finset (Fin 11)).erase 1) = 513 := by decide
  have e2 : edgeCode (({0,1,9} : Finset (Fin 11)).erase 9) = 3 := by decide
  have c3 : edgeCode ({0,1,9} : Finset (Fin 11)) = 515 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F0_1_9.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face0_8_10_coeff (h : ({0,8,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({0,8,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({0,8,10} : Finset (Fin 11)) h3 0 = 0 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({0,8,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({0,8,10} : Finset (Fin 11)) h3 1 = 8 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({0,8,10} : Finset (Fin 11)).erase 0) = 1280 := by decide
  have e1 : edgeCode (({0,8,10} : Finset (Fin 11)).erase 8) = 1025 := by decide
  have e2 : edgeCode (({0,8,10} : Finset (Fin 11)).erase 10) = 257 := by decide
  have c3 : edgeCode ({0,8,10} : Finset (Fin 11)) = 1281 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F0_8_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face0_9_10_coeff (h : ({0,9,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({0,9,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({0,9,10} : Finset (Fin 11)) h3 0 = 0 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({0,9,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({0,9,10} : Finset (Fin 11)) h3 1 = 9 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({0,9,10} : Finset (Fin 11)).erase 0) = 1536 := by decide
  have e1 : edgeCode (({0,9,10} : Finset (Fin 11)).erase 9) = 1025 := by decide
  have e2 : edgeCode (({0,9,10} : Finset (Fin 11)).erase 10) = 513 := by decide
  have c3 : edgeCode ({0,9,10} : Finset (Fin 11)) = 1537 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F0_9_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face1_2_9_coeff (h : ({1,2,9} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({1,2,9} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({1,2,9} : Finset (Fin 11)) h3 0 = 1 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({1,2,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({1,2,9} : Finset (Fin 11)) h3 1 = 2 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({1,2,9} : Finset (Fin 11)).erase 1) = 516 := by decide
  have e1 : edgeCode (({1,2,9} : Finset (Fin 11)).erase 2) = 514 := by decide
  have e2 : edgeCode (({1,2,9} : Finset (Fin 11)).erase 9) = 6 := by decide
  have c3 : edgeCode ({1,2,9} : Finset (Fin 11)) = 518 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F1_2_9.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face2_3_10_coeff (h : ({2,3,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({2,3,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({2,3,10} : Finset (Fin 11)) h3 0 = 2 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({2,3,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({2,3,10} : Finset (Fin 11)) h3 1 = 3 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({2,3,10} : Finset (Fin 11)).erase 2) = 1032 := by decide
  have e1 : edgeCode (({2,3,10} : Finset (Fin 11)).erase 3) = 1028 := by decide
  have e2 : edgeCode (({2,3,10} : Finset (Fin 11)).erase 10) = 12 := by decide
  have c3 : edgeCode ({2,3,10} : Finset (Fin 11)) = 1036 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F2_3_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face2_9_10_coeff (h : ({2,9,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({2,9,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({2,9,10} : Finset (Fin 11)) h3 0 = 2 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({2,9,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({2,9,10} : Finset (Fin 11)) h3 1 = 9 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({2,9,10} : Finset (Fin 11)).erase 2) = 1536 := by decide
  have e1 : edgeCode (({2,9,10} : Finset (Fin 11)).erase 9) = 1028 := by decide
  have e2 : edgeCode (({2,9,10} : Finset (Fin 11)).erase 10) = 516 := by decide
  have c3 : edgeCode ({2,9,10} : Finset (Fin 11)) = 1540 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F2_9_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face3_4_10_coeff (h : ({3,4,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({3,4,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({3,4,10} : Finset (Fin 11)) h3 0 = 3 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({3,4,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({3,4,10} : Finset (Fin 11)) h3 1 = 4 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({3,4,10} : Finset (Fin 11)).erase 3) = 1040 := by decide
  have e1 : edgeCode (({3,4,10} : Finset (Fin 11)).erase 4) = 1032 := by decide
  have e2 : edgeCode (({3,4,10} : Finset (Fin 11)).erase 10) = 24 := by decide
  have c3 : edgeCode ({3,4,10} : Finset (Fin 11)) = 1048 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F3_4_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face4_5_10_coeff (h : ({4,5,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({4,5,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({4,5,10} : Finset (Fin 11)) h3 0 = 4 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({4,5,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({4,5,10} : Finset (Fin 11)) h3 1 = 5 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({4,5,10} : Finset (Fin 11)).erase 4) = 1056 := by decide
  have e1 : edgeCode (({4,5,10} : Finset (Fin 11)).erase 5) = 1040 := by decide
  have e2 : edgeCode (({4,5,10} : Finset (Fin 11)).erase 10) = 48 := by decide
  have c3 : edgeCode ({4,5,10} : Finset (Fin 11)) = 1072 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F4_5_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face5_6_10_coeff (h : ({5,6,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({5,6,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({5,6,10} : Finset (Fin 11)) h3 0 = 5 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({5,6,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({5,6,10} : Finset (Fin 11)) h3 1 = 6 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({5,6,10} : Finset (Fin 11)).erase 5) = 1088 := by decide
  have e1 : edgeCode (({5,6,10} : Finset (Fin 11)).erase 6) = 1056 := by decide
  have e2 : edgeCode (({5,6,10} : Finset (Fin 11)).erase 10) = 96 := by decide
  have c3 : edgeCode ({5,6,10} : Finset (Fin 11)) = 1120 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F5_6_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face6_7_10_coeff (h : ({6,7,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({6,7,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({6,7,10} : Finset (Fin 11)) h3 0 = 6 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({6,7,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({6,7,10} : Finset (Fin 11)) h3 1 = 7 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({6,7,10} : Finset (Fin 11)).erase 6) = 1152 := by decide
  have e1 : edgeCode (({6,7,10} : Finset (Fin 11)).erase 7) = 1088 := by decide
  have e2 : edgeCode (({6,7,10} : Finset (Fin 11)).erase 10) = 192 := by decide
  have c3 : edgeCode ({6,7,10} : Finset (Fin 11)) = 1216 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F6_7_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

theorem face7_8_10_coeff (h : ({7,8,10} : Finset (Fin 11)) ∈ q0Faces 2) :
    canonicalFaceP q0m2D q0m2Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_p ∧ canonicalFaceQ q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_q ∧
    canonicalFaceB q0m2D ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_b ∧ q0m2FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_bound := by
  have h3 := q0FaceCard 2 ⟨({7,8,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({7,8,10} : Finset (Fin 11)) h3 0 = 7 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({7,8,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({7,8,10} : Finset (Fin 11)) h3 1 = 8 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({7,8,10} : Finset (Fin 11)).erase 7) = 1280 := by decide
  have e1 : edgeCode (({7,8,10} : Finset (Fin 11)).erase 8) = 1152 := by decide
  have e2 : edgeCode (({7,8,10} : Finset (Fin 11)).erase 10) = 384 := by decide
  have c3 : edgeCode ({7,8,10} : Finset (Fin 11)) = 1408 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,q0m2Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MuN,q0m2KapCode,N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideSecondCode,N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,q0m2D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [q0m2MaskCode,q0m2MinusPairs,q0m2SideFirstCode,N11Formalization.Class33FaceTreeQ0M2F7_8_10.fc_b]
  · simp only [q0m2FaceMax,c3,q0m2FaceMaxCode]

/-- The `faces` field. -/
def q0m2Faces : ∀ f : q0Faces 2, EfficientFaceCertificate (canonicalFaceP q0m2D q0m2Kap f)
    (canonicalFaceQ q0m2D f) (canonicalFaceB q0m2D f) (q0m2FaceMax f) := by
  rintro ⟨f,hf⟩
  rcases q0m2_face_cases f hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1,h2,h3,h4⟩ := face0_1_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F0_1_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face0_8_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F0_8_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face0_9_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F0_9_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face1_2_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F1_2_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face2_3_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F2_3_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face2_9_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F2_9_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face3_4_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F3_4_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face4_5_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F4_5_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face5_6_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F5_6_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face6_7_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F6_7_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face7_8_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeQ0M2F7_8_10.certificate

/-- Reduction of `Q0FiniteTable 2` to its nine sector certificates and the strict total. -/
theorem q0m2_table_of_sectors (sectorMax : Fin 9 → ℚ)
    (hsector : ∀ i : Fin 9, EfficientSectorCertificate (canonicalSectorC q0m2D 0 0 i)
      (q0m2D.mu (ActualRingLinkBoundaryData.nextSite i)) (q0m2D.leftSecond i) (q0m2D.rightSecond i)
      (q0m2D.leftFirst i) (q0m2D.rightFirst i) (sectorMax i))
    (hstrict : canonicalTotalUpperQ q0m2D q0m2Kap 0 sharpAlpha q0m2FaceMax q0m2SwitchMax sectorMax <
      RatInterval.piLo) : Q0FiniteTable 2 :=
  ⟨q0m2D,q0m2Kap,⟨{ faceMax := q0m2FaceMax
      switchMax := q0m2SwitchMax
      sectorMax := sectorMax
      balance := q0m2_balance
      edge_nonnegative := q0m2_kap_nonneg
      eta_nonnegative := le_refl 0
      bracket := sharpAlpha_bracket
      faces := q0m2Faces
      switches := q0m2Switches
      sectors := hsector
      strict := hstrict }⟩⟩

end N11Formalization.Class33Q0M2Assembly
#print axioms N11Formalization.Class33Q0M2Assembly.q0m2Faces
#print axioms N11Formalization.Class33Q0M2Assembly.q0m2_table_of_sectors
