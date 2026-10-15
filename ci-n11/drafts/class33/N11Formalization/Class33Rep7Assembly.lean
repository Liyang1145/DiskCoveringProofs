import N11Formalization.Class33SwitchBridge
import N11Formalization.Class33Labels
import N11Formalization.CanonicalBalancedFiniteClassCertificate
import N11Formalization.Class33FaceTreeRep7F0_1_8
import N11Formalization.Class33FaceTreeRep7F1_2_9
import N11Formalization.Class33FaceTreeRep7F1_8_9
import N11Formalization.Class33FaceTreeRep7F2_3_9
import N11Formalization.Class33FaceTreeRep7F3_4_9
import N11Formalization.Class33FaceTreeRep7F4_5_10
import N11Formalization.Class33FaceTreeRep7F4_9_10
import N11Formalization.Class33FaceTreeRep7F5_6_10
import N11Formalization.Class33FaceTreeRep7F6_7_10
import N11Formalization.Class33FaceTreeRep7F7_8_10
import N11Formalization.Class33FaceTreeRep7F8_9_10

/-! Class33 DRAFT (uncompiled): q1-balanced representative cut 7 (q1Faces 7 4).
Faces: 11 plane trees (Class33FaceTreeRep7F*); switches: `rep7Switches`.
`rep7_table_of_sectors` reduces `CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 7` to the 9 sector certificates and the strict total. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33Rep7Assembly
open CanonicalSharedMomentFiniteCertificate ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport
open ActualOrderedMetricGraphs ActualCanonicalFaceCoordinates SharedMomentFiniteFactorCertificate
open SharedMomentEfficientFactorCertificate Class33RepData Class33SwitchBridge Class33Labels

theorem rep7_face_cases : ∀ f ∈ q1Faces 7 4, f = ({0,1,8} : Finset (Fin 11)) ∨ f = ({1,2,9} : Finset (Fin 11)) ∨ f = ({1,8,9} : Finset (Fin 11)) ∨ f = ({2,3,9} : Finset (Fin 11)) ∨ f = ({3,4,9} : Finset (Fin 11)) ∨ f = ({4,5,10} : Finset (Fin 11)) ∨ f = ({4,9,10} : Finset (Fin 11)) ∨ f = ({5,6,10} : Finset (Fin 11)) ∨ f = ({6,7,10} : Finset (Fin 11)) ∨ f = ({7,8,10} : Finset (Fin 11)) ∨ f = ({8,9,10} : Finset (Fin 11)) := by
  decide
def rep7FaceMaxCode : ℕ → ℚ
  | 259 => N11Formalization.Class33FaceTreeRep7F0_1_8.fc_bound
  | 518 => N11Formalization.Class33FaceTreeRep7F1_2_9.fc_bound
  | 770 => N11Formalization.Class33FaceTreeRep7F1_8_9.fc_bound
  | 524 => N11Formalization.Class33FaceTreeRep7F2_3_9.fc_bound
  | 536 => N11Formalization.Class33FaceTreeRep7F3_4_9.fc_bound
  | 1072 => N11Formalization.Class33FaceTreeRep7F4_5_10.fc_bound
  | 1552 => N11Formalization.Class33FaceTreeRep7F4_9_10.fc_bound
  | 1120 => N11Formalization.Class33FaceTreeRep7F5_6_10.fc_bound
  | 1216 => N11Formalization.Class33FaceTreeRep7F6_7_10.fc_bound
  | 1408 => N11Formalization.Class33FaceTreeRep7F7_8_10.fc_bound
  | 1792 => N11Formalization.Class33FaceTreeRep7F8_9_10.fc_bound
  | _ => 0
def rep7FaceMax (f : q1Faces 7 4) : ℚ := rep7FaceMaxCode (edgeCode f.val)

theorem face0_1_8_coeff (h : ({0,1,8} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F0_1_8.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F0_1_8.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F0_1_8.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F0_1_8.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({0,1,8} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({0,1,8} : Finset (Fin 11)) h3 0 = 0 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({0,1,8} : Finset (Fin 11)) h3 2 = 8 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({0,1,8} : Finset (Fin 11)) h3 1 = 1 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({0,1,8} : Finset (Fin 11)).erase 0) = 258 := by decide
  have e1 : edgeCode (({0,1,8} : Finset (Fin 11)).erase 1) = 257 := by decide
  have e2 : edgeCode (({0,1,8} : Finset (Fin 11)).erase 8) = 3 := by decide
  have c3 : edgeCode ({0,1,8} : Finset (Fin 11)) = 259 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F0_1_8.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F0_1_8.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F0_1_8.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face1_2_9_coeff (h : ({1,2,9} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_2_9.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_2_9.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_2_9.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_2_9.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({1,2,9} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F1_2_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F1_2_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F1_2_9.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face1_8_9_coeff (h : ({1,8,9} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_8_9.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_8_9.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_8_9.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F1_8_9.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({1,8,9} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 0 = 1 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 1 = 8 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 1) = 768 := by decide
  have e1 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 8) = 514 := by decide
  have e2 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 9) = 258 := by decide
  have c3 : edgeCode ({1,8,9} : Finset (Fin 11)) = 770 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F1_8_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F1_8_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F1_8_9.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face2_3_9_coeff (h : ({2,3,9} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F2_3_9.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F2_3_9.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F2_3_9.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F2_3_9.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({2,3,9} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({2,3,9} : Finset (Fin 11)) h3 0 = 2 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({2,3,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({2,3,9} : Finset (Fin 11)) h3 1 = 3 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({2,3,9} : Finset (Fin 11)).erase 2) = 520 := by decide
  have e1 : edgeCode (({2,3,9} : Finset (Fin 11)).erase 3) = 516 := by decide
  have e2 : edgeCode (({2,3,9} : Finset (Fin 11)).erase 9) = 12 := by decide
  have c3 : edgeCode ({2,3,9} : Finset (Fin 11)) = 524 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F2_3_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F2_3_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F2_3_9.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face3_4_9_coeff (h : ({3,4,9} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F3_4_9.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F3_4_9.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F3_4_9.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F3_4_9.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({3,4,9} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({3,4,9} : Finset (Fin 11)) h3 0 = 3 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({3,4,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({3,4,9} : Finset (Fin 11)) h3 1 = 4 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({3,4,9} : Finset (Fin 11)).erase 3) = 528 := by decide
  have e1 : edgeCode (({3,4,9} : Finset (Fin 11)).erase 4) = 520 := by decide
  have e2 : edgeCode (({3,4,9} : Finset (Fin 11)).erase 9) = 24 := by decide
  have c3 : edgeCode ({3,4,9} : Finset (Fin 11)) = 536 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F3_4_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F3_4_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F3_4_9.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face4_5_10_coeff (h : ({4,5,10} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_5_10.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_5_10.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_5_10.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_5_10.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({4,5,10} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F4_5_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F4_5_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F4_5_10.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face4_9_10_coeff (h : ({4,9,10} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_9_10.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_9_10.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_9_10.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F4_9_10.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({4,9,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({4,9,10} : Finset (Fin 11)) h3 0 = 4 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({4,9,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({4,9,10} : Finset (Fin 11)) h3 1 = 9 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({4,9,10} : Finset (Fin 11)).erase 4) = 1536 := by decide
  have e1 : edgeCode (({4,9,10} : Finset (Fin 11)).erase 9) = 1040 := by decide
  have e2 : edgeCode (({4,9,10} : Finset (Fin 11)).erase 10) = 528 := by decide
  have c3 : edgeCode ({4,9,10} : Finset (Fin 11)) = 1552 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F4_9_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F4_9_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F4_9_10.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face5_6_10_coeff (h : ({5,6,10} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F5_6_10.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F5_6_10.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F5_6_10.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F5_6_10.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({5,6,10} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F5_6_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F5_6_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F5_6_10.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face6_7_10_coeff (h : ({6,7,10} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F6_7_10.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F6_7_10.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F6_7_10.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F6_7_10.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({6,7,10} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F6_7_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F6_7_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F6_7_10.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face7_8_10_coeff (h : ({7,8,10} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F7_8_10.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F7_8_10.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F7_8_10.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F7_8_10.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({7,8,10} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F7_8_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F7_8_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F7_8_10.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

theorem face8_9_10_coeff (h : ({8,9,10} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    canonicalFaceP rep7D rep7Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F8_9_10.fc_p ∧ canonicalFaceQ rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F8_9_10.fc_q ∧
    canonicalFaceB rep7D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F8_9_10.fc_b ∧ rep7FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep7F8_9_10.fc_bound := by
  have h3 := q1FaceCard 7 4 ⟨({8,9,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({8,9,10} : Finset (Fin 11)) h3 0 = 8 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({8,9,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({8,9,10} : Finset (Fin 11)) h3 1 = 9 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({8,9,10} : Finset (Fin 11)).erase 8) = 1536 := by decide
  have e1 : edgeCode (({8,9,10} : Finset (Fin 11)).erase 9) = 1280 := by decide
  have e2 : edgeCode (({8,9,10} : Finset (Fin 11)).erase 10) = 768 := by decide
  have c3 : edgeCode ({8,9,10} : Finset (Fin 11)) = 1792 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,N11Formalization.Class33FaceTreeRep7F8_9_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,N11Formalization.Class33FaceTreeRep7F8_9_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,N11Formalization.Class33FaceTreeRep7F8_9_10.fc_b]
  · simp only [rep7FaceMax,c3,rep7FaceMaxCode]

/-- The `faces` field. -/
def rep7Faces : ∀ f : q1Faces 7 4, EfficientFaceCertificate (canonicalFaceP rep7D rep7Kap f)
    (canonicalFaceQ rep7D f) (canonicalFaceB rep7D f) (rep7FaceMax f) := by
  rintro ⟨f,hf⟩
  rcases rep7_face_cases f hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1,h2,h3,h4⟩ := face0_1_8_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F0_1_8.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face1_2_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F1_2_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face1_8_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F1_8_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face2_3_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F2_3_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face3_4_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F3_4_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face4_5_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F4_5_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face4_9_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F4_9_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face5_6_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F5_6_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face6_7_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F6_7_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face7_8_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F7_8_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face8_9_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep7F8_9_10.certificate

/-- Reduction of `CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 7` to its nine sector certificates and the strict total. -/
theorem rep7_table_of_sectors (sectorMax : Fin 9 → ℚ)
    (hsector : ∀ i : Fin 9, EfficientSectorCertificate (canonicalSectorC rep7D 0 rep7Eta i)
      (rep7D.mu (ActualRingLinkBoundaryData.nextSite i)) (rep7D.leftSecond i) (rep7D.rightSecond i)
      (rep7D.leftFirst i) (rep7D.rightFirst i) (sectorMax i))
    (hstrict : canonicalTotalUpperQ rep7D rep7Kap rep7Eta sharpAlpha rep7FaceMax rep7SwitchMax sectorMax <
      RatInterval.piLo) : CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 7 :=
  ⟨rep7D,rep7Kap,rep7Eta,⟨{ faceMax := rep7FaceMax
      switchMax := rep7SwitchMax
      sectorMax := sectorMax
      balance := rep7_balance
      edge_nonnegative := rep7_kap_nonneg
      eta_nonnegative := rep7_eta_nonneg
      bracket := sharpAlpha_bracket
      faces := rep7Faces
      switches := rep7Switches
      sectors := hsector
      strict := hstrict }⟩⟩

end N11Formalization.Class33Rep7Assembly
#print axioms N11Formalization.Class33Rep7Assembly.rep7Faces
#print axioms N11Formalization.Class33Rep7Assembly.rep7_table_of_sectors
