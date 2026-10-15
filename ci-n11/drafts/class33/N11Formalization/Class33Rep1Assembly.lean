import N11Formalization.Class33SwitchFields
import N11Formalization.Class33Labels
import N11Formalization.CanonicalBalancedFiniteClassCertificate
import N11Formalization.Class33FaceTreeRep1F0_1_8
import N11Formalization.Class33FaceTreeRep1F1_2_10
import N11Formalization.Class33FaceTreeRep1F1_8_10
import N11Formalization.Class33FaceTreeRep1F2_3_9
import N11Formalization.Class33FaceTreeRep1F2_9_10
import N11Formalization.Class33FaceTreeRep1F3_4_9
import N11Formalization.Class33FaceTreeRep1F4_5_9
import N11Formalization.Class33FaceTreeRep1F5_6_9
import N11Formalization.Class33FaceTreeRep1F6_7_10
import N11Formalization.Class33FaceTreeRep1F6_9_10
import N11Formalization.Class33FaceTreeRep1F7_8_10

/-! Class33 DRAFT (uncompiled): q1-balanced representative cut 1 (q1Faces 1 4).
Faces: 11 plane trees (Class33FaceTreeRep1F*); switches: `rep1Switches`.
`rep1_table_of_sectors` reduces `CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 1` to the 9 sector certificates and the strict total. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33Rep1Assembly
open CanonicalSharedMomentFiniteCertificate ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport
open ActualOrderedMetricGraphs ActualCanonicalFaceCoordinates SharedMomentFiniteFactorCertificate
open SharedMomentEfficientFactorCertificate Class33RepData Class33SwitchBridge Class33Labels
open Class33SwitchFields

theorem rep1_face_cases : ∀ f ∈ q1Faces 1 4, f = ({0,1,8} : Finset (Fin 11)) ∨ f = ({1,2,10} : Finset (Fin 11)) ∨ f = ({1,8,10} : Finset (Fin 11)) ∨ f = ({2,3,9} : Finset (Fin 11)) ∨ f = ({2,9,10} : Finset (Fin 11)) ∨ f = ({3,4,9} : Finset (Fin 11)) ∨ f = ({4,5,9} : Finset (Fin 11)) ∨ f = ({5,6,9} : Finset (Fin 11)) ∨ f = ({6,7,10} : Finset (Fin 11)) ∨ f = ({6,9,10} : Finset (Fin 11)) ∨ f = ({7,8,10} : Finset (Fin 11)) := by
  decide
def rep1FaceMaxCode : ℕ → ℚ
  | 259 => N11Formalization.Class33FaceTreeRep1F0_1_8.fc_bound
  | 1030 => N11Formalization.Class33FaceTreeRep1F1_2_10.fc_bound
  | 1282 => N11Formalization.Class33FaceTreeRep1F1_8_10.fc_bound
  | 524 => N11Formalization.Class33FaceTreeRep1F2_3_9.fc_bound
  | 1540 => N11Formalization.Class33FaceTreeRep1F2_9_10.fc_bound
  | 536 => N11Formalization.Class33FaceTreeRep1F3_4_9.fc_bound
  | 560 => N11Formalization.Class33FaceTreeRep1F4_5_9.fc_bound
  | 608 => N11Formalization.Class33FaceTreeRep1F5_6_9.fc_bound
  | 1216 => N11Formalization.Class33FaceTreeRep1F6_7_10.fc_bound
  | 1600 => N11Formalization.Class33FaceTreeRep1F6_9_10.fc_bound
  | 1408 => N11Formalization.Class33FaceTreeRep1F7_8_10.fc_bound
  | _ => 0
def rep1FaceMax (f : q1Faces 1 4) : ℚ := rep1FaceMaxCode (edgeCode f.val)

theorem face0_1_8_coeff (h : ({0,1,8} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F0_1_8.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F0_1_8.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F0_1_8.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F0_1_8.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({0,1,8} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F0_1_8.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F0_1_8.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F0_1_8.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face1_2_10_coeff (h : ({1,2,10} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_2_10.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_2_10.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_2_10.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_2_10.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({1,2,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({1,2,10} : Finset (Fin 11)) h3 0 = 1 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({1,2,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({1,2,10} : Finset (Fin 11)) h3 1 = 2 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({1,2,10} : Finset (Fin 11)).erase 1) = 1028 := by decide
  have e1 : edgeCode (({1,2,10} : Finset (Fin 11)).erase 2) = 1026 := by decide
  have e2 : edgeCode (({1,2,10} : Finset (Fin 11)).erase 10) = 6 := by decide
  have c3 : edgeCode ({1,2,10} : Finset (Fin 11)) = 1030 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F1_2_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F1_2_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F1_2_10.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face1_8_10_coeff (h : ({1,8,10} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_8_10.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_8_10.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_8_10.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F1_8_10.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({1,8,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({1,8,10} : Finset (Fin 11)) h3 0 = 1 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({1,8,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({1,8,10} : Finset (Fin 11)) h3 1 = 8 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({1,8,10} : Finset (Fin 11)).erase 1) = 1280 := by decide
  have e1 : edgeCode (({1,8,10} : Finset (Fin 11)).erase 8) = 1026 := by decide
  have e2 : edgeCode (({1,8,10} : Finset (Fin 11)).erase 10) = 258 := by decide
  have c3 : edgeCode ({1,8,10} : Finset (Fin 11)) = 1282 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F1_8_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F1_8_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F1_8_10.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face2_3_9_coeff (h : ({2,3,9} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_3_9.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_3_9.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_3_9.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_3_9.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({2,3,9} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F2_3_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F2_3_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F2_3_9.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face2_9_10_coeff (h : ({2,9,10} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_9_10.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_9_10.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_9_10.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F2_9_10.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({2,9,10} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F2_9_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F2_9_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F2_9_10.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face3_4_9_coeff (h : ({3,4,9} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F3_4_9.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F3_4_9.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F3_4_9.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F3_4_9.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({3,4,9} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F3_4_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F3_4_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F3_4_9.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face4_5_9_coeff (h : ({4,5,9} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F4_5_9.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F4_5_9.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F4_5_9.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F4_5_9.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({4,5,9} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({4,5,9} : Finset (Fin 11)) h3 0 = 4 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({4,5,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({4,5,9} : Finset (Fin 11)) h3 1 = 5 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({4,5,9} : Finset (Fin 11)).erase 4) = 544 := by decide
  have e1 : edgeCode (({4,5,9} : Finset (Fin 11)).erase 5) = 528 := by decide
  have e2 : edgeCode (({4,5,9} : Finset (Fin 11)).erase 9) = 48 := by decide
  have c3 : edgeCode ({4,5,9} : Finset (Fin 11)) = 560 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F4_5_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F4_5_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F4_5_9.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face5_6_9_coeff (h : ({5,6,9} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F5_6_9.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F5_6_9.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F5_6_9.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F5_6_9.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({5,6,9} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({5,6,9} : Finset (Fin 11)) h3 0 = 5 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({5,6,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({5,6,9} : Finset (Fin 11)) h3 1 = 6 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({5,6,9} : Finset (Fin 11)).erase 5) = 576 := by decide
  have e1 : edgeCode (({5,6,9} : Finset (Fin 11)).erase 6) = 544 := by decide
  have e2 : edgeCode (({5,6,9} : Finset (Fin 11)).erase 9) = 96 := by decide
  have c3 : edgeCode ({5,6,9} : Finset (Fin 11)) = 608 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F5_6_9.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F5_6_9.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F5_6_9.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face6_7_10_coeff (h : ({6,7,10} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_7_10.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_7_10.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_7_10.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_7_10.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({6,7,10} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F6_7_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F6_7_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F6_7_10.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face6_9_10_coeff (h : ({6,9,10} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_9_10.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_9_10.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_9_10.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F6_9_10.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({6,9,10} : Finset (Fin 11)), h⟩
  have l0 : canonicalLabel ({6,9,10} : Finset (Fin 11)) h3 0 = 6 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({6,9,10} : Finset (Fin 11)) h3 2 = 10 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({6,9,10} : Finset (Fin 11)) h3 1 = 9 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({6,9,10} : Finset (Fin 11)).erase 6) = 1536 := by decide
  have e1 : edgeCode (({6,9,10} : Finset (Fin 11)).erase 9) = 1088 := by decide
  have e2 : edgeCode (({6,9,10} : Finset (Fin 11)).erase 10) = 576 := by decide
  have c3 : edgeCode ({6,9,10} : Finset (Fin 11)) = 1600 := by decide
  refine ⟨?_,?_,?_,?_⟩
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F6_9_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F6_9_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F6_9_10.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

theorem face7_8_10_coeff (h : ({7,8,10} : Finset (Fin 11)) ∈ q1Faces 1 4) :
    canonicalFaceP rep1D rep1Kap ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F7_8_10.fc_p ∧ canonicalFaceQ rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F7_8_10.fc_q ∧
    canonicalFaceB rep1D ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F7_8_10.fc_b ∧ rep1FaceMax ⟨_,h⟩ = N11Formalization.Class33FaceTreeRep1F7_8_10.fc_bound := by
  have h3 := q1FaceCard 1 4 ⟨({7,8,10} : Finset (Fin 11)), h⟩
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
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,rep1Kap,
        l0,l1,l2,e0,e1,e2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MuN,rep1KapCode,N11Formalization.Class33FaceTreeRep1F7_8_10.fc_p]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideSecondCode,N11Formalization.Class33FaceTreeRep1F7_8_10.fc_q]
  · funext s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep1D,
        l0,l1,l2,e0,e1,e2,c3,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep1MaskCode,rep1MinusPairs,rep1SideFirstCode,N11Formalization.Class33FaceTreeRep1F7_8_10.fc_b]
  · simp only [rep1FaceMax,c3,rep1FaceMaxCode]

/-- The `faces` field. -/
def rep1Faces : ∀ f : q1Faces 1 4, EfficientFaceCertificate (canonicalFaceP rep1D rep1Kap f)
    (canonicalFaceQ rep1D f) (canonicalFaceB rep1D f) (rep1FaceMax f) := by
  rintro ⟨f,hf⟩
  rcases rep1_face_cases f hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1,h2,h3,h4⟩ := face0_1_8_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F0_1_8.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face1_2_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F1_2_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face1_8_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F1_8_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face2_3_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F2_3_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face2_9_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F2_9_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face3_4_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F3_4_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face4_5_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F4_5_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face5_6_9_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F5_6_9.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face6_7_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F6_7_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face6_9_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F6_9_10.certificate
  · obtain ⟨h1,h2,h3,h4⟩ := face7_8_10_coeff hf
    rw [h1,h2,h3,h4]
    exact N11Formalization.Class33FaceTreeRep1F7_8_10.certificate

/-- Reduction of `CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 1` to its nine sector certificates and the strict total. -/
theorem rep1_table_of_sectors (sectorMax : Fin 9 → ℚ)
    (hsector : ∀ i : Fin 9, EfficientSectorCertificate (canonicalSectorC rep1D 0 rep1Eta i)
      (rep1D.mu (ActualRingLinkBoundaryData.nextSite i)) (rep1D.leftSecond i) (rep1D.rightSecond i)
      (rep1D.leftFirst i) (rep1D.rightFirst i) (sectorMax i))
    (hstrict : canonicalTotalUpperQ rep1D rep1Kap rep1Eta sharpAlpha rep1FaceMax rep1SwitchMax sectorMax <
      RatInterval.piLo) : CanonicalBalancedFiniteClassCertificate.RepresentativeFiniteTable 1 :=
  ⟨rep1D,rep1Kap,rep1Eta,⟨{ faceMax := rep1FaceMax
      switchMax := rep1SwitchMax
      sectorMax := sectorMax
      balance := rep1_balance
      edge_nonnegative := rep1_kap_nonneg
      eta_nonnegative := rep1_eta_nonneg
      bracket := sharpAlpha_bracket
      faces := rep1Faces
      switches := rep1Switches
      sectors := hsector
      strict := hstrict }⟩⟩

end N11Formalization.Class33Rep1Assembly
#print axioms N11Formalization.Class33Rep1Assembly.rep1Faces
#print axioms N11Formalization.Class33Rep1Assembly.rep1_table_of_sectors
