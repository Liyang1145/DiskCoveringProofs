import N11Formalization.SourceStressGridReadout

/-! Small common-denominator actual45 stress enclosures. ALL proposed grid
endpoints are checked for outward containment of the already sound source
intervals. The rational tables are not assumed equal to the actual stress.
This stage makes subsequent contraction arithmetic finite and inexpensive. -/
set_option autoImplicit false
namespace N11Formalization.SourceCompactStressIntervals
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceStressIntervals SourceStressGridReadout
noncomputable section

def loN : Fin 45 → ℤ :=
  ![2781082,3258429,2625691,3442258,4961088,3002527,2886344,2741967,
    2741967,2886344,3002527,4961088,3442258,2625691,3258429,2781082,
    1930860,1930860,1320533,687878,894594,1320533,687878,894594,
    2862934,4132188,5691720,974919,800689,1281103,363167,292727,332267,
    292727,363167,332267,800689,974919,1281103,4132188,2862934,5691720,
    1599862,1599862,1984941]
def hiN : Fin 45 → ℤ :=
  ![2809053,3291219,2655648,3481572,4987202,3018271,2900718,2755618,
    2755618,2900718,3018271,4987202,3481572,2655648,3291219,2809053,
    1962139,1962139,1320536,687894,894611,1320536,687894,894611,
    2874321,4149267,5691723,977484,804535,1281106,364167,294059,332270,
    294059,364167,332270,804535,977484,1281106,4149267,2874321,5691723,
    1605820,1605820,1984944]

def compact (e : SourceEdge) : RatInterval :=
  intv ((loN (srcFlat e) : ℚ)/100000000) ((hiN (srcFlat e) : ℚ)/100000000)

private theorem slope5_eq : slopeI 5=intv (32095/100000) (32096/100000) := slope3_eq
private theorem slope6_eq : slopeI 6=intv (19424/100000) (19425/100000) := slope2_eq
private theorem slope7_eq : slopeI 7=intv (25465/100000) (25466/100000) := slope1_eq
private theorem slope8_eq : slopeI 8=intv (29836/100000) (29837/100000) := slope0_eq
private theorem succ4 : (4 : Fin 9)+1=5 := by decide

macro "compact_spoke_eval" : tactic =>
  `(tactic|
    (simp only [Contains,compact,loN,hiN,srcFlat,SourceN2.spokeFlat,
      stressI,spokeI,div,inv,spokeDen,SourceSignedStressAssembly.tieRep,tieOrbitQ,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
     simp [Fin.ext_iff,nd_fin_succ_0,nd_fin_succ_1,nd_fin_succ_2,
      nd_fin_succ_3,succ4,nd_fin_succ_5,nd_fin_succ_6,nd_fin_succ_7,nd_fin_succ_8,
      slope0_eq,slope1_eq,slope2_eq,slope3_eq,slope4_eq,
      slope5_eq,slope6_eq,slope7_eq,slope8_eq,
      num0_eq,num1_eq,num2_eq,num3_eq,num4_eq]
     norm_num [RatInterval.mul,RatInterval.neg,RatInterval.ofRat,intv]))

private theorem spoke00 : Contains (compact (.inl (0,0))) (stressI (.inl (0,0))) := by compact_spoke_eval
private theorem spoke01 : Contains (compact (.inl (0,1))) (stressI (.inl (0,1))) := by compact_spoke_eval
private theorem spoke10 : Contains (compact (.inl (1,0))) (stressI (.inl (1,0))) := by compact_spoke_eval
private theorem spoke11 : Contains (compact (.inl (1,1))) (stressI (.inl (1,1))) := by compact_spoke_eval
private theorem spoke20 : Contains (compact (.inl (2,0))) (stressI (.inl (2,0))) := by compact_spoke_eval
private theorem spoke21 : Contains (compact (.inl (2,1))) (stressI (.inl (2,1))) := by compact_spoke_eval
private theorem spoke30 : Contains (compact (.inl (3,0))) (stressI (.inl (3,0))) := by compact_spoke_eval
private theorem spoke31 : Contains (compact (.inl (3,1))) (stressI (.inl (3,1))) := by compact_spoke_eval
private theorem spoke40 : Contains (compact (.inl (4,0))) (stressI (.inl (4,0))) := by compact_spoke_eval
private theorem spoke41 : Contains (compact (.inl (4,1))) (stressI (.inl (4,1))) := by compact_spoke_eval
private theorem spoke50 : Contains (compact (.inl (5,0))) (stressI (.inl (5,0))) := by compact_spoke_eval
private theorem spoke51 : Contains (compact (.inl (5,1))) (stressI (.inl (5,1))) := by compact_spoke_eval
private theorem spoke60 : Contains (compact (.inl (6,0))) (stressI (.inl (6,0))) := by compact_spoke_eval
private theorem spoke61 : Contains (compact (.inl (6,1))) (stressI (.inl (6,1))) := by compact_spoke_eval
private theorem spoke70 : Contains (compact (.inl (7,0))) (stressI (.inl (7,0))) := by compact_spoke_eval
private theorem spoke71 : Contains (compact (.inl (7,1))) (stressI (.inl (7,1))) := by compact_spoke_eval
private theorem spoke80 : Contains (compact (.inl (8,0))) (stressI (.inl (8,0))) := by compact_spoke_eval
private theorem spoke81 : Contains (compact (.inl (8,1))) (stressI (.inl (8,1))) := by compact_spoke_eval

macro "compact_face_eval" : tactic =>
  `(tactic|
    (simp only [Contains,compact,loN,hiN,srcFlat,SourceN2.faceFlatEdge,stressI,
      faceI,div,inv,representativeI,SourceAllFaceBalance.repIndex,
      SourceAllFaceBalance.vertexPerm,SourceFaceReflection.swapVertex,faceOrbitQ,
      SourceBoundarySignBounds.compactA,SourceBoundarySignBounds.compactB,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk,
      centralA_eq,centralB_eq]
     nd_eval))

private theorem face00 : Contains (compact (.inr (0,0))) (stressI (.inr (0,0))) := by compact_face_eval
private theorem face01 : Contains (compact (.inr (0,1))) (stressI (.inr (0,1))) := by compact_face_eval
private theorem face02 : Contains (compact (.inr (0,2))) (stressI (.inr (0,2))) := by compact_face_eval
private theorem face10 : Contains (compact (.inr (1,0))) (stressI (.inr (1,0))) := by compact_face_eval
private theorem face11 : Contains (compact (.inr (1,1))) (stressI (.inr (1,1))) := by compact_face_eval
private theorem face12 : Contains (compact (.inr (1,2))) (stressI (.inr (1,2))) := by compact_face_eval
private theorem face20 : Contains (compact (.inr (2,0))) (stressI (.inr (2,0))) := by compact_face_eval
private theorem face21 : Contains (compact (.inr (2,1))) (stressI (.inr (2,1))) := by compact_face_eval
private theorem face22 : Contains (compact (.inr (2,2))) (stressI (.inr (2,2))) := by compact_face_eval
private theorem face30 : Contains (compact (.inr (3,0))) (stressI (.inr (3,0))) := by compact_face_eval
private theorem face31 : Contains (compact (.inr (3,1))) (stressI (.inr (3,1))) := by compact_face_eval
private theorem face32 : Contains (compact (.inr (3,2))) (stressI (.inr (3,2))) := by compact_face_eval
private theorem face40 : Contains (compact (.inr (4,0))) (stressI (.inr (4,0))) := by compact_face_eval
private theorem face41 : Contains (compact (.inr (4,1))) (stressI (.inr (4,1))) := by compact_face_eval
private theorem face42 : Contains (compact (.inr (4,2))) (stressI (.inr (4,2))) := by compact_face_eval
private theorem face50 : Contains (compact (.inr (5,0))) (stressI (.inr (5,0))) := by compact_face_eval
private theorem face51 : Contains (compact (.inr (5,1))) (stressI (.inr (5,1))) := by compact_face_eval
private theorem face52 : Contains (compact (.inr (5,2))) (stressI (.inr (5,2))) := by compact_face_eval
private theorem face60 : Contains (compact (.inr (6,0))) (stressI (.inr (6,0))) := by compact_face_eval
private theorem face61 : Contains (compact (.inr (6,1))) (stressI (.inr (6,1))) := by compact_face_eval
private theorem face62 : Contains (compact (.inr (6,2))) (stressI (.inr (6,2))) := by compact_face_eval
private theorem face70 : Contains (compact (.inr (7,0))) (stressI (.inr (7,0))) := by compact_face_eval
private theorem face71 : Contains (compact (.inr (7,1))) (stressI (.inr (7,1))) := by compact_face_eval
private theorem face72 : Contains (compact (.inr (7,2))) (stressI (.inr (7,2))) := by compact_face_eval
private theorem face80 : Contains (compact (.inr (8,0))) (stressI (.inr (8,0))) := by compact_face_eval
private theorem face81 : Contains (compact (.inr (8,1))) (stressI (.inr (8,1))) := by compact_face_eval
private theorem face82 : Contains (compact (.inr (8,2))) (stressI (.inr (8,2))) := by compact_face_eval

theorem compact_contains (e : SourceEdge) : Contains (compact e) (stressI e) := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · fin_cases k <;> fin_cases s
    · exact spoke00
    · exact spoke01
    · exact spoke10
    · exact spoke11
    · exact spoke20
    · exact spoke21
    · exact spoke30
    · exact spoke31
    · exact spoke40
    · exact spoke41
    · exact spoke50
    · exact spoke51
    · exact spoke60
    · exact spoke61
    · exact spoke70
    · exact spoke71
    · exact spoke80
    · exact spoke81
  · fin_cases f <;> fin_cases t
    · exact face00
    · exact face01
    · exact face02
    · exact face10
    · exact face11
    · exact face12
    · exact face20
    · exact face21
    · exact face22
    · exact face30
    · exact face31
    · exact face32
    · exact face40
    · exact face41
    · exact face42
    · exact face50
    · exact face51
    · exact face52
    · exact face60
    · exact face61
    · exact face62
    · exact face70
    · exact face71
    · exact face72
    · exact face80
    · exact face81
    · exact face82

theorem compact_mem (e : SourceEdge) :
    (compact e).Mem (SourceSignedStressAssembly.stress e) :=
  mem_of_contains (compact_contains e) (stressI_mem e)

end
end N11Formalization.SourceCompactStressIntervals
#check @N11Formalization.SourceCompactStressIntervals.compact_mem
#print axioms N11Formalization.SourceCompactStressIntervals.compact_mem
