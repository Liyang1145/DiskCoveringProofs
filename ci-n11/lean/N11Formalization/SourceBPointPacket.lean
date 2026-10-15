import N11Formalization.SourceBMatrixIntervals

/-! Exact source-coordinate input packet at scale10^5. Generated literals are
proposals; ALL58 Contains readouts and real actual-source consumers below
must pass the kernel. No root is replaced by a midpoint. -/
set_option autoImplicit false
namespace N11Formalization.SourceBPointPacket
open N11Formalization RatInterval SourceBMatrixIntervals
noncomputable section

def PL : Fin 29 → Fin 2 → ℤ :=
 ![![-73577,-67726],
   ![-14460,-98951],
   ![40459,-91450],
   ![92557,-37856],
   ![92557,37853],
   ![40459,91447],
   ![-14460,98948],
   ![-73577,67723],
   ![-100001,-1],
   ![-76472,-29838],
   ![-35580,-67363],
   ![9482,-69444],
   ![61580,-59862],
   ![89251,-1],
   ![61580,59859],
   ![9482,69441],
   ![-35580,67360],
   ![-76472,29835],
   ![27296,-1],
   ![-14944,-1],
   ![6176,-31590],
   ![6176,31587],
   ![-11638,-37856],
   ![30602,-37856],
   ![58273,-22008],
   ![58273,22005],
   ![30602,37853],
   ![-11638,37853],
   ![-52943,-2]]

def PH : Fin 29 → Fin 2 → ℤ :=
 ![![-73574,-67723],
   ![-14457,-98948],
   ![40462,-91447],
   ![92560,-37853],
   ![92560,37856],
   ![40462,91450],
   ![-14457,98951],
   ![-73574,67726],
   ![-99998,2],
   ![-76469,-29835],
   ![-35577,-67360],
   ![9485,-69441],
   ![61583,-59859],
   ![89254,2],
   ![61583,59862],
   ![9485,69444],
   ![-35577,67363],
   ![-76469,29838],
   ![27299,2],
   ![-14941,2],
   ![6179,-31587],
   ![6179,31590],
   ![-11635,-37853],
   ![30605,-37853],
   ![58276,-22005],
   ![58276,22008],
   ![30605,37856],
   ![-11635,37856],
   ![-52940,1]]

def pointI (i : Fin 29) (q : Fin 2) : RatInterval :=
  intv ((PL i q : ℚ)/100000) ((PH i q : ℚ)/100000)

macro "source_point_eval" : tactic =>
  `(tactic|
    (simp [Contains,pointI,PL,PH,nodeBox,siteBox,auxBox,flipBox,representativeBox,
      SourceAllFaceBalance.mirrored,SourceAllFaceBalance.repIndex,Fin.reduceFinMk]
     all_goals nd_eval))

private theorem p0_0 : Contains (pointI 0 0) (nodeBox 0 0) := by
  source_point_eval
private theorem p0_1 : Contains (pointI 0 1) (nodeBox 0 1) := by
  source_point_eval
private theorem p1_0 : Contains (pointI 1 0) (nodeBox 1 0) := by
  source_point_eval
private theorem p1_1 : Contains (pointI 1 1) (nodeBox 1 1) := by
  source_point_eval
private theorem p2_0 : Contains (pointI 2 0) (nodeBox 2 0) := by
  source_point_eval
private theorem p2_1 : Contains (pointI 2 1) (nodeBox 2 1) := by
  source_point_eval
private theorem p3_0 : Contains (pointI 3 0) (nodeBox 3 0) := by
  source_point_eval
private theorem p3_1 : Contains (pointI 3 1) (nodeBox 3 1) := by
  source_point_eval
private theorem p4_0 : Contains (pointI 4 0) (nodeBox 4 0) := by
  source_point_eval
private theorem p4_1 : Contains (pointI 4 1) (nodeBox 4 1) := by
  source_point_eval
private theorem p5_0 : Contains (pointI 5 0) (nodeBox 5 0) := by
  source_point_eval
private theorem p5_1 : Contains (pointI 5 1) (nodeBox 5 1) := by
  source_point_eval
private theorem p6_0 : Contains (pointI 6 0) (nodeBox 6 0) := by
  source_point_eval
private theorem p6_1 : Contains (pointI 6 1) (nodeBox 6 1) := by
  source_point_eval
private theorem p7_0 : Contains (pointI 7 0) (nodeBox 7 0) := by
  source_point_eval
private theorem p7_1 : Contains (pointI 7 1) (nodeBox 7 1) := by
  source_point_eval
private theorem p8_0 : Contains (pointI 8 0) (nodeBox 8 0) := by
  source_point_eval
private theorem p8_1 : Contains (pointI 8 1) (nodeBox 8 1) := by
  source_point_eval
private theorem p9_0 : Contains (pointI 9 0) (nodeBox 9 0) := by
  source_point_eval
private theorem p9_1 : Contains (pointI 9 1) (nodeBox 9 1) := by
  source_point_eval
private theorem p10_0 : Contains (pointI 10 0) (nodeBox 10 0) := by
  source_point_eval
private theorem p10_1 : Contains (pointI 10 1) (nodeBox 10 1) := by
  source_point_eval
private theorem p11_0 : Contains (pointI 11 0) (nodeBox 11 0) := by
  source_point_eval
private theorem p11_1 : Contains (pointI 11 1) (nodeBox 11 1) := by
  source_point_eval
private theorem p12_0 : Contains (pointI 12 0) (nodeBox 12 0) := by
  source_point_eval
private theorem p12_1 : Contains (pointI 12 1) (nodeBox 12 1) := by
  source_point_eval
private theorem p13_0 : Contains (pointI 13 0) (nodeBox 13 0) := by
  source_point_eval
private theorem p13_1 : Contains (pointI 13 1) (nodeBox 13 1) := by
  source_point_eval
private theorem p14_0 : Contains (pointI 14 0) (nodeBox 14 0) := by
  source_point_eval
private theorem p14_1 : Contains (pointI 14 1) (nodeBox 14 1) := by
  source_point_eval
private theorem p15_0 : Contains (pointI 15 0) (nodeBox 15 0) := by
  source_point_eval
private theorem p15_1 : Contains (pointI 15 1) (nodeBox 15 1) := by
  source_point_eval
private theorem p16_0 : Contains (pointI 16 0) (nodeBox 16 0) := by
  source_point_eval
private theorem p16_1 : Contains (pointI 16 1) (nodeBox 16 1) := by
  source_point_eval
private theorem p17_0 : Contains (pointI 17 0) (nodeBox 17 0) := by
  source_point_eval
private theorem p17_1 : Contains (pointI 17 1) (nodeBox 17 1) := by
  source_point_eval
private theorem p18_0 : Contains (pointI 18 0) (nodeBox 18 0) := by
  source_point_eval
private theorem p18_1 : Contains (pointI 18 1) (nodeBox 18 1) := by
  source_point_eval
private theorem p19_0 : Contains (pointI 19 0) (nodeBox 19 0) := by
  source_point_eval
private theorem p19_1 : Contains (pointI 19 1) (nodeBox 19 1) := by
  source_point_eval
private theorem p20_0 : Contains (pointI 20 0) (nodeBox 20 0) := by
  source_point_eval
private theorem p20_1 : Contains (pointI 20 1) (nodeBox 20 1) := by
  source_point_eval
private theorem p21_0 : Contains (pointI 21 0) (nodeBox 21 0) := by
  source_point_eval
private theorem p21_1 : Contains (pointI 21 1) (nodeBox 21 1) := by
  source_point_eval
private theorem p22_0 : Contains (pointI 22 0) (nodeBox 22 0) := by
  source_point_eval
private theorem p22_1 : Contains (pointI 22 1) (nodeBox 22 1) := by
  source_point_eval
private theorem p23_0 : Contains (pointI 23 0) (nodeBox 23 0) := by
  source_point_eval
private theorem p23_1 : Contains (pointI 23 1) (nodeBox 23 1) := by
  source_point_eval
private theorem p24_0 : Contains (pointI 24 0) (nodeBox 24 0) := by
  source_point_eval
private theorem p24_1 : Contains (pointI 24 1) (nodeBox 24 1) := by
  source_point_eval
private theorem p25_0 : Contains (pointI 25 0) (nodeBox 25 0) := by
  source_point_eval
private theorem p25_1 : Contains (pointI 25 1) (nodeBox 25 1) := by
  source_point_eval
private theorem p26_0 : Contains (pointI 26 0) (nodeBox 26 0) := by
  source_point_eval
private theorem p26_1 : Contains (pointI 26 1) (nodeBox 26 1) := by
  source_point_eval
private theorem p27_0 : Contains (pointI 27 0) (nodeBox 27 0) := by
  source_point_eval
private theorem p27_1 : Contains (pointI 27 1) (nodeBox 27 1) := by
  source_point_eval
private theorem p28_0 : Contains (pointI 28 0) (nodeBox 28 0) := by
  source_point_eval
private theorem p28_1 : Contains (pointI 28 1) (nodeBox 28 1) := by
  source_point_eval

theorem pointI_contains (i : Fin 29) (q : Fin 2) :
    Contains (pointI i q) (nodeBox i q) := by
  fin_cases i <;> fin_cases q
  · exact p0_0
  · exact p0_1
  · exact p1_0
  · exact p1_1
  · exact p2_0
  · exact p2_1
  · exact p3_0
  · exact p3_1
  · exact p4_0
  · exact p4_1
  · exact p5_0
  · exact p5_1
  · exact p6_0
  · exact p6_1
  · exact p7_0
  · exact p7_1
  · exact p8_0
  · exact p8_1
  · exact p9_0
  · exact p9_1
  · exact p10_0
  · exact p10_1
  · exact p11_0
  · exact p11_1
  · exact p12_0
  · exact p12_1
  · exact p13_0
  · exact p13_1
  · exact p14_0
  · exact p14_1
  · exact p15_0
  · exact p15_1
  · exact p16_0
  · exact p16_1
  · exact p17_0
  · exact p17_1
  · exact p18_0
  · exact p18_1
  · exact p19_0
  · exact p19_1
  · exact p20_0
  · exact p20_1
  · exact p21_0
  · exact p21_1
  · exact p22_0
  · exact p22_1
  · exact p23_0
  · exact p23_1
  · exact p24_0
  · exact p24_1
  · exact p25_0
  · exact p25_1
  · exact p26_0
  · exact p26_1
  · exact p27_0
  · exact p27_1
  · exact p28_0
  · exact p28_1

theorem pointI_mem (i : Fin 29) (q : Fin 2) :
    (pointI i q).Mem ((SourceN2.srcX2 SourceExactRoot.sourceRoot i).ofLp q) :=
  mem_of_contains (pointI_contains i q) (nodeBox_mem i q)

end
end N11Formalization.SourceBPointPacket
#check @N11Formalization.SourceBPointPacket.pointI_mem
#print axioms N11Formalization.SourceBPointPacket.pointI_mem
