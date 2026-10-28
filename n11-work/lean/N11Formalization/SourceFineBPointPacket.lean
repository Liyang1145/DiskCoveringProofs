import N11Formalization.SourceBPointPacket

/-! Finer exact-grid coordinate readouts of SAME true29 source points.
All58 outward containments must be kernel-paid; no midpoint root/auxiliary
substitution. Real hubs9/10 and genuine reflected auxiliaries remain. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineBPointPacket
open N11Formalization RatInterval SourceBMatrixIntervals
noncomputable section

def PL : Fin 29 → Fin 2 → ℤ :=
 ![![-73575385,-67724908],![-14458443,-98949248],![40460867,-91448993],
   ![92558379,-37854278],![92558379,37854276],![40460867,91448991],
   ![-14458443,98949246],![-73575385,67724905],![-100000000,-2],
   ![-76470619,-29836983],![-35578741,-67361113],![9483654,-69442413],
   ![61581165,-59860858],![89252163,0],![61581165,59860855],
   ![9483654,69442411],![-35578741,67361110],![-76470619,29836979],
   ![27297746,0],![-14942850,0],![6177448,-31588136],![6177448,31588135],
   ![-11636647,-37854279],![30603950,-37854280],![58274948,-22006582],
   ![58274948,22006577],![30603950,37854274],![-11636647,37854275],
   ![-52941238,-5]]
def PH : Fin 29 → Fin 2 → ℤ :=
 ![![-73575382,-67724905],![-14458439,-98949246],![40460870,-91448991],
   ![92558381,-37854275],![92558381,37854278],![40460870,91448993],
   ![-14458439,98949248],![-73575382,67724908],![-99999999,2],
   ![-76470616,-29836979],![-35578738,-67361110],![9483657,-69442411],
   ![61581169,-59860855],![89252183,0],![61581169,59860858],
   ![9483657,69442413],![-35578738,67361113],![-76470616,29836983],
   ![27297747,0],![-14942849,0],![6177449,-31588135],![6177449,31588136],
   ![-11636639,-37854275],![30603957,-37854274],![58274972,-22006577],
   ![58274972,22006582],![30603957,37854280],![-11636639,37854279],
   ![-52941233,5]]

def pointI (i : Fin 29) (q : Fin 2) : RatInterval :=
  intv ((PL i q : ℚ)/100000000) ((PH i q : ℚ)/100000000)

macro "fine_source_point_eval" : tactic =>
  `(tactic|
    (simp [Contains,pointI,PL,PH,nodeBox,siteBox,auxBox,flipBox,representativeBox,
      SourceAllFaceBalance.mirrored,SourceAllFaceBalance.repIndex,Fin.reduceFinMk]
     all_goals nd_eval))

private theorem p0 (q : Fin 2) : Contains (pointI 0 q) (nodeBox 0 q) := by fin_cases q <;> fine_source_point_eval
private theorem p1 (q : Fin 2) : Contains (pointI 1 q) (nodeBox 1 q) := by fin_cases q <;> fine_source_point_eval
private theorem p2 (q : Fin 2) : Contains (pointI 2 q) (nodeBox 2 q) := by fin_cases q <;> fine_source_point_eval
private theorem p3 (q : Fin 2) : Contains (pointI 3 q) (nodeBox 3 q) := by fin_cases q <;> fine_source_point_eval
private theorem p4 (q : Fin 2) : Contains (pointI 4 q) (nodeBox 4 q) := by fin_cases q <;> fine_source_point_eval
private theorem p5 (q : Fin 2) : Contains (pointI 5 q) (nodeBox 5 q) := by fin_cases q <;> fine_source_point_eval
private theorem p6 (q : Fin 2) : Contains (pointI 6 q) (nodeBox 6 q) := by fin_cases q <;> fine_source_point_eval
private theorem p7 (q : Fin 2) : Contains (pointI 7 q) (nodeBox 7 q) := by fin_cases q <;> fine_source_point_eval
private theorem p8 (q : Fin 2) : Contains (pointI 8 q) (nodeBox 8 q) := by fin_cases q <;> fine_source_point_eval
private theorem p9 (q : Fin 2) : Contains (pointI 9 q) (nodeBox 9 q) := by fin_cases q <;> fine_source_point_eval
private theorem p10 (q : Fin 2) : Contains (pointI 10 q) (nodeBox 10 q) := by fin_cases q <;> fine_source_point_eval
private theorem p11 (q : Fin 2) : Contains (pointI 11 q) (nodeBox 11 q) := by fin_cases q <;> fine_source_point_eval
private theorem p12 (q : Fin 2) : Contains (pointI 12 q) (nodeBox 12 q) := by fin_cases q <;> fine_source_point_eval
private theorem p13 (q : Fin 2) : Contains (pointI 13 q) (nodeBox 13 q) := by fin_cases q <;> fine_source_point_eval
private theorem p14 (q : Fin 2) : Contains (pointI 14 q) (nodeBox 14 q) := by fin_cases q <;> fine_source_point_eval
private theorem p15 (q : Fin 2) : Contains (pointI 15 q) (nodeBox 15 q) := by fin_cases q <;> fine_source_point_eval
private theorem p16 (q : Fin 2) : Contains (pointI 16 q) (nodeBox 16 q) := by fin_cases q <;> fine_source_point_eval
private theorem p17 (q : Fin 2) : Contains (pointI 17 q) (nodeBox 17 q) := by fin_cases q <;> fine_source_point_eval
private theorem p18 (q : Fin 2) : Contains (pointI 18 q) (nodeBox 18 q) := by fin_cases q <;> fine_source_point_eval
private theorem p19 (q : Fin 2) : Contains (pointI 19 q) (nodeBox 19 q) := by fin_cases q <;> fine_source_point_eval
private theorem p20 (q : Fin 2) : Contains (pointI 20 q) (nodeBox 20 q) := by fin_cases q <;> fine_source_point_eval
private theorem p21 (q : Fin 2) : Contains (pointI 21 q) (nodeBox 21 q) := by fin_cases q <;> fine_source_point_eval
private theorem p22 (q : Fin 2) : Contains (pointI 22 q) (nodeBox 22 q) := by fin_cases q <;> fine_source_point_eval
private theorem p23 (q : Fin 2) : Contains (pointI 23 q) (nodeBox 23 q) := by fin_cases q <;> fine_source_point_eval
private theorem p24 (q : Fin 2) : Contains (pointI 24 q) (nodeBox 24 q) := by fin_cases q <;> fine_source_point_eval
private theorem p25 (q : Fin 2) : Contains (pointI 25 q) (nodeBox 25 q) := by fin_cases q <;> fine_source_point_eval
private theorem p26 (q : Fin 2) : Contains (pointI 26 q) (nodeBox 26 q) := by fin_cases q <;> fine_source_point_eval
private theorem p27 (q : Fin 2) : Contains (pointI 27 q) (nodeBox 27 q) := by fin_cases q <;> fine_source_point_eval
private theorem p28 (q : Fin 2) : Contains (pointI 28 q) (nodeBox 28 q) := by fin_cases q <;> fine_source_point_eval

theorem pointI_contains (i : Fin 29) (q : Fin 2) :
    Contains (pointI i q) (nodeBox i q) := by
  fin_cases i
  · exact p0 q
  · exact p1 q
  · exact p2 q
  · exact p3 q
  · exact p4 q
  · exact p5 q
  · exact p6 q
  · exact p7 q
  · exact p8 q
  · exact p9 q
  · exact p10 q
  · exact p11 q
  · exact p12 q
  · exact p13 q
  · exact p14 q
  · exact p15 q
  · exact p16 q
  · exact p17 q
  · exact p18 q
  · exact p19 q
  · exact p20 q
  · exact p21 q
  · exact p22 q
  · exact p23 q
  · exact p24 q
  · exact p25 q
  · exact p26 q
  · exact p27 q
  · exact p28 q

theorem pointI_mem (i : Fin 29) (q : Fin 2) :
    (pointI i q).Mem ((SourceN2.srcX2 SourceExactRoot.sourceRoot i).ofLp q) :=
  mem_of_contains (pointI_contains i q) (nodeBox_mem i q)

theorem point_width (i : Fin 29) (q : Fin 2) : PL i q ≤ PH i q := by
  fin_cases i <;> fin_cases q <;> decide +kernel

end
end N11Formalization.SourceFineBPointPacket
#check @N11Formalization.SourceFineBPointPacket.pointI_mem
#print axioms N11Formalization.SourceFineBPointPacket.pointI_mem
