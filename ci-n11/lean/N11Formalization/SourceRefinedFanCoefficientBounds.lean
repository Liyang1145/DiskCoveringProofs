import N11Formalization.SourceBoundarySignBounds

/-! Sharper actual source normal coefficients at SAME root. All literals are
OUTWARD enclosures of the existing sound determinant-expression boxes, checked
by kernel rational arithmetic. No numerical coefficient equality or replacement
source is asserted. These boxes have width2/100000 rather than2..3/1000. -/
set_option autoImplicit false
namespace N11Formalization.SourceRefinedFanCoefficientBounds
open N11Formalization RatInterval
noncomputable section

abbrev contact (i : Fin 4) : Fin 9 := SourceBoundarySignBounds.contact i
abbrev rawA (i : Fin 4) : RatInterval := SourceBoundarySignBounds.rawA i
abbrev rawB (i : Fin 4) : RatInterval := SourceBoundarySignBounds.rawB i

def ABox (i : Fin 4) : RatInterval :=
  ![intv (-50386438/100000000) (-50384438/100000000),
    intv (-76205758/100000000) (-76203758/100000000),
    intv (-109478177/100000000) (-109476177/100000000),
    intv (-80747670/100000000) (-80745670/100000000)] i
def BBox (i : Fin 4) : RatInterval :=
  ![intv (-72772402/100000000) (-72770402/100000000),
    intv (-62630518/100000000) (-62628518/100000000),
    intv (-88316469/100000000) (-88314469/100000000),
    intv (-80747670/100000000) (-80745670/100000000)] i

private theorem hub1 (q : Fin 2) :
    SourceFanBarycentricSigns.hubBox 1 q=ndHub1Box ndBox q := by
  simp [SourceFanBarycentricSigns.hubBox]
private theorem hub2 (q : Fin 2) :
    SourceFanBarycentricSigns.hubBox 2 q=ndHub0Box ndBox q := by
  simp [SourceFanBarycentricSigns.hubBox,Fin.ext_iff]
private theorem hub3 (q : Fin 2) :
    SourceFanBarycentricSigns.hubBox 3 q=ndHub0Box ndBox q := by
  simp [SourceFanBarycentricSigns.hubBox,Fin.ext_iff]
private theorem hub8 (q : Fin 2) :
    SourceFanBarycentricSigns.hubBox 8 q=ndHub1Box ndBox q := by
  simp [SourceFanBarycentricSigns.hubBox]

macro "refined_coefficient_eval" : tactic =>
  `(tactic|
    (simp only [Contains,ABox,BBox,rawA,rawB,SourceBoundarySignBounds.rawA,
      SourceBoundarySignBounds.rawB,div,inv,SourceBoundarySignBounds.numeratorA,
      SourceBoundarySignBounds.numeratorB,SourceBoundarySignBounds.denominator,
      contact,SourceBoundarySignBounds.contact,SourceFanBarycentricSigns.determinantBox,
      SourceFanBarycentricSigns.normalPBox,SourceFanBarycentricSigns.normalQBox,
      SourceFanBarycentricSigns.normalHBox,hub1,hub2,hub3,hub8,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
     nd_eval))

private theorem A0 : Contains (ABox 0) (rawA 0) := by refined_coefficient_eval
private theorem A1 : Contains (ABox 1) (rawA 1) := by refined_coefficient_eval
private theorem A2 : Contains (ABox 2) (rawA 2) := by refined_coefficient_eval
private theorem A3 : Contains (ABox 3) (rawA 3) := by refined_coefficient_eval
private theorem B0 : Contains (BBox 0) (rawB 0) := by refined_coefficient_eval
private theorem B1 : Contains (BBox 1) (rawB 1) := by refined_coefficient_eval
private theorem B2 : Contains (BBox 2) (rawB 2) := by refined_coefficient_eval
private theorem B3 : Contains (BBox 3) (rawB 3) := by refined_coefficient_eval

theorem contains_raw (i : Fin 4) :
    Contains (ABox i) (rawA i) ∧ Contains (BBox i) (rawB i) := by
  fin_cases i
  · exact ⟨A0,B0⟩
  · exact ⟨A1,B1⟩
  · exact ⟨A2,B2⟩
  · exact ⟨A3,B3⟩

private theorem det_mem {P Q : Point} {IP IQ : Fin 2 → RatInterval}
    (hp : ∀ q,(IP q).Mem (P q)) (hq : ∀ q,(IQ q).Mem (Q q)) :
    (SourceFanBarycentricSigns.determinantBox IP IQ).Mem (PinTangentGeometry.det P Q) :=
  sub_mem (mul_mem (hp 0) (hq 1)) (mul_mem (hp 1) (hq 0))

theorem raw_membership (i : Fin 4) :
    (rawA i).Mem (SourceFanLengthCovector.sourceA (contact i)) ∧
    (rawB i).Mem (SourceFanLengthCovector.sourceB (contact i)) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hp (q : Fin 2) :
      (SourceFanBarycentricSigns.normalPBox (contact i) q).Mem
        (SourceFanLengthCovector.normalP (contact i) q) :=
    sub_mem (ndUvecBox_mem hb _ q) (ndRingBox_mem hb _ q)
  have hq (q : Fin 2) :
      (SourceFanBarycentricSigns.normalQBox (contact i) q).Mem
        (SourceFanLengthCovector.normalQ (contact i) q) :=
    sub_mem (ndUvecBox_mem hb _ q) (ndRingBox_mem hb _ q)
  have hh (q : Fin 2) :
      (SourceFanBarycentricSigns.normalHBox (contact i) q).Mem
        (SourceFanLengthCovector.normalH (contact i) q) := by
    have hs :
        (SourceFanBarycentricSigns.hubBox (contact i) q).Mem
          (SourceFanLengthCovector.sourceHub (contact i) q) := by
      unfold SourceFanBarycentricSigns.hubBox SourceFanLengthCovector.sourceHub
      split_ifs
      · exact ndHub1Box_mem hb q
      · exact ndHub0Box_mem hb q
    exact sub_mem (ndUvecBox_mem hb _ q) hs
  exact ⟨div_mem (det_mem hh hq) (det_mem hp hq)
      (Or.inr (SourceBoundarySignBounds.denominator_pos i)),
    div_mem (det_mem hp hh) (det_mem hp hq)
      (Or.inr (SourceBoundarySignBounds.denominator_pos i))⟩

/-- ALL8 refined coefficients contain the ACTUAL derivative coefficients,
not the certificate box centre's diagnostic values. -/
theorem refined_membership (i : Fin 4) :
    (ABox i).Mem (SourceFanLengthCovector.sourceA (contact i)) ∧
    (BBox i).Mem (SourceFanLengthCovector.sourceB (contact i)) :=
  ⟨mem_of_contains (contains_raw i).1 (raw_membership i).1,
    mem_of_contains (contains_raw i).2 (raw_membership i).2⟩

theorem widths (i : Fin 4) :
    (ABox i).hi-(ABox i).lo=2/100000 ∧
      (BBox i).hi-(BBox i).lo=2/100000 := by
  fin_cases i <;> norm_num [ABox,BBox,intv]

end
end N11Formalization.SourceRefinedFanCoefficientBounds
#check @N11Formalization.SourceRefinedFanCoefficientBounds.refined_membership
#print axioms N11Formalization.SourceRefinedFanCoefficientBounds.refined_membership
