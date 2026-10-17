import N11Formalization.SourceCentreB2Readout

/-! Compact rational enclosures for ACTUAL root fan coefficients used by the
boundary sign consumer. Diagnostic floats are not proof inputs: each enclosure
is widened from the existing kernel-sound expression-tree box by exact rational
Contains checks. The source root/radius is not replaced by an endpoint. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundarySignBounds
open N11Formalization RatInterval SourceFanBarycentricSigns
noncomputable section

def contact (i : Fin 4) : Fin 9 := ![1,2,3,8] i
def denominator (i : Fin 4) : RatInterval :=
  determinantBox (normalPBox (contact i)) (normalQBox (contact i))
def numeratorA (i : Fin 4) : RatInterval :=
  determinantBox (normalHBox (contact i)) (normalQBox (contact i))
def numeratorB (i : Fin 4) : RatInterval :=
  determinantBox (normalPBox (contact i)) (normalHBox (contact i))

private theorem denominator_pos0 : 0<(denominator 0).lo := by
  simp only [denominator,contact,Matrix.cons_val_zero,determinantBox,normalPBox,normalQBox]
  nd_eval
private theorem denominator_pos1 : 0<(denominator 1).lo := by
  simp only [denominator,contact,Matrix.cons_val_one,determinantBox,normalPBox,normalQBox]
  nd_eval
private theorem denominator_pos2 : 0<(denominator 2).lo := by
  change 0<(determinantBox (normalPBox 3) (normalQBox 3)).lo
  simp only [determinantBox,normalPBox,normalQBox]
  nd_eval
private theorem denominator_pos3 : 0<(denominator 3).lo := by
  change 0<(determinantBox (normalPBox 8) (normalQBox 8)).lo
  simp only [determinantBox,normalPBox,normalQBox]
  nd_eval
theorem denominator_pos (i : Fin 4) : 0<(denominator i).lo := by
  fin_cases i
  · exact denominator_pos0
  · exact denominator_pos1
  · exact denominator_pos2
  · exact denominator_pos3

def rawA (i : Fin 4) : RatInterval := div (numeratorA i) (denominator i) (Or.inr (denominator_pos i))
def rawB (i : Fin 4) : RatInterval := div (numeratorB i) (denominator i) (Or.inr (denominator_pos i))
def compactA (i : Fin 4) : RatInterval :=
  ![intv (-505/1000) (-503/1000),intv (-763/1000) (-761/1000),
    intv (-1096/1000) (-1093/1000),intv (-809/1000) (-806/1000)] i
def compactB (i : Fin 4) : RatInterval :=
  ![intv (-729/1000) (-726/1000),intv (-628/1000) (-625/1000),
    intv (-885/1000) (-881/1000),intv (-809/1000) (-806/1000)] i

private theorem selector1 (q : Fin 2) : hubBox 1 q=ndHub1Box ndBox q := by simp [hubBox]
private theorem selector2 (q : Fin 2) : hubBox 2 q=ndHub0Box ndBox q := by simp [hubBox,Fin.ext_iff]
private theorem selector3 (q : Fin 2) : hubBox 3 q=ndHub0Box ndBox q := by simp [hubBox,Fin.ext_iff]
private theorem selector8 (q : Fin 2) : hubBox 8 q=ndHub1Box ndBox q := by simp [hubBox]

macro "boundary_coefficient_eval" : tactic =>
  `(tactic|
    (simp only [Contains,compactA,compactB,rawA,rawB,div,inv,numeratorA,numeratorB,
      denominator,contact,determinantBox,normalPBox,normalQBox,normalHBox,
      selector1,selector2,selector3,selector8,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk]
     nd_eval))

private theorem compactA0 : Contains (compactA 0) (rawA 0) := by boundary_coefficient_eval
private theorem compactA1 : Contains (compactA 1) (rawA 1) := by boundary_coefficient_eval
private theorem compactA2 : Contains (compactA 2) (rawA 2) := by boundary_coefficient_eval
private theorem compactA3 : Contains (compactA 3) (rawA 3) := by boundary_coefficient_eval
private theorem compactB0 : Contains (compactB 0) (rawB 0) := by boundary_coefficient_eval
private theorem compactB1 : Contains (compactB 1) (rawB 1) := by boundary_coefficient_eval
private theorem compactB2 : Contains (compactB 2) (rawB 2) := by boundary_coefficient_eval
private theorem compactB3 : Contains (compactB 3) (rawB 3) := by boundary_coefficient_eval

theorem compact_contains (i : Fin 4) :
    Contains (compactA i) (rawA i) ∧ Contains (compactB i) (rawB i) := by
  fin_cases i
  · exact ⟨compactA0,compactB0⟩
  · exact ⟨compactA1,compactB1⟩
  · exact ⟨compactA2,compactB2⟩
  · exact ⟨compactA3,compactB3⟩

private theorem normal_mem (i : Fin 4) :
    (∀ q : Fin 2,(normalPBox (contact i) q).Mem (SourceFanLengthCovector.normalP (contact i) q)) ∧
    (∀ q : Fin 2,(normalQBox (contact i) q).Mem (SourceFanLengthCovector.normalQ (contact i) q)) ∧
    (∀ q : Fin 2,(normalHBox (contact i) q).Mem (SourceFanLengthCovector.normalH (contact i) q)) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  refine ⟨fun q => sub_mem (ndUvecBox_mem hb _ q) (ndRingBox_mem hb _ q),
    fun q => sub_mem (ndUvecBox_mem hb _ q) (ndRingBox_mem hb _ q),?_⟩
  intro q
  have hh : (hubBox (contact i) q).Mem (SourceFanLengthCovector.sourceHub (contact i) q) := by
    unfold hubBox SourceFanLengthCovector.sourceHub
    split_ifs
    · exact ndHub1Box_mem hb q
    · exact ndHub0Box_mem hb q
  exact sub_mem (ndUvecBox_mem hb _ q) hh

private theorem detBox_mem {a b : Point} {A B : Fin 2 → RatInterval}
    (hA : ∀ q,(A q).Mem (a q)) (hB : ∀ q,(B q).Mem (b q)) :
    (determinantBox A B).Mem (PinTangentGeometry.det a b) :=
  sub_mem (mul_mem (hA 0) (hB 1)) (mul_mem (hA 1) (hB 0))

/-- Coefficient boxes contain the ACTUAL source derivative coefficients,
not a rational numerical Newton candidate. -/
theorem compact_membership (i : Fin 4) :
    (compactA i).Mem (SourceFanLengthCovector.sourceA (contact i)) ∧
    (compactB i).Mem (SourceFanLengthCovector.sourceB (contact i)) := by
  obtain ⟨hP,hQ,hH⟩ := normal_mem i
  have hD := detBox_mem hP hQ
  refine ⟨mem_of_contains (compact_contains i).1 ?_,
    mem_of_contains (compact_contains i).2 ?_⟩
  · exact div_mem (detBox_mem hH hQ) hD (Or.inr (denominator_pos i))
  · exact div_mem (detBox_mem hP hH) hD (Or.inr (denominator_pos i))

end
end N11Formalization.SourceBoundarySignBounds
#check @N11Formalization.SourceBoundarySignBounds.compact_membership
#print axioms N11Formalization.SourceBoundarySignBounds.compact_membership
