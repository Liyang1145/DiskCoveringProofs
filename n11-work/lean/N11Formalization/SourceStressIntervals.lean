import N11Formalization.SourceStressClosedFormula
import N11Formalization.SourceBoundaryMultiplierIntervals

/-! Sound intervals for ALL45 actual carrying stress coefficients. Each
interval comes from the SAME source root-expression boxes; no decimal stress,
midpoint, symmetry-restricted optimum or supplied membership hypothesis.
The enclosures are inputs to the actual20-node interval solve; no contraction
or strict mixed-coercivity certificate is claimed here. -/
set_option autoImplicit false
namespace N11Formalization.SourceStressIntervals
open N11Formalization RatInterval SourceFanBarycentricSigns
open SourceBoundaryMultiplierIntervals SourceStressClosedFormula
noncomputable section

def slopeI (k : Fin 9) : RatInterval :=
  rounded (mul (sinTotLag (ndAngleBox ndBox k)) (ndRhoBox ndBox k))

private theorem slope0 : 0<(slopeI 0).lo := by unfold slopeI rounded; nd_eval
private theorem slope1 : 0<(slopeI 1).lo := by unfold slopeI rounded; nd_eval
private theorem slope2 : 0<(slopeI 2).lo := by unfold slopeI rounded; nd_eval
private theorem slope3 : 0<(slopeI 3).lo := by unfold slopeI rounded; nd_eval
private theorem slope4 : 0<(slopeI 4).lo := by unfold slopeI rounded; nd_eval

theorem slopeI_pos (k : Fin 9) : 0<(slopeI k).lo := by
  fin_cases k
  · exact slope0
  · exact slope1
  · exact slope2
  · exact slope3
  · exact slope4
  · exact slope3
  · exact slope2
  · exact slope1
  · exact slope0

theorem slopeI_mem (k : Fin 9) : (slopeI k).Mem (SourceBoundaryWeights.slope k) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have h := rounded_mem (mul_mem (sinTotLag_mem (ndAngleBox_mem hb k))
    (ndRhoBox_mem hb k))
  change (slopeI k).Mem
    (Real.sin (angleVec SourceExactRoot.sourceRoot k)*rhoK SourceExactRoot.sourceRoot k) at h
  simpa only [SourceBoundaryWeights.slope,mul_comm] using h

def tieOrbitQ (j : Fin 5) : ℚ := ![2,2,2,2,1] j
def faceOrbitQ (j : Fin 5) : ℚ := ![2,2,2,1,2] j

theorem tieOrbitQ_pos (j : Fin 5) : 0<tieOrbitQ j := by fin_cases j <;> norm_num [tieOrbitQ]
theorem faceOrbitQ_pos (j : Fin 5) : 0<faceOrbitQ j := by fin_cases j <;> norm_num [faceOrbitQ]
theorem tieOrbitQ_cast (j : Fin 5) :
    (tieOrbitQ j : ℝ)=SourceSignedStressAssembly.tieOrbitSize j := by
  fin_cases j <;> norm_num [tieOrbitQ,SourceSignedStressAssembly.tieOrbitSize]
theorem faceOrbitQ_cast (j : Fin 5) :
    (faceOrbitQ j : ℝ)=SourceAllFaceBalance.orbitSize j := by
  fin_cases j <;> norm_num [faceOrbitQ,SourceAllFaceBalance.orbitSize]

def spokeDen (k : Fin 9) (s : Fin 2) : RatInterval :=
  mul (ofRat (tieOrbitQ (SourceSignedStressAssembly.tieRep k)))
    (slopeI (if s=0 then k else k+1))

theorem spokeDen_pos (k : Fin 9) (s : Fin 2) : 0<(spokeDen k s).lo := by
  let l : Fin 9 := if s=0 then k else k+1
  have hm := slopeI_mem l
  have hv : (slopeI l).lo≤(slopeI l).hi := by
    exact (Rat.cast_le).mp (le_trans hm.1 hm.2)
  have hl := slopeI_pos l
  have hh : 0<(slopeI l).hi := lt_of_lt_of_le hl hv
  have ho := tieOrbitQ_pos (SourceSignedStressAssembly.tieRep k)
  change 0 < min
    (min (tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).lo)
      (tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).hi))
    (min (tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).lo)
      (tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).hi))
  exact lt_min (lt_min (mul_pos ho hl) (mul_pos ho hh))
    (lt_min (mul_pos ho hl) (mul_pos ho hh))

def spokeI (k : Fin 9) (s : Fin 2) : RatInterval :=
  div (neg (numeratorBox (SourceSignedStressAssembly.tieRep k)))
    (spokeDen k s) (Or.inr (spokeDen_pos k s))

theorem spokeI_mem (k : Fin 9) (s : Fin 2) :
    (spokeI k s).Mem (SourceSignedStressAssembly.stress (.inl (k,s))) := by
  rw [spoke_closed]
  have hd := mul_mem (ofRat_mem (tieOrbitQ (SourceSignedStressAssembly.tieRep k)))
    (slopeI_mem (if s=0 then k else k+1))
  rw [tieOrbitQ_cast] at hd
  have he : (SourceBoundaryWeights.slope (if s=0 then k else k+1))=
      if s=0 then SourceBoundaryWeights.slope k else SourceBoundaryWeights.slope (k+1) := by
    split_ifs <;> rfl
  rw [he] at hd
  exact div_mem (neg_mem (numeratorBox_mem _)) hd (Or.inr (spokeDen_pos k s))

private theorem det_mem {P Q : Point} {IP IQ : Fin 2 → RatInterval}
    (hp : ∀ i,(IP i).Mem (P i)) (hq : ∀ i,(IQ i).Mem (Q i)) :
    (determinantBox IP IQ).Mem (PinTangentGeometry.det P Q) :=
  sub_mem (mul_mem (hp 0) (hq 1)) (mul_mem (hp 1) (hq 0))

def centralDen : RatInterval := determinantBox centralPBox centralQBox
theorem centralDen_neg : centralDen.hi<0 := by
  simp only [centralDen,determinantBox,centralPBox,centralQBox]
  nd_eval

def centralAI : RatInterval :=
  rounded (div (determinantBox centralHBox centralQBox) centralDen (Or.inl centralDen_neg))
def centralBI : RatInterval :=
  rounded (div (determinantBox centralPBox centralHBox) centralDen (Or.inl centralDen_neg))

theorem central_coeff_mem :
    centralAI.Mem SourceCentralGeometry.a ∧ centralBI.Mem SourceCentralGeometry.b := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hp (i : Fin 2) : (centralPBox i).Mem (SourceCentralGeometry.nP i) :=
    sub_mem (ndWPointBox_mem hb i) (ndHub0Box_mem hb i)
  have hq (i : Fin 2) : (centralQBox i).Mem (SourceCentralGeometry.nQ i) :=
    sub_mem (ndWPointBox_mem hb i) (ndHub1Box_mem hb i)
  have hh (i : Fin 2) : (centralHBox i).Mem (SourceCentralGeometry.nH i) :=
    sub_mem (ndWPointBox_mem hb i) (ndRingBox_mem hb 6 i)
  exact ⟨rounded_mem (div_mem (det_mem hh hq) (det_mem hp hq) (Or.inl centralDen_neg)),
    rounded_mem (div_mem (det_mem hp hh) (det_mem hp hq) (Or.inl centralDen_neg))⟩

def representativeI (j : Fin 5) (t : Fin 3) : RatInterval :=
  ![![mul (ndBox 7) (SourceBoundarySignBounds.compactA 0),
      mul (ndBox 7) (SourceBoundarySignBounds.compactB 0),neg (ndBox 7)],
    ![mul (ndBox 8) (SourceBoundarySignBounds.compactA 1),
      mul (ndBox 8) (SourceBoundarySignBounds.compactB 1),neg (ndBox 8)],
    ![mul (ndBox 9) (SourceBoundarySignBounds.compactA 2),
      mul (ndBox 9) (SourceBoundarySignBounds.compactB 2),neg (ndBox 9)],
    ![mul (ndBox 10) (SourceBoundarySignBounds.compactA 3),
      mul (ndBox 10) (SourceBoundarySignBounds.compactB 3),neg (ndBox 10)],
    ![neg (ndBox 11),mul (ndBox 11) centralAI,mul (ndBox 11) centralBI]] j t

theorem representativeI_mem (j : Fin 5) (t : Fin 3) :
    (representativeI j t).Mem (representativeCoefficient j t) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have h1 := SourceBoundarySignBounds.compact_membership 0
  have h2 := SourceBoundarySignBounds.compact_membership 1
  have h3 := SourceBoundarySignBounds.compact_membership 2
  have h8 := SourceBoundarySignBounds.compact_membership 3
  change (SourceBoundarySignBounds.compactA 0).Mem (SourceFanLengthCovector.sourceA 1) ∧
    (SourceBoundarySignBounds.compactB 0).Mem (SourceFanLengthCovector.sourceB 1) at h1
  change (SourceBoundarySignBounds.compactA 1).Mem (SourceFanLengthCovector.sourceA 2) ∧
    (SourceBoundarySignBounds.compactB 1).Mem (SourceFanLengthCovector.sourceB 2) at h2
  change (SourceBoundarySignBounds.compactA 2).Mem (SourceFanLengthCovector.sourceA 3) ∧
    (SourceBoundarySignBounds.compactB 2).Mem (SourceFanLengthCovector.sourceB 3) at h3
  change (SourceBoundarySignBounds.compactA 3).Mem (SourceFanLengthCovector.sourceA 8) ∧
    (SourceBoundarySignBounds.compactB 3).Mem (SourceFanLengthCovector.sourceB 8) at h8
  fin_cases j <;> fin_cases t
  all_goals simp only [representativeI,representativeCoefficient,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
  · exact mul_mem (hb 7) h1.1
  · exact mul_mem (hb 7) h1.2
  · exact neg_mem (hb 7)
  · exact mul_mem (hb 8) h2.1
  · exact mul_mem (hb 8) h2.2
  · exact neg_mem (hb 8)
  · exact mul_mem (hb 9) h3.1
  · exact mul_mem (hb 9) h3.2
  · exact neg_mem (hb 9)
  · exact mul_mem (hb 10) h8.1
  · exact mul_mem (hb 10) h8.2
  · exact neg_mem (hb 10)
  · exact neg_mem (hb 11)
  · exact mul_mem (hb 11) central_coeff_mem.1
  · exact mul_mem (hb 11) central_coeff_mem.2

def faceI (f : Fin 9) (t : Fin 3) : RatInterval :=
  div (representativeI (SourceAllFaceBalance.repIndex f) (SourceAllFaceBalance.vertexPerm f t))
    (ofRat (faceOrbitQ (SourceAllFaceBalance.repIndex f)))
    (Or.inr (faceOrbitQ_pos _))

theorem faceI_mem (f : Fin 9) (t : Fin 3) :
    (faceI f t).Mem (SourceSignedStressAssembly.stress (.inr (f,t))) := by
  rw [face_closed]
  have ho := ofRat_mem (faceOrbitQ (SourceAllFaceBalance.repIndex f))
  rw [faceOrbitQ_cast] at ho
  exact div_mem (representativeI_mem _ _) ho (Or.inr (faceOrbitQ_pos _))

def stressI : ResumeLocalIncidence.SourceEdge → RatInterval
  | .inl (k,s) => spokeI k s
  | .inr (f,t) => faceI f t

/-- Unconditional ALL45 actual stress interval membership. No numeric inverse
or contraction/response interval certificate is inferred by this statement. -/
theorem stressI_mem (e : ResumeLocalIncidence.SourceEdge) :
    (stressI e).Mem (SourceSignedStressAssembly.stress e) := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · exact spokeI_mem k s
  · exact faceI_mem f t

end
end N11Formalization.SourceStressIntervals
#check @N11Formalization.SourceStressIntervals.stressI_mem
#print axioms N11Formalization.SourceStressIntervals.stressI_mem
