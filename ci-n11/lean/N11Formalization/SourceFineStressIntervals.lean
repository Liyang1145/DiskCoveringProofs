import N11Formalization.SourceRefinedBoundaryIntervals
import N11Formalization.SourceStressIntervals

/-! Finer interval expressions for the SAME actual45 stress. Genuine LENGTH
numerators use paid fine source geometry/normal coefficient inputs. Source
radius factors remain cancelled by the exact closed formula. This pays
membership, not finite common-denominator readouts or downstream coercivity. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineStressIntervals
open N11Formalization RatInterval SourceStressClosedFormula
open SourceRefinedFanCoefficientBounds
noncomputable section

def slopeI (k : Fin 9) : RatInterval :=
  SourceRefinedBoundaryIntervals.fine
    (mul (sinTotLag (ndAngleBox ndBox k)) (ndRhoBox ndBox k))

private theorem slope0 : 0 < (slopeI 0).lo := by
  unfold slopeI SourceRefinedBoundaryIntervals.fine
  nd_eval
private theorem slope1 : 0 < (slopeI 1).lo := by
  unfold slopeI SourceRefinedBoundaryIntervals.fine
  nd_eval
private theorem slope2 : 0 < (slopeI 2).lo := by
  unfold slopeI SourceRefinedBoundaryIntervals.fine
  nd_eval
private theorem slope3 : 0 < (slopeI 3).lo := by
  unfold slopeI SourceRefinedBoundaryIntervals.fine
  nd_eval
private theorem slope4 : 0 < (slopeI 4).lo := by
  unfold slopeI SourceRefinedBoundaryIntervals.fine
  nd_eval

theorem slopeI_pos (k : Fin 9) : 0 < (slopeI k).lo := by
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
  have h := SourceRefinedBoundaryIntervals.fine_mem
    (mul_mem (sinTotLag_mem (ndAngleBox_mem hb k)) (ndRhoBox_mem hb k))
  change (slopeI k).Mem
    (Real.sin (angleVec SourceExactRoot.sourceRoot k)*rhoK SourceExactRoot.sourceRoot k) at h
  simpa only [SourceBoundaryWeights.slope,mul_comm] using h

def spokeDen (k : Fin 9) (s : Fin 2) : RatInterval :=
  mul (ofRat (SourceStressIntervals.tieOrbitQ (SourceSignedStressAssembly.tieRep k)))
    (slopeI (if s=0 then k else k+1))

theorem spokeDen_pos (k : Fin 9) (s : Fin 2) : 0 < (spokeDen k s).lo := by
  let l : Fin 9 := if s=0 then k else k+1
  have hm := slopeI_mem l
  have hv : (slopeI l).lo ≤ (slopeI l).hi :=
    Rat.cast_le.mp (hm.1.trans hm.2)
  have hl := slopeI_pos l
  have hh := hl.trans_le hv
  have ho := SourceStressIntervals.tieOrbitQ_pos (SourceSignedStressAssembly.tieRep k)
  change 0 < min
    (min (SourceStressIntervals.tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).lo)
      (SourceStressIntervals.tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).hi))
    (min (SourceStressIntervals.tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).lo)
      (SourceStressIntervals.tieOrbitQ (SourceSignedStressAssembly.tieRep k)*(slopeI l).hi))
  exact lt_min (lt_min (mul_pos ho hl) (mul_pos ho hh))
    (lt_min (mul_pos ho hl) (mul_pos ho hh))

def spokeI (k : Fin 9) (s : Fin 2) : RatInterval :=
  div (neg (SourceRefinedBoundaryIntervals.numeratorBox (SourceSignedStressAssembly.tieRep k)))
    (spokeDen k s) (Or.inr (spokeDen_pos k s))

theorem spokeI_mem (k : Fin 9) (s : Fin 2) :
    (spokeI k s).Mem (SourceSignedStressAssembly.stress (.inl (k,s))) := by
  rw [spoke_closed]
  have hd := mul_mem
    (ofRat_mem (SourceStressIntervals.tieOrbitQ (SourceSignedStressAssembly.tieRep k)))
    (slopeI_mem (if s=0 then k else k+1))
  rw [SourceStressIntervals.tieOrbitQ_cast] at hd
  have he : SourceBoundaryWeights.slope (if s=0 then k else k+1) =
      if s=0 then SourceBoundaryWeights.slope k else SourceBoundaryWeights.slope (k+1) := by
    split_ifs <;> rfl
  rw [he] at hd
  exact div_mem (neg_mem (SourceRefinedBoundaryIntervals.numeratorBox_mem _)) hd
    (Or.inr (spokeDen_pos k s))

def representativeI (j : Fin 5) (t : Fin 3) : RatInterval :=
  ![![mul (ndBox 7) (ABox 0),mul (ndBox 7) (BBox 0),neg (ndBox 7)],
    ![mul (ndBox 8) (ABox 1),mul (ndBox 8) (BBox 1),neg (ndBox 8)],
    ![mul (ndBox 9) (ABox 2),mul (ndBox 9) (BBox 2),neg (ndBox 9)],
    ![mul (ndBox 10) (ABox 3),mul (ndBox 10) (BBox 3),neg (ndBox 10)],
    ![neg (ndBox 11),mul (ndBox 11) SourceStressIntervals.centralAI,
      mul (ndBox 11) SourceStressIntervals.centralBI]] j t

theorem representativeI_mem (j : Fin 5) (t : Fin 3) :
    (representativeI j t).Mem (representativeCoefficient j t) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have h1 := refined_membership 0
  have h2 := refined_membership 1
  have h3 := refined_membership 2
  have h8 := refined_membership 3
  change (ABox 0).Mem (SourceFanLengthCovector.sourceA 1) ∧
    (BBox 0).Mem (SourceFanLengthCovector.sourceB 1) at h1
  change (ABox 1).Mem (SourceFanLengthCovector.sourceA 2) ∧
    (BBox 1).Mem (SourceFanLengthCovector.sourceB 2) at h2
  change (ABox 2).Mem (SourceFanLengthCovector.sourceA 3) ∧
    (BBox 2).Mem (SourceFanLengthCovector.sourceB 3) at h3
  change (ABox 3).Mem (SourceFanLengthCovector.sourceA 8) ∧
    (BBox 3).Mem (SourceFanLengthCovector.sourceB 8) at h8
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
  · exact mul_mem (hb 11) SourceStressIntervals.central_coeff_mem.1
  · exact mul_mem (hb 11) SourceStressIntervals.central_coeff_mem.2

def faceI (f : Fin 9) (t : Fin 3) : RatInterval :=
  div (representativeI (SourceAllFaceBalance.repIndex f) (SourceAllFaceBalance.vertexPerm f t))
    (ofRat (SourceStressIntervals.faceOrbitQ (SourceAllFaceBalance.repIndex f)))
    (Or.inr (SourceStressIntervals.faceOrbitQ_pos _))

theorem faceI_mem (f : Fin 9) (t : Fin 3) :
    (faceI f t).Mem (SourceSignedStressAssembly.stress (.inr (f,t))) := by
  rw [face_closed]
  have ho := ofRat_mem (SourceStressIntervals.faceOrbitQ (SourceAllFaceBalance.repIndex f))
  rw [SourceStressIntervals.faceOrbitQ_cast] at ho
  exact div_mem (representativeI_mem _ _) ho
    (Or.inr (SourceStressIntervals.faceOrbitQ_pos _))

def stressI : ResumeLocalIncidence.SourceEdge → RatInterval
  | .inl (k,s) => spokeI k s
  | .inr (f,t) => faceI f t

/-- ALL45 memberships of SAME stress in the finer expression boxes. -/
theorem stressI_mem (e : ResumeLocalIncidence.SourceEdge) :
    (stressI e).Mem (SourceSignedStressAssembly.stress e) := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · exact spokeI_mem k s
  · exact faceI_mem f t

end
end N11Formalization.SourceFineStressIntervals
#check @N11Formalization.SourceFineStressIntervals.stressI_mem
#print axioms N11Formalization.SourceFineStressIntervals.stressI_mem
