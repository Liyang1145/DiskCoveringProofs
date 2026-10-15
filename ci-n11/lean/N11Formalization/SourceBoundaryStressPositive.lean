import N11Formalization.SourceBoundaryIntervalReadout

/-! Strict signs of the actual boundary multipliers and ALL45 actual carrying
stress coefficients. The closed rational inequalities consume the actual
root-expression interval membership and the actual LENGTH derivative bridge.
No numerical multiplier, sign or graph-balance premise is supplied. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundaryStressPositive
open N11Formalization RatInterval SourceBoundaryMultiplierIntervals
open SourceBoundaryIntervalReadout SourceBoundaryMultiplierFormula
noncomputable section

macro "numerator_sign_eval" : tactic =>
  `(tactic|
    (simp only [numeratorBox,fanBox,centralBox,innerBox,normalPBox,normalQBox,normalCBox,
      SourceBoundarySignBounds.contact,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk]
     simp only [nd_fin_succ_1,nd_fin_succ_2,nd_fin_succ_3,nd_fin_succ_8]
     simp [velocityBox,widthQ,directionQ,Fin.ext_iff,
      ring00,ring01,ring10,ring11,ring20,ring21,ring30,ring31,ring40,ring41,
      ring50,ring51,ring60,ring61,ring70,ring71,ring80,ring81,
      pin10,pin11,pin20,pin21,pin30,pin31,pin80,pin81,w0,w1,slope4,
      SourceBoundarySignBounds.compactA,SourceBoundarySignBounds.compactB]
     nd_eval))

theorem numerator_hi_zero : (numeratorBox 0).hi<0 := by numerator_sign_eval
theorem numerator_hi_one : (numeratorBox 1).hi<0 := by numerator_sign_eval
theorem numerator_hi_two : (numeratorBox 2).hi<0 := by numerator_sign_eval
theorem numerator_hi_three : (numeratorBox 3).hi<0 := by numerator_sign_eval
theorem numerator_hi_four : (numeratorBox 4).hi<0 := by numerator_sign_eval

theorem numerator_hi_neg (j : Fin 5) : (numeratorBox j).hi<0 := by
  fin_cases j
  · exact numerator_hi_zero
  · exact numerator_hi_one
  · exact numerator_hi_two
  · exact numerator_hi_three
  · exact numerator_hi_four

/-- All FIVE signs now paid for the actual multipliers; the independent ring4
analytic proof of multiplier3 is retained as a separate calibration. -/
theorem boundaryMultiplier_neg (j : Fin 5) :
    PhysicalBoundaryStationarity.boundaryMultiplier j<0 := by
  have hnum : numerator j<0 := by
    have hhi : ((numeratorBox j).hi : ℝ)<0 := by exact_mod_cast numerator_hi_neg j
    exact lt_of_le_of_lt (mem_le_hi (numeratorBox_mem j)) hhi
  rw [multiplier_numerator]
  exact div_neg_of_neg_of_pos hnum SourceExactRoot.sourceRadius_pos

theorem tieWeight_pos (j : Fin 5) : 0<PhysicalBoundaryStationarity.tieWeight j :=
  mul_pos (neg_pos.mpr (boundaryMultiplier_neg j))
    (SourceBoundaryWeights.radiusScale_pos (BoundaryGapConversion.representative j))

theorem stress_pos (e : ResumeLocalIncidence.SourceEdge) :
    0<SourceSignedStressAssembly.stress e :=
  (SourceSignedStressAssembly.stress_positive_iff.mpr tieWeight_pos) e

theorem canonical_nonneg (e : ResumeNetwork.Edge) :
    0≤SourceCentreB2Readout.canonicalStress e :=
  SourceAlphaOf.alphaEdge_nonneg_of _ (fun s => (stress_pos s).le) e

end
end N11Formalization.SourceBoundaryStressPositive
#check @N11Formalization.SourceBoundaryStressPositive.boundaryMultiplier_neg
#check @N11Formalization.SourceBoundaryStressPositive.tieWeight_pos
#check @N11Formalization.SourceBoundaryStressPositive.stress_pos
#check @N11Formalization.SourceBoundaryStressPositive.canonical_nonneg
#print axioms N11Formalization.SourceBoundaryStressPositive.boundaryMultiplier_neg
#print axioms N11Formalization.SourceBoundaryStressPositive.stress_pos
