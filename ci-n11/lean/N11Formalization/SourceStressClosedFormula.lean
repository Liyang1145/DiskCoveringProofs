import N11Formalization.SourceBoundaryStressPositive

/-! Closed formulas for the SAME actual45 stress. Face conversion denominators
cancel exactly against barycentric denominators; spoke radius factors cancel
against the actual boundary multiplier numerator. These identities are for
interval certification, not a new stress or a floating candidate. -/
set_option autoImplicit false
namespace N11Formalization.SourceStressClosedFormula
open N11Formalization SourceFanLengthCovector
noncomputable section

private theorem cancel_face (lam a b c : ℝ) (hc : c≠0) :
    (-lam*c)*(-a/c)=lam*a ∧ (-lam*c)*(-b/c)=lam*b ∧
      (-lam*c)*(1/c)=-lam := by
  constructor
  · field_simp [hc]
  constructor <;> field_simp [hc]

def representativeCoefficient (j : Fin 5) (t : Fin 3) : ℝ :=
  ![![last5 SourceExactRoot.sourceRoot 0*sourceA 1,
      last5 SourceExactRoot.sourceRoot 0*sourceB 1,-last5 SourceExactRoot.sourceRoot 0],
    ![last5 SourceExactRoot.sourceRoot 1*sourceA 2,
      last5 SourceExactRoot.sourceRoot 1*sourceB 2,-last5 SourceExactRoot.sourceRoot 1],
    ![last5 SourceExactRoot.sourceRoot 2*sourceA 3,
      last5 SourceExactRoot.sourceRoot 2*sourceB 3,-last5 SourceExactRoot.sourceRoot 2],
    ![last5 SourceExactRoot.sourceRoot 3*sourceA 8,
      last5 SourceExactRoot.sourceRoot 3*sourceB 8,-last5 SourceExactRoot.sourceRoot 3],
    ![-last5 SourceExactRoot.sourceRoot 4,
      last5 SourceExactRoot.sourceRoot 4*SourceCentralGeometry.a,
      last5 SourceExactRoot.sourceRoot 4*SourceCentralGeometry.b]] j t

theorem representative_cancellation (j : Fin 5) (t : Fin 3) :
    PhysicalInteriorObjective.weight j*SourceRepresentativeFaceBalance.beta j t=
      representativeCoefficient j t := by
  have h1 := cancel_face (last5 SourceExactRoot.sourceRoot 0) (sourceA 1) (sourceB 1)
    (SourceFanConversion.sourceConversion 1)
    (ne_of_gt (SourceFanConversion.sourceConversion_pos 1 (by simp)))
  have h2 := cancel_face (last5 SourceExactRoot.sourceRoot 1) (sourceA 2) (sourceB 2)
    (SourceFanConversion.sourceConversion 2)
    (ne_of_gt (SourceFanConversion.sourceConversion_pos 2 (by simp)))
  have h3 := cancel_face (last5 SourceExactRoot.sourceRoot 2) (sourceA 3) (sourceB 3)
    (SourceFanConversion.sourceConversion 3)
    (ne_of_gt (SourceFanConversion.sourceConversion_pos 3 (by simp)))
  have h8 := cancel_face (last5 SourceExactRoot.sourceRoot 3) (sourceA 8) (sourceB 8)
    (SourceFanConversion.sourceConversion 8)
    (ne_of_gt (SourceFanConversion.sourceConversion_pos 8 (by simp)))
  have hc := cancel_face (last5 SourceExactRoot.sourceRoot 4)
    SourceCentralGeometry.a SourceCentralGeometry.b SourceCentralGeometry.conversion
    (ne_of_gt SourceCentralGeometry.conversion_pos)
  fin_cases j <;> fin_cases t
  all_goals
    simp only [PhysicalInteriorObjective.weight,PhysicalInteriorObjective.conversion,
      SourceRepresentativeFaceBalance.beta,representativeCoefficient,
      SourceFanConversion.betaP,SourceFanConversion.betaQ,SourceFanConversion.betaH,
      SourceCentralGeometry.betaP,SourceCentralGeometry.betaQ,SourceCentralGeometry.betaH,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
  · exact h1.1
  · exact h1.2.1
  · exact h1.2.2
  · exact h2.1
  · exact h2.2.1
  · exact h2.2.2
  · exact h3.1
  · exact h3.2.1
  · exact h3.2.2
  · exact h8.1
  · exact h8.2.1
  · exact h8.2.2
  · exact hc.2.2
  · exact hc.1
  · exact hc.2.1

/-- Actual27 face coefficients, conversion denominator eliminated exactly. -/
theorem face_closed (f : Fin 9) (t : Fin 3) :
    SourceSignedStressAssembly.stress (.inr (f,t))=
      representativeCoefficient (SourceAllFaceBalance.repIndex f)
        (SourceAllFaceBalance.vertexPerm f t)/
          SourceAllFaceBalance.orbitSize (SourceAllFaceBalance.repIndex f) := by
  change (PhysicalInteriorObjective.weight (SourceAllFaceBalance.repIndex f)/
    SourceAllFaceBalance.orbitSize (SourceAllFaceBalance.repIndex f))*
      SourceRepresentativeFaceBalance.beta (SourceAllFaceBalance.repIndex f)
        (SourceAllFaceBalance.vertexPerm f t)=_
  rw [div_mul_eq_mul_div,representative_cancellation]

private theorem succ4 : (4 : Fin 9)+1=5 := by decide

theorem radiusScale_rep (k : Fin 9) :
    SourceBoundaryWeights.radiusScale
      (BoundaryGapConversion.representative (SourceSignedStressAssembly.tieRep k))=
        SourceBoundaryWeights.radiusScale k := by
  fin_cases k <;> simp [SourceBoundaryWeights.radiusScale,
    BoundaryGapConversion.representative,SourceSignedStressAssembly.tieRep,
    SourceBoundaryWeights.slope,rhoK,angleVec,nd_fin_succ_0,nd_fin_succ_1,
    nd_fin_succ_2,nd_fin_succ_3,succ4,nd_fin_succ_5,nd_fin_succ_6,
    nd_fin_succ_7,nd_fin_succ_8] <;> ring

private theorem spoke_left_algebra (R m P Q o : ℝ) (hP : P≠0) (hQ : Q≠0)
    (hPQ : P+Q≠0) (ho : o≠0) :
    ((-m*(R/P+R/Q))/o)*(Q/(P+Q))=(-m*R)/(o*P) := by
  field_simp [hP,hQ,hPQ,ho]
  ring

private theorem spoke_right_algebra (R m P Q o : ℝ) (hP : P≠0) (hQ : Q≠0)
    (hPQ : P+Q≠0) (ho : o≠0) :
    ((-m*(R/P+R/Q))/o)*(1-Q/(P+Q))=(-m*R)/(o*Q) := by
  field_simp [hP,hQ,hPQ,ho]
  ring

theorem spoke_radius_closed (k : Fin 9) (s : Fin 2) :
    SourceSignedStressAssembly.stress (.inl (k,s))=
      (-PhysicalBoundaryStationarity.boundaryMultiplier (SourceSignedStressAssembly.tieRep k)*
        SourceExactRoot.sourceRoot 6)/
      (SourceSignedStressAssembly.tieOrbitSize (SourceSignedStressAssembly.tieRep k)*
        (if s=0 then SourceBoundaryWeights.slope k else SourceBoundaryWeights.slope (k+1))) := by
  change ((-PhysicalBoundaryStationarity.boundaryMultiplier (SourceSignedStressAssembly.tieRep k)*
    SourceBoundaryWeights.radiusScale
      (BoundaryGapConversion.representative (SourceSignedStressAssembly.tieRep k)))/
        SourceSignedStressAssembly.tieOrbitSize (SourceSignedStressAssembly.tieRep k))*
    SourceSignedStressAssembly.split k s=_
  rw [radiusScale_rep]
  have hP := ne_of_gt (SourceBoundaryWeights.slope_pos k)
  have hQ := ne_of_gt (SourceBoundaryWeights.slope_pos (k+1))
  have hPQ := ne_of_gt (add_pos (SourceBoundaryWeights.slope_pos k)
    (SourceBoundaryWeights.slope_pos (k+1)))
  have ho := ne_of_gt (SourceSignedStressAssembly.tieOrbitSize_pos
    (SourceSignedStressAssembly.tieRep k))
  unfold SourceSignedStressAssembly.split
  rw [SourceBoundaryWeights.eta_eq]
  by_cases hs : s=0
  · simp only [hs,ite_true]
    exact spoke_left_algebra _ _ _ _ _ hP hQ hPQ ho
  · simp only [hs,ite_false]
    exact spoke_right_algebra _ _ _ _ _ hP hQ hPQ ho

/-- Actual18 spokes: the SAME genuine numerator, source radius eliminated.
This reduces interval dependencies before solving the actual20-node matrix. -/
theorem spoke_closed (k : Fin 9) (s : Fin 2) :
    SourceSignedStressAssembly.stress (.inl (k,s))=
      -SourceBoundaryMultiplierFormula.numerator (SourceSignedStressAssembly.tieRep k)/
      (SourceSignedStressAssembly.tieOrbitSize (SourceSignedStressAssembly.tieRep k)*
        (if s=0 then SourceBoundaryWeights.slope k else SourceBoundaryWeights.slope (k+1))) := by
  rw [spoke_radius_closed,SourceBoundaryMultiplierFormula.multiplier_numerator]
  have hR : SourceExactRoot.sourceRoot 6≠0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  rw [neg_mul,div_mul_cancel₀ _ hR]

end
end N11Formalization.SourceStressClosedFormula
#check @N11Formalization.SourceStressClosedFormula.face_closed
#check @N11Formalization.SourceStressClosedFormula.spoke_closed
#print axioms N11Formalization.SourceStressClosedFormula.face_closed
#print axioms N11Formalization.SourceStressClosedFormula.spoke_closed
