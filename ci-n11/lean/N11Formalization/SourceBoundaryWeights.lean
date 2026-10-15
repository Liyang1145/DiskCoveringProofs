import N11Formalization.SourceBoundaryTieDerivative

/-! Actual source unit-circle tie weights: eta lies strictly between0 and1,
and the candidate gap/radius conversion scale is positive. The sine/rho
identities refer to actual arcEnd branches, including the wrap8→0 tie.
The GAP gradient-to-radius identity is still a separate consumer obligation. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundaryWeights
open N11Formalization PinTangentGeometry SourceBoundaryTieDerivative
noncomputable section

private theorem det_circle_smul (r s t : ℝ) :
    det (circleMap s) (r • circleMap t)=r*Real.sin (t-s) := by
  rw [Real.sin_sub]
  unfold det circleMap
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,PiLp.smul_apply,smul_eq_mul]
  ring

private theorem det_sub_right (p q r : Point) :
    det p (q-r)=det p q-det p r := by
  unfold det
  simp only [PiLp.sub_apply]
  ring
private theorem det_self (p : Point) : det p p=0 := by unfold det; ring

def slope (k : Fin 9) : ℝ :=
  rhoK SourceExactRoot.sourceRoot k*Real.sin (angleVec SourceExactRoot.sourceRoot k)

theorem slope_pos (k : Fin 9) : 0<slope k := by
  have ha := SourceWidthNondegenerate.source_width_bounds k
  exact mul_pos (CartesianPolarFrame.source_rho_pos k)
    (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2,Real.pi_pos]))

theorem left_tangent_row (k : Fin 9) : det (T k) (nP k)=slope k := by
  rw [nP,det_sub_right,det_self,zero_sub]
  change -det (arcEnd SourceExactRoot.sourceRoot k) (ringCenter SourceExactRoot.sourceRoot k)=_
  rw [arcEnd_eq_circleMap,ringCenter_eq_smul,det_circle_smul]
  rw [show thetaOf (angleVec SourceExactRoot.sourceRoot) k -
    (thetaOf (angleVec SourceExactRoot.sourceRoot) k+angleVec SourceExactRoot.sourceRoot k)=
    -angleVec SourceExactRoot.sourceRoot k from by ring,Real.sin_neg]
  change -(rhoK SourceExactRoot.sourceRoot k * -Real.sin (angleVec SourceExactRoot.sourceRoot k))=_
  simp only [slope,mul_neg,neg_neg]

theorem right_tangent_row (k : Fin 9) : det (T k) (nQ k)=-slope (k+1) := by
  rw [nQ,det_sub_right,det_self,zero_sub]
  change -det (arcEnd SourceExactRoot.sourceRoot k) (ringCenter SourceExactRoot.sourceRoot (k+1))=_
  rw [arcEnd_eq_circleMap_arcLo_succ,ringCenter_eq_smul,det_circle_smul]
  rw [show thetaOf (angleVec SourceExactRoot.sourceRoot) (k+1) -
      (thetaOf (angleVec SourceExactRoot.sourceRoot) (k+1) -
        angleVec SourceExactRoot.sourceRoot (k+1))=angleVec SourceExactRoot.sourceRoot (k+1) from by
    ring]
  rfl

theorem source_denominator (k : Fin 9) :
    det (T k) (SourceBoundaryTieDerivative.D k)=slope k+slope (k+1) := by
  have he : det (T k) (SourceBoundaryTieDerivative.D k)=det (T k) (nP k)-det (T k) (nQ k) := by
    unfold SourceBoundaryTieDerivative.D nP nQ det
    simp only [PiLp.sub_apply]
    ring
  rw [he,left_tangent_row,right_tangent_row,sub_neg_eq_add]

theorem eta_eq (k : Fin 9) : eta k=slope (k+1)/(slope k+slope (k+1)) := by
  rw [eta,right_tangent_row,source_denominator,neg_neg]

theorem eta_bounds (k : Fin 9) : 0<eta k ∧ eta k<1 := by
  rw [eta_eq]
  have hp := slope_pos k
  have hq := slope_pos (k+1)
  have hd := add_pos hp hq
  exact ⟨div_pos hq hd,(div_lt_one hd).mpr (by linarith)⟩

def radiusScale (k : Fin 9) : ℝ :=
  SourceExactRoot.sourceRoot 6/slope k+SourceExactRoot.sourceRoot 6/slope (k+1)

theorem radiusScale_pos (k : Fin 9) : 0<radiusScale k :=
  add_pos (div_pos SourceExactRoot.sourceRadius_pos (slope_pos k))
    (div_pos SourceExactRoot.sourceRadius_pos (slope_pos (k+1)))

/-- Explicit coupled-inverse R coefficient; no fixed-R simplification. -/
theorem inverse_width_radius_slope (k : Fin 9) :
    -CoupledRadialFrame.radiusSlope (SourceExactRoot.sourceRoot 6)
        (angleVec SourceExactRoot.sourceRoot k) /
        WidthRadialDerivative.widthSlope (SourceExactRoot.sourceRoot 6)
          (angleVec SourceExactRoot.sourceRoot k) =
      SourceExactRoot.sourceRoot 6/slope k := by
  have hroot : Real.sqrt ((SourceExactRoot.sourceRoot 6)^2-
      Real.sin (angleVec SourceExactRoot.sourceRoot k)^2)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr (SourceWidthNondegenerate.source_radicand_pos k))
  have hs : slope k≠0 := ne_of_gt (slope_pos k)
  have hn : Real.sin (angleVec SourceExactRoot.sourceRoot k) *
      WidthRadialDerivative.rhoMinus (SourceExactRoot.sourceRoot 6)
        (angleVec SourceExactRoot.sourceRoot k) = slope k := by
    unfold slope WidthRadialDerivative.rhoMinus rhoK
    ring
  unfold CoupledRadialFrame.radiusSlope WidthRadialDerivative.widthSlope
  rw [hn]
  change -(-SourceExactRoot.sourceRoot 6/
      Real.sqrt ((SourceExactRoot.sourceRoot 6)^2-
        Real.sin (angleVec SourceExactRoot.sourceRoot k)^2)) /
      (slope k/Real.sqrt ((SourceExactRoot.sourceRoot 6)^2-
        Real.sin (angleVec SourceExactRoot.sourceRoot k)^2)) =
      SourceExactRoot.sourceRoot 6/slope k
  field_simp [hs,hroot]

end
end N11Formalization.SourceBoundaryWeights
#check @N11Formalization.SourceBoundaryWeights.eta_bounds
#check @N11Formalization.SourceBoundaryWeights.radiusScale_pos
#check @N11Formalization.SourceBoundaryWeights.inverse_width_radius_slope
#print axioms N11Formalization.SourceBoundaryWeights.eta_bounds
