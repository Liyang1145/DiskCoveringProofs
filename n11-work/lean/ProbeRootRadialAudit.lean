import N11Formalization
set_option pp.proofs false
set_option pp.explicit true
#print N11Formalization.CoupledRadialFrame.radialFrame
#print N11Formalization.CoupledRadialFrame.slopeA
#print N11Formalization.CoupledRadialFrame.slopeB
#print N11Formalization.CoupledRadialFrame.sourcePoint
#print N11Formalization.CoupledRadialFrame.sourceJacobian
#print N11Formalization.CoupledRadialFrame.sourceInverse_strict_derivative
#check @N11Formalization.CoupledRadialFrame.sourceInverse_apply_image
#check @N11Formalization.RootRadialDualConsumer.objectiveRho_radial_eventually
#check @N11Formalization.RootRadialDualConsumer.sourceInverse_radius_eventually
#check @N11Formalization.RootRadialDualConsumer.sourceRoot_rho_dual
#print axioms N11Formalization.CoupledRadialFrame.sourceInverse_left
#print axioms N11Formalization.CoupledRadialFrame.sourceInverse_right
#print axioms N11Formalization.CoupledRadialFrame.sourceInverse_apply_image
#print axioms N11Formalization.RootRadialDualConsumer.objectiveRho_radial_eventually
#print axioms N11Formalization.RootRadialDualConsumer.sourceInverse_radius_eventually
#print axioms N11Formalization.RootRadialDualConsumer.sourceRoot_rho_dual

namespace N11RadialAudit
open N11Formalization CoupledRadialFrame WidthRadialDerivative
/-- Independent scalar calibration: at zero width and positive radius, rho=1-R. -/
theorem radial_zero_width (R : ℝ) (hR : 0 ≤ R) : rhoMinus R 0 = 1 - R := by
  simp [rhoMinus, Real.sqrt_sq_eq_abs, abs_of_nonneg hR]
/-- The joint radius column is nonzero even where the width diagonal vanishes. -/
theorem radius_column_zero_width (R : ℝ) (hR : 0 < R) : radiusSlope R 0 = -1 := by
  simp [radiusSlope, Real.sqrt_sq_eq_abs, abs_of_pos hR, ne_of_gt hR]
end N11RadialAudit
#print axioms N11RadialAudit.radial_zero_width
#print axioms N11RadialAudit.radius_column_zero_width
