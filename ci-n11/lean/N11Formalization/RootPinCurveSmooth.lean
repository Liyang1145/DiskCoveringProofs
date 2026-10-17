import N11Formalization.RootPinDifferentialConsumer
set_option autoImplicit false
namespace N11Formalization.RootPinCurveSmooth
open N11Formalization
noncomputable section
abbrev TCPoint := Fin 12 → ℝ

private theorem source_rads : ∀ j : Fin 9,
    (SourceExactRoot.sourceRoot 6)^2 - Real.sin (angleVec SourceExactRoot.sourceRoot j)^2 ≠ 0 :=
  fun j => ne_of_gt (SourceWidthNondegenerate.source_radicand_pos j)

theorem source_Uvec_smooth (k : Fin 9) :
    ContDiffAt ℝ 1 (fun u : TCPoint => Uvec u k) SourceExactRoot.sourceRoot := by
  rw [contDiffAt_piLp 2]
  intro i
  fin_cases i
  · exact contDiffAt_UvecX k _ source_rads
  · exact contDiffAt_UvecY k _ source_rads

theorem source_ringCenter_smooth (k : Fin 9) :
    ContDiffAt ℝ 1 (fun u : TCPoint => ringCenter u k) SourceExactRoot.sourceRoot := by
  rw [contDiffAt_piLp 2]
  intro i
  fin_cases i
  · exact contDiffAt_ringCenterX k _ source_rads
  · exact contDiffAt_ringCenterY k _ source_rads

/-- Geometric consumer of the actual source Frechet derivative: given a differentiable
TC curve and any differentiable true equal-circle pin curve through the same source pin,
the true pin velocity is the actual Uvec Frechet derivative applied to the curve velocity.
No Uvec/center/radius derivative hypotheses or neighborhood branch hypotheses remain. -/
theorem source_true_pin_velocity (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    {u : ℝ → TCPoint} {du : TCPoint} {t : ℝ}
    (hu : HasDerivAt u du t) (hroot : u t = SourceExactRoot.sourceRoot)
    {V : ℝ → Point} {v : Point} (hv : HasDerivAt V v t)
    (hV : V t = Uvec SourceExactRoot.sourceRoot k)
    (hvP : ∀ᶠ s in nhds t, ‖V s-ringCenter (u s) k‖^2 = (u s 6)^2)
    (hvQ : ∀ᶠ s in nhds t, ‖V s-ringCenter (u s) (k+1)‖^2 = (u s 6)^2) :
    v = fderiv ℝ (fun z : TCPoint => Uvec z k) SourceExactRoot.sourceRoot du := by
  have hdU := ((source_Uvec_smooth k).differentiableAt (by norm_num)).hasFDerivAt
  have hdP := ((source_ringCenter_smooth k).differentiableAt (by norm_num)).hasFDerivAt
  have hdQ := ((source_ringCenter_smooth (k+1)).differentiableAt (by norm_num)).hasFDerivAt
  have hw := hdU.comp_hasDerivAt_of_eq t hu hroot.symm
  have hp := hdP.comp_hasDerivAt_of_eq t hu hroot.symm
  have hq := hdQ.comp_hasDerivAt_of_eq t hu hroot.symm
  have hr : HasDerivAt (fun s => u s 6) (du 6) t := by
    exact (ContinuousLinearMap.proj (6 : Fin 12) : TCPoint →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hu
  exact (RootPinDifferentialConsumer.source_reflected_curve_derivative_eq k hk hroot hV
    hw hv hp hq hr hu.continuousAt hvP hvQ).symm

end
end N11Formalization.RootPinCurveSmooth
#check @N11Formalization.RootPinCurveSmooth.source_true_pin_velocity
#print axioms N11Formalization.RootPinCurveSmooth.source_true_pin_velocity
