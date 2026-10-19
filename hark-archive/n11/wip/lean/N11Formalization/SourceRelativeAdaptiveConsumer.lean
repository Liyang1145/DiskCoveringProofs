import N11Formalization.SourceRelativeNormConsumer
import N11Formalization.SourceResponseFluxIdentity
import N11Formalization.ResumeAdaptiveRows
import N11Formalization.ResumeAdaptiveBalance

/-! Actual adaptive Qx consumer of the SAME9R/10 transformed columns.
All directions are arbitrary Fin9 reals; no pin/local radius is hidden.
No G bound, positivity for arbitrary x, coercivity or global cover theorem. -/
set_option autoImplicit false
namespace N11Formalization.SourceRelativeAdaptiveConsumer
open N11Formalization ResumeNetwork ResumeDirichlet
open SourceRelativeMetric SourceRelativeNormConsumer SourceResponseFluxIdentity
noncomputable section

def D (e : Edge) : Point :=
  edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
    (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
    (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e

def tangent (j : Fin 9) : Point := FlashLocal.circleTangent (sourceAngle j)

def power (x : Fin 9 → ℝ) : ℝ :=
  Real.sqrt (∑ a : Fin 4,
    (FlashLocal.GtX ResumeAnchorFlux.anchorIncidence D tangent canonicalN x a)^2)

theorem power_nonneg (x : Fin 9 → ℝ) : 0 ≤ power x := Real.sqrt_nonneg _
theorem power_sq (x : Fin 9 → ℝ) :
    (power x)^2 = ∑ a : Fin 4,
      (FlashLocal.GtX ResumeAnchorFlux.anchorIncidence D tangent canonicalN x a)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))

def delta (x : Fin 9 → ℝ) (e : Edge) : ℝ :=
  FlashLocal.Qx ResumeAnchorFlux.anchorIncidence D tangent canonicalN 1468 x e

/-- Real updated-stress consumer of the proved relative N-row norm,
not a wrapper with an unpaid hrow premise. -/
theorem delta_relative (x : Fin 9 → ℝ) (e : Edge) :
    |delta x e| ≤ (1468*(99/200)*(power x))*SourceCentreB2Readout.canonicalStress e :=
  ResumeAdaptiveRows.Qx_relative ResumeAnchorFlux.anchorIncidence D tangent canonicalN x
    SourceCentreB2Readout.canonicalStress (by norm_num) (power_nonneg x)
    (power_sq x) canonical_row_bound e

theorem delta_mass_zero (x : Fin 9 → ℝ) : ∑ e : Edge,delta x e=0 :=
  ResumeAdaptiveRows.Qx_sum_zero ResumeAnchorFlux.anchorIncidence D tangent canonicalN x
    1468 canonical_mass_zero

theorem delta_force_zero (x : Fin 9 → ℝ) (v : Free) :
    ∑ e : Edge, (delta x e*incidence e v) • D e=0 :=
  ResumeAdaptiveBalance.Qx_balance ResumeAnchorFlux.anchorIncidence D tangent canonicalN x
    1468 canonical_force_zero v

end
end N11Formalization.SourceRelativeAdaptiveConsumer
#check @N11Formalization.SourceRelativeAdaptiveConsumer.delta_relative
#check @N11Formalization.SourceRelativeAdaptiveConsumer.delta_mass_zero
#check @N11Formalization.SourceRelativeAdaptiveConsumer.delta_force_zero
#print axioms N11Formalization.SourceRelativeAdaptiveConsumer.delta_relative
#print axioms N11Formalization.SourceRelativeAdaptiveConsumer.delta_force_zero
