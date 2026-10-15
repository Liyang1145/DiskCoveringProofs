import N11Formalization.SourceRadialFluxConsumer
import N11Formalization.FlashResponseHessianFlux

/-! Actual source response row sums and hsrc=H0 Hessian identity, consuming
the constructed sourceH columns and the ACTUAL positive radial anchor flux.
No hflux/hrow/H identity premise remains; matrix enclosures and coercivity
are separate obligations. -/
set_option autoImplicit false
namespace N11Formalization.SourceResponseFluxIdentity
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic
open SourceCentreB2Readout SourcePositiveHarmonicConsumer SourceRadialFluxConsumer
noncomputable section

theorem anchorIncidence_same (e : Edge) (j : Fin 9) :
    FlashResponseHessianFlux.anchorIncidence e j=ResumeAnchorFlux.anchorIncidence e j := by
  rcases e with ⟨i,s⟩ | ⟨f,q⟩
  · by_cases hj : anchorIndex i s=j
    · simp [FlashResponseHessianFlux.anchorIncidence,ResumeAnchorFlux.anchorIncidence,hj]
    · simp [FlashResponseHessianFlux.anchorIncidence,ResumeAnchorFlux.anchorIncidence,hj,Ne.symm hj]
  · rfl

theorem harmonic_flux_Flash (j : Fin 9) :
    (∑ e : Edge,(canonicalStress e*FlashResponseHessianFlux.anchorIncidence e j) •
      ResumeDirichlet.edgeVector sourceAnchors
        (fun i => lift sourceH sourceAnchors (.inl i))
        (fun f => lift sourceH sourceAnchors (.inr f)) e)=sourceLoad j • sourceAnchors j := by
  rw [← harmonic_flux_radial j]
  unfold ResumeAnchorFlux.flux
  apply Finset.sum_congr rfl
  intro e _
  rw [anchorIncidence_same,mul_comm]

theorem sourceAnchors_unit (j : Fin 9) : ‖sourceAnchors j‖=1 :=
  FanFoutPos.norm_arcEnd _ _

def sourceAngle (j : Fin 9) : ℝ :=
  arcHiG SourceExactRoot.sourceRoot (FlashRootNetwork.rawOfRing j)

theorem sourceAnchors_circle (j : Fin 9) : sourceAnchors j=circleMap (sourceAngle j) := by
  exact arcEnd_eq_circleMap _ _

def sourceResponse : Fin 9 → Fin 9 → ℝ :=
  ResumeResponseGram.response canonicalStress (coeff sourceH)

/-- Actual source response row sums, not a supplied calibration premise. -/
theorem sourceResponse_rowsum (i : Fin 9) :
    ∑ j : Fin 9,sourceResponse i j*inner ℝ (sourceAnchors i) (sourceAnchors j)=sourceLoad i :=
  FlashResponseHessianFlux.rowsum_eq_rho canonicalStress sourceH sourceAnchors sourceLoad
    sourceH_columns harmonic_flux_Flash sourceAnchors_unit i

theorem sourceResponse_rowsum_pos (i : Fin 9) :
    0 < ∑ j : Fin 9,sourceResponse i j*inner ℝ (sourceAnchors i) (sourceAnchors j) := by
  rw [sourceResponse_rowsum]
  exact sourceLoad_pos i

/-- ACTUAL all-entry hsrc=H0 identity at SAME source, with physical radiality,
row sums and harmonic extension discharged. Not a positive-definiteness claim. -/
theorem actual_hsrc_eq_H0mat :
    FlashResponseHessian.hsrc sourceResponse (fun i => FlashLocal.circleTangent (sourceAngle i))=
      FlashLocal.H0mat sourceResponse sourceLoad (fun i => FlashLocal.circleTangent (sourceAngle i)) :=
  FlashResponseHessianFlux.hsrc_eq_H0mat_closed canonicalStress sourceH sourceAnchors
    sourceAngle sourceLoad sourceH_columns harmonic_flux_Flash
      sourceAnchors_unit sourceAnchors_circle

end
end N11Formalization.SourceResponseFluxIdentity
#check @N11Formalization.SourceResponseFluxIdentity.sourceResponse_rowsum
#check @N11Formalization.SourceResponseFluxIdentity.sourceResponse_rowsum_pos
#check @N11Formalization.SourceResponseFluxIdentity.actual_hsrc_eq_H0mat
#print axioms N11Formalization.SourceResponseFluxIdentity.sourceResponse_rowsum
#print axioms N11Formalization.SourceResponseFluxIdentity.actual_hsrc_eq_H0mat
