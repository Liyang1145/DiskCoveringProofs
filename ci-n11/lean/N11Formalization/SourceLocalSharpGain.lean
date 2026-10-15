import N11Formalization.SourceActualCrossBound
import N11Formalization.SourceActualResponseBound
import N11Formalization.SourceActualCoercivity
import N11Formalization.FlashLocalDirectionalActual

/-! Actual directional remainder and sharp-ball gain for SAME source9R/10
update. Only canonical6 pin/full729/50000 ball are the local domain.
No unknown hdir/cross/force/length/response/N/G/coercivity premise.
Arbitrary Covers topology/all120 patch domain coverage remain separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceLocalSharpGain
open N11Formalization ResumeNetwork ResumeDirichlet ResumeLocalIncidence
open SourceCentreB2Readout SourcePositiveHarmonicConsumer SourceResponseFluxIdentity
open SourceResponsePSDConsumer SourceRadialFluxConsumer SourceResponseKernelConsumer
open SourceRelativeMetric SourceRelativeAdaptiveConsumer SourceRelativeFluxNorms
noncomputable section

def displacedAnchors (x : Fin 9 → ℝ) : Fin 9 → Point :=
  sourceAnchors+FlashLocal.disp sourceAngle x

theorem displacedAnchors_circle (x : Fin 9 → ℝ) (j : Fin 9) :
    displacedAnchors x j=circleMap (sourceAngle j+x j) := by
  simp only [displacedAnchors,Pi.add_apply,FlashLocal.disp,sourceAnchors_circle]
  module

theorem carrying_squared_length (e : Edge) (he : canonicalStress e≠0) :
    (edgeLength sourceAnchors sourceCenters sourceAux e)^2=SourceExactRoot.sourceRadius^2 := by
  classical
  by_cases hs : ∃ s : SourceEdge,edgeMap s=e
  · obtain ⟨s,rfl⟩ := hs
    rw [SourceSharpEnergyCalibration.carrying_edge_length]
  · have hz := SourceAlphaOf.alphaEdge_of_not_mem SourceSignedStressAssembly.stress hs
    exact (he hz).elim

/-- All source/mixed/response/flux/relative/geometry premises instantiated
with true SAME data. The complete directional remainder on the original ball. -/
theorem actual_directional (x : Fin 9 → ℝ) (hp : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,x j^2)≤(729/50000 : ℝ)) :
    (∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j)/2+
      1468*(power x)^2-(179/5000)*(Real.sqrt (∑ j : Fin 9,x j^2))^3-
      ((2/25)/3)*(Real.sqrt (∑ j : Fin 9,x j^2))^4-
      1468*((99/200)*(2/25)+429/50000)*(power x)*
        (Real.sqrt (∑ j : Fin 9,x j^2))^2 ≤
      V2 (displacedAnchors x)-SourceExactRoot.sourceRadius^2 := by
  have hsum : (0 : ℝ)≤∑ j : Fin 9,x j^2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hflux (j : Fin 9) :
      ResumeAnchorFlux.flux canonicalStress sourceAnchors sourceCenters sourceAux j=
        sourceLoad j • circleMap (sourceAngle j) := by
    rw [canonical_flux_radial,sourceAnchors_circle]
  have hU : ∀ j,‖(sourceAnchors+FlashLocal.disp sourceAngle x) j‖≤1 :=
    FlashLocal.hU_of_circle sourceAnchors_circle
  have h := FlashLocal.directional_lower_actual
    (α := canonicalStress) (U := sourceAnchors) (C := sourceCenters) (Z := sourceAux)
    sourceAngle x sourceLoad (N := canonicalN)
    (τ := 1468) (d := 2/25) (A := 429/50000) (B := 99/200)
    (Ccross := 179/5000) (Rstar := SourceExactRoot.sourceRadius)
    (q := Real.sqrt (∑ j : Fin 9,x j^2)) (p := power x) 6 (Λα := Λ)
    SourceBoundaryStressPositive.canonical_nonneg (by norm_num) (by norm_num)
    (power_nonneg x) (by norm_num) (actual_amplitude_gate x hp hr)
    SourceRelativeNormConsumer.canonical_row_bound canonical_mass_zero canonical_force_zero
    canonical_mass_one canonical_free_balance carrying_squared_length hU
    SourceActualResponseBound.actual_anchorWeight (Real.sqrt_nonneg _) (Real.sq_sqrt hsum)
    Λ_energy_eq_source hp Λ_symm Λ_psd (by norm_num)
    SourceActualCrossBound.actual_pinned_operator (fun j => (sourceLoad_pos j).le) hflux
    (by norm_num) (power_sq x) (delta_flux_bound x)
  change (1/2)*(∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j)+
    1468*(power x)^2-(179/5000)*(Real.sqrt (∑ j : Fin 9,x j^2))^3-
    (2/25)*(Real.sqrt (∑ j : Fin 9,x j^2))^4/3-
    1468*((99/200)*(2/25)+429/50000)*(power x)*
      (Real.sqrt (∑ j : Fin 9,x j^2))^2 ≤
      V2 (displacedAnchors x)-SourceExactRoot.sourceRadius^2 at h
  convert h using 1 <;> ring

/-- Actual local oracle gain for ALL directions in the full original pinned
ball. No directional/mixed/coercivity premise; not a proof of patch coverage. -/
theorem actual_local_gain (x : Fin 9 → ℝ) (hp : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,x j^2)≤(729/50000 : ℝ)) :
    (∑ j : Fin 9,x j^2)/100000≤
      V2 (displacedAnchors x)-SourceExactRoot.sourceRadius^2 :=
  SourceActualCoercivity.gain_of_directional _ x hp hr (actual_directional x hp hr)

/-- Actual51-edge feasible witnesses consume the real local gain. All33 face
constraints remain in Feasible, including zero-stress slack faces. -/
theorem feasible_radius_lower (x : Fin 9 → ℝ) (hp : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,x j^2)≤(729/50000 : ℝ))
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (displacedAnchors x) C Z r) :
    SourceExactRoot.sourceRadius≤r := by
  have hg := actual_local_gain x hp hr
  have hu := oracle_le_feasible hf
  have hsum : (0 : ℝ)≤(∑ j : Fin 9,x j^2)/100000 :=
    div_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (by norm_num)
  have hR := SourceExactRoot.sourceRadius_pos
  nlinarith [hf.1]

end
end N11Formalization.SourceLocalSharpGain
#check @N11Formalization.SourceLocalSharpGain.actual_directional
#check @N11Formalization.SourceLocalSharpGain.actual_local_gain
#check @N11Formalization.SourceLocalSharpGain.feasible_radius_lower
#print axioms N11Formalization.SourceLocalSharpGain.actual_local_gain
