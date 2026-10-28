import N11Formalization
set_option autoImplicit false
open N11Formalization ResumeNetwork ResumeDirichlet ResumeLocalIncidence
open SourceRelativeFluxGeometry SourceRelativeFluxNorms SourceRelativeAdaptiveConsumer

#print SourceRelativeMetric.R
#print SourceRelativeFluxGeometry.F
#print SourceRelativeFluxGeometry.G
#print SourceRelativeFluxNorms.updatedStress
#check @SourceRelativeFluxGeometry.flux_source_spokes
#check @SourceRelativeFluxGeometry.G_flux
#check @SourceRelativeFluxPacket.FB_contains
#check @SourceRelativeFluxPacket.GB_contains
#check @SourceRelativeFluxPacket.flux_readout
#check @SourceRelativeFluxPacket.G_readout
#check @SourceRelativeFluxNorms.canonicalFluxBox_mem
#check @SourceRelativeFluxNorms.canonicalGBox_mem
#check @SourceRelativeFluxNorms.pin_source
#check @SourceRelativeFluxNorms.actual_flux_norm
#check @SourceRelativeFluxNorms.actual_pinned_G_norm
#check @SourceRelativeFluxNorms.actual_amplitude_gate
#check @SourceRelativeFluxNorms.delta_flux_bound
#check @SourceRelativeFluxNorms.updated_mass_one
#check @SourceRelativeFluxNorms.updated_nonneg
#check @SourceRelativeFluxNorms.updated_force_zero
#check @SourceRelativeFluxNorms.updated_root_value
#print axioms SourceRelativeFluxGeometry.flux_source_spokes
#print axioms SourceRelativeFluxGeometry.G_flux
#print axioms SourceRelativeFluxNorms.actual_flux_norm
#print axioms SourceRelativeFluxNorms.actual_pinned_G_norm
#print axioms SourceRelativeFluxNorms.actual_amplitude_gate
#print axioms SourceRelativeFluxNorms.delta_flux_bound
#print axioms SourceRelativeFluxNorms.updated_nonneg
#print axioms SourceRelativeFluxNorms.updated_force_zero
#print axioms SourceRelativeFluxNorms.updated_root_value

-- Actual72 flux/32 pinnedG inputs, not an approximate Schur/N replacement.
example (a : Fin 4) (j : Fin 9) (c : Fin 2) :
    (canonicalFluxBox a j c).Mem ((F a j).ofLp c) :=
  canonicalFluxBox_mem a j c
example (i : Fin 8) (a : Fin 4) :
    (canonicalGBox i a).Mem (G ((6 : Fin 9).succAbove i) a) :=
  canonicalGBox_mem i a

example (x : Fin 9 → ℝ) (hpin : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,(x j)^2) ≤ (729/50000 : ℝ)) :
    1468*(99/200)*(power x)<1 := actual_amplitude_gate x hpin hr

example (x : Fin 9 → ℝ) (hpin : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,(x j)^2) ≤ (729/50000 : ℝ)) :
    (∀ e : Edge,0 ≤ updatedStress x e) ∧ (∑ e : Edge,updatedStress x e)=1 :=
  ⟨updated_nonneg x hpin hr,updated_mass_one x⟩

example (x : Fin 9 → ℝ) (v : Free) :
    ∑ e : Edge,(updatedStress x e*incidence e v) • SourceRelativeAdaptiveConsumer.D e=0 :=
  updated_force_zero x v

example (x : Fin 9 → ℝ) (hpin : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,(x j)^2) ≤ (729/50000 : ℝ)) :
    dirichletEnergy (updatedStress x) SourcePositiveHarmonicConsumer.sourceAnchors =
      SourceExactRoot.sourceRadius^2 := updated_root_value x hpin hr

-- Zero update control at the original source, sourceRadius still root6.
example (e : Edge) : updatedStress 0 e=SourceCentreB2Readout.canonicalStress e := by
  simp [updatedStress,delta,FlashLocal.Qx,FlashLocal.GtX]

-- Distinct representation calibration: factor2 is required by G=TN;
-- with v=t=(1,0), flux inner1 produces G2, not G1.
example : (2 : ℝ)*inner ℝ (!₂[1,0] : Point) (!₂[1,0] : Point)=2 ∧
    (2 : ℝ)*inner ℝ (!₂[1,0] : Point) (!₂[1,0] : Point)≠1 := by
  simp only [PinTangentGeometry.inner_coords]
  norm_num

-- Pin permutation is not identity and can't be silently omitted.
example : ResumePinnedMatrixReindex.pinEquiv (0 : Fin 8)=2 := rfl
example : siteMap (8 : Fin 9)=6 := by decide
example : siteMap (6 : Fin 9)≠6 := by decide
example : SourceN2.srcFaceSite2 (SourceN2.faceFlat 0 1)=(9 : Fin 11) := by decide
example : SourceN2.srcFaceSite2 (SourceN2.faceFlat 0 2)=(10 : Fin 11) := by decide

example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceExactRoot.source_attainment
