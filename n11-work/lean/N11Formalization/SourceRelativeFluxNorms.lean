import N11Formalization.SourceRelativeFluxPacket
import N11Formalization.FlashLocalFrobeniusEnclosure
import N11Formalization.SourceSharpEnergyCalibration
import N11Formalization.ResumeAdaptiveRoot

/-! SAME9R/10 actual flux/G norms and amplitude gate.
No flux/G/membership/norm premise. The source/canonical pin is explicitly
transported. Actual augmented-H0/G coercivity remains a separate obligation. -/
set_option autoImplicit false
namespace N11Formalization.SourceRelativeFluxNorms
open N11Formalization RatInterval ResumeLocalIncidence
open SourceRelativeFluxGeometry SourceRelativeFluxPacket
open SourceRelativeMetric SourceRelativeAdaptiveConsumer
open ResumePinnedMatrixReindex
noncomputable section

private theorem FB_hi (k : Fin 9) (a : Fin 4) (c : Fin 2) :
    (FB k a c).abs.hi = (fmag k a c : ℚ)/1000000000 := by
  simp only [FB,intv,RatInterval.abs,fmag,Int.cast_max,Int.cast_neg]
  rw [← neg_div,max_div_div_right (by norm_num : (0 : ℚ) ≤ 1000000000)]

private theorem GB_hi (k : Fin 9) (a : Fin 4) :
    (GB k a).abs.hi = (gmag k a : ℚ)/1000000000 := by
  simp only [GB,intv,RatInterval.abs,gmag,Int.cast_max,Int.cast_neg]
  rw [← neg_div,max_div_div_right (by norm_num : (0 : ℚ) ≤ 1000000000)]

theorem flux_box_certificate :
    (∑ k : Fin 9,∑ a : Fin 4,∑ c : Fin 2,(FB k a c).abs.hi^2) ≤
      (429/50000 : ℚ)^2 := by
  have h : (∑ k : Fin 9,∑ a : Fin 4,∑ c : Fin 2,(fmag k a c : ℚ)^2) ≤
      (429 : ℚ)^2*400000000 := by exact_mod_cast flux_readout
  have hs := div_le_div_of_nonneg_right h
    (by norm_num : (0 : ℚ) ≤ 1000000000000000000)
  simp only [FB_hi,div_pow,Finset.sum_div]
  norm_num at hs ⊢
  simp only [Finset.sum_div,add_div] at hs
  exact hs

theorem G_box_certificate :
    (∑ k : Fin 8,∑ a : Fin 4,(GB (Fin.castSucc k) a).abs.hi^2) ≤
      (15363/1000000 : ℚ)^2 := by
  have h : (∑ k : Fin 8,∑ a : Fin 4,(gmag (Fin.castSucc k) a : ℚ)^2) ≤
      (15363 : ℚ)^2*1000000 := by exact_mod_cast G_readout
  have hs := div_le_div_of_nonneg_right h
    (by norm_num : (0 : ℚ) ≤ 1000000000000000000)
  simp only [GB_hi,div_pow,Finset.sum_div]
  norm_num at hs ⊢
  simp only [Finset.sum_div] at hs
  exact hs

private theorem raw_sum (f : Fin 9 → ℝ) :
    (∑ k : Fin 9,f (siteMap k))=∑ j : Fin 9,f j :=
  canonRawEquiv.symm.sum_comp f

theorem flux_squared_raw (a : Fin 4) :
    (FlashLocal.frob (F a))^2 =
      ∑ k : Fin 9,∑ c : Fin 2,((F a (siteMap k)).ofLp c)^2 := by
  rw [FlashLocal.frob,Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  have h := raw_sum (fun j : Fin 9 => ‖F a j‖^2)
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _
  rw [PinTangentGeometry.norm_sq_coords,Fin.sum_univ_two]

/-- Actual72 coordinate inputs consumed into the REAL adaptive flux norm.
No hFsq/membership/numeric/readout premise. -/
theorem actual_flux_norm :
    (∑ a : Fin 4,(FlashLocal.frob (F a))^2) ≤ (429/50000 : ℝ)^2 := by
  have h := FlashLocal.sum_sq_le_of_boxes
    (fun t : Fin 9 × (Fin 4 × Fin 2) => ((F t.2.1 (siteMap t.1)).ofLp t.2.2))
    (fun t : Fin 9 × (Fin 4 × Fin 2) => FB t.1 t.2.1 t.2.2)
    (fun t => FB_mem t.1 t.2.1 t.2.2)
  have hc : ((∑ k : Fin 9,∑ a : Fin 4,∑ c : Fin 2,(FB k a c).abs.hi^2 : ℚ) : ℝ) ≤
      (429/50000 : ℝ)^2 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr flux_box_certificate
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using hcast
  simp only [Fintype.sum_prod_type] at h
  simp_rw [flux_squared_raw]
  rw [Finset.sum_comm]
  exact h.trans hc

def canonicalFluxBox (a : Fin 4) (j : Fin 9) (c : Fin 2) : RatInterval :=
  FB (canonRawEquiv j) a c

theorem canonicalFluxBox_mem (a : Fin 4) (j : Fin 9) (c : Fin 2) :
    (canonicalFluxBox a j c).Mem ((F a j).ofLp c) := by
  have h := FB_mem (canonRawEquiv j) a c
  have he : siteMap (canonRawEquiv j)=j := canonRawEquiv.symm_apply_apply j
  rw [he] at h
  exact h

theorem pin_source (i : Fin 8) :
    siteMap (Fin.castSucc (pinEquiv i))=(6 : Fin 9).succAbove i := by
  fin_cases i <;> decide

def canonicalGBox (i : Fin 8) (a : Fin 4) : RatInterval :=
  GB (Fin.castSucc (pinEquiv i)) a

/-- Exact raw8→canonical6 pin consumer for all32 actualG entries. -/
theorem canonicalGBox_mem (i : Fin 8) (a : Fin 4) :
    (canonicalGBox i a).Mem (G ((6 : Fin 9).succAbove i) a) := by
  have h := GB_mem (Fin.castSucc (pinEquiv i)) a
  rw [pin_source] at h
  exact h

theorem canonical_G_box_certificate :
    (∑ i : Fin 8,∑ a : Fin 4,(canonicalGBox i a).abs.hi^2) ≤
      (15363/1000000 : ℚ)^2 := by
  have h := pinEquiv.sum_comp (fun i : Fin 8 =>
    ∑ a : Fin 4,(GB (Fin.castSucc i) a).abs.hi^2)
  change (∑ i : Fin 8,∑ a : Fin 4,
    (GB (Fin.castSucc (pinEquiv i)) a).abs.hi^2) ≤ _
  rw [h]
  exact G_box_certificate

/-- ALL32 actual pinnedG coefficients with correct canonical6 pin.
No hG/membership/Frobenius premise, no old metric's norms assumed. -/
theorem actual_pinned_G_norm :
    (∑ i : Fin 8,∑ a : Fin 4,(G ((6 : Fin 9).succAbove i) a)^2) ≤
      (15363/1000000 : ℝ)^2 := by
  exact FlashLocal.hgFrob_of_boxes
    ResumeAnchorFlux.anchorIncidence SourceRelativeAdaptiveConsumer.D
    SourceRelativeAdaptiveConsumer.tangent canonicalN 6 canonicalGBox
    canonical_G_box_certificate canonicalGBox_mem

/-- REAL amplitude gate of THIS actual Qx update throughout the pinned ball.
Pin and radius are the domain, not quantitative G/hrow premises. -/
theorem actual_amplitude_gate (x : Fin 9 → ℝ) (hpin : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,(x j)^2) ≤ (729/50000 : ℝ)) :
    1468*(99/200)*(power x) < 1 := by
  have hsum : (0 : ℝ) ≤ ∑ j : Fin 9,(x j)^2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hg := FlashLocal.gtX_norm_le_frobenius_pinned
    (6 : Fin 9) G x (by norm_num) actual_pinned_G_norm
    (Real.sqrt_nonneg _) (Real.sq_sqrt hsum)
    (power_nonneg x) (power_sq x) hpin
  have h1 : power x ≤ (15363/1000000 : ℝ)*(729/50000) :=
    hg.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
  have h2 := mul_le_mul_of_nonneg_left h1
    (by norm_num : (0 : ℝ) ≤ 1468*(99/200))
  exact h2.trans_lt (by norm_num)

/-- Actual update-flux loss input, for arbitrary directions, no hFsq supplied. -/
theorem delta_flux_bound (x : Fin 9 → ℝ) :
    FlashLocal.frob (ResumeAnchorFlux.flux (delta x)
      SourcePositiveHarmonicConsumer.sourceAnchors
      SourcePositiveHarmonicConsumer.sourceCenters
      SourcePositiveHarmonicConsumer.sourceAux) ≤
        1468*(429/50000)*(power x) :=
  FlashLocal.frob_flux_Qx_le ResumeAnchorFlux.anchorIncidence
    SourceRelativeAdaptiveConsumer.D SourceRelativeAdaptiveConsumer.tangent
    canonicalN 1468 x SourcePositiveHarmonicConsumer.sourceAnchors
    SourcePositiveHarmonicConsumer.sourceCenters SourcePositiveHarmonicConsumer.sourceAux
    (by norm_num) (by norm_num) (power_nonneg x) (power_sq x) actual_flux_norm

def updatedStress (x : Fin 9 → ℝ) (e : ResumeNetwork.Edge) : ℝ :=
  SourceCentreB2Readout.canonicalStress e+delta x e

theorem updated_mass_one (x : Fin 9 → ℝ) : ∑ e,updatedStress x e=1 := by
  simp only [updatedStress,Finset.sum_add_distrib,
    SourceCentreB2Readout.canonical_mass_one,delta_mass_zero,add_zero]

/-- Actual stress nonnegativity over the stated pinned ball.
No unpaid G/hrow/amplitude premise remains. This is not coercivity. -/
theorem updated_nonneg (x : Fin 9 → ℝ) (hpin : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,(x j)^2) ≤ (729/50000 : ℝ))
    (e : ResumeNetwork.Edge) : 0 ≤ updatedStress x e := by
  have hg := actual_amplitude_gate x hpin hr
  have hd := (abs_le.mp (delta_relative x e)).1
  have hslack : 0 ≤ (1-1468*(99/200)*(power x))*
      SourceCentreB2Readout.canonicalStress e :=
    mul_nonneg (by linarith) (SourceBoundaryStressPositive.canonical_nonneg e)
  unfold updatedStress
  nlinarith only [hd,hslack]

theorem updated_force_zero (x : Fin 9 → ℝ) (v : ResumeDirichlet.Free) :
    ∑ e : ResumeNetwork.Edge,(updatedStress x e*ResumeDirichlet.incidence e v) •
      SourceRelativeAdaptiveConsumer.D e=0 := by
  have ha := SourceCentreB2Readout.canonical_free_balance v
  have hd := delta_force_zero x v
  change (∑ e : ResumeNetwork.Edge,
    (SourceCentreB2Readout.canonicalStress e*ResumeDirichlet.incidence e v) •
      SourceRelativeAdaptiveConsumer.D e)=0 at ha
  simp only [updatedStress,add_mul,add_smul,Finset.sum_add_distrib]
  rw [ha,hd,add_zero]

theorem delta_zero_on_zero_stress (x : Fin 9 → ℝ) (e : ResumeNetwork.Edge)
    (he : SourceCentreB2Readout.canonicalStress e=0) : delta x e=0 := by
  have h := delta_relative x e
  rw [he,mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

private theorem source_carrying_length (e : ResumeNetwork.Edge)
    (he : SourceCentreB2Readout.canonicalStress e≠0) :
    (ResumeNetwork.edgeLength SourcePositiveHarmonicConsumer.sourceAnchors
      SourcePositiveHarmonicConsumer.sourceCenters SourcePositiveHarmonicConsumer.sourceAux e)^2 =
        SourceExactRoot.sourceRadius^2 := by
  classical
  by_cases hs : ∃ s : ResumeLocalIncidence.SourceEdge,ResumeLocalIncidence.edgeMap s=e
  · obtain ⟨s,rfl⟩ := hs
    rw [SourceSharpEnergyCalibration.carrying_edge_length]
  · have hz := SourceAlphaOf.alphaEdge_of_not_mem SourceSignedStressAssembly.stress hs
    exact (he hz).elim

/-- Actual varied stress still minimizes at the SAME source datum and has
exact value sourceRadius². No displaced-minimizer, force, length or mass
premise; pin and ball radius are the explicit domain. Not patch coercivity. -/
theorem updated_root_value (x : Fin 9 → ℝ) (hpin : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,(x j)^2) ≤ (729/50000 : ℝ)) :
    ResumeNetwork.dirichletEnergy (updatedStress x)
      SourcePositiveHarmonicConsumer.sourceAnchors = SourceExactRoot.sourceRadius^2 := by
  exact ResumeAdaptiveRoot.adaptive_root_value
    (α := SourceCentreB2Readout.canonicalStress) (δ := delta x)
    (U := SourcePositiveHarmonicConsumer.sourceAnchors)
    (C := SourcePositiveHarmonicConsumer.sourceCenters)
    (Z := SourcePositiveHarmonicConsumer.sourceAux)
    (R := SourceExactRoot.sourceRadius) (updated_nonneg x hpin hr)
    SourceCentreB2Readout.canonical_mass_one (delta_mass_zero x)
    SourceCentreB2Readout.canonical_free_balance (delta_force_zero x)
    (delta_zero_on_zero_stress x) source_carrying_length

end
end N11Formalization.SourceRelativeFluxNorms
#check @N11Formalization.SourceRelativeFluxNorms.actual_flux_norm
#check @N11Formalization.SourceRelativeFluxNorms.actual_pinned_G_norm
#check @N11Formalization.SourceRelativeFluxNorms.actual_amplitude_gate
#check @N11Formalization.SourceRelativeFluxNorms.delta_flux_bound
#check @N11Formalization.SourceRelativeFluxNorms.updated_nonneg
#check @N11Formalization.SourceRelativeFluxNorms.updated_force_zero
#check @N11Formalization.SourceRelativeFluxNorms.updated_root_value
#print axioms N11Formalization.SourceRelativeFluxNorms.updated_root_value
#print axioms N11Formalization.SourceRelativeFluxNorms.actual_flux_norm
#print axioms N11Formalization.SourceRelativeFluxNorms.actual_amplitude_gate
