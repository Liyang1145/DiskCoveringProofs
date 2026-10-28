import N11Formalization.SourceRelativeAdaptiveConsumer
import N11Formalization.SourceBPointPacket
import N11Formalization.ResumePinnedMatrixReindex

/-! SAME9R/10 actual flux/G identities and source-coordinate boxes.
Canonical flux has no factor2; G=2 inner(flux,tangent).
Source anchor signs are -1, so spoke loads use anchor-minus-site.
The raw8/canonical6 pin is an exact reindexing, not a graph symmetry.
This supplies real entry inputs, not numeric norm/coercivity readouts. -/
set_option autoImplicit false
namespace N11Formalization.SourceRelativeFluxGeometry
open N11Formalization RatInterval ResumeNetwork ResumeDirichlet ResumeLocalIncidence
open SourceRelativeMetric SourceRelativeNormPacket SourceRelativeNormConsumer
open SourcePositiveHarmonicConsumer SourceRadialFluxConsumer SourceResponseFluxIdentity
open SourceBPointPacket SourceActiveMatrixIntervals
noncomputable section

def F (a : Fin 4) (j : Fin 9) : Point :=
  ResumeAnchorFlux.flux (fun e => canonicalN e a) sourceAnchors sourceCenters sourceAux j

def G (j : Fin 9) (a : Fin 4) : ℝ :=
  FlashLocal.Gmat ResumeAnchorFlux.anchorIncidence SourceRelativeAdaptiveConsumer.D
    SourceRelativeAdaptiveConsumer.tangent canonicalN j a

theorem flux_source_spokes (a : Fin 4) (k : Fin 9) :
    F a (siteMap k) =
      ∑ s : Fin 2, sourceN (HarmonicSourceTransport.srcFlat (.inl (k,s))) a •
        (arcEnd SourceExactRoot.sourceRoot k-
          centersOfRoot SourceExactRoot.sourceRoot (SourceTieForceTransport.spokeSite k s)) := by
  classical
  have hz (e : Edge) (he : e ∉ Finset.univ.image edgeMap) :
      ResumeAnchorFlux.anchorIncidence e (siteMap k)*canonicalN e a=0 := by
    have hn : ¬ ∃ s : SourceEdge,edgeMap s=e := by simpa using he
    rw [canonical_zero_off e hn a,mul_zero]
  have hr := HarmonicSourceGeometryV2.point_sum_edgeMap_reindex
    (α := fun e => ResumeAnchorFlux.anchorIncidence e (siteMap k)*canonicalN e a)
    (F := edgeVector sourceAnchors sourceCenters sourceAux) hz
  rw [F,ResumeAnchorFlux.flux,hr,Fintype.sum_sum_type]
  have hf (p : Fin 9 × Fin 3) :
      ResumeAnchorFlux.anchorIncidence (edgeMap (.inr p)) (siteMap k)=0 := rfl
  simp only [hf,zero_mul,zero_smul,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [incidence_source_spoke,vector_source_spoke,canonical_source]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true,neg_one_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [neg_smul,← smul_neg,neg_sub]
  · intro l _ hl
    simp only [if_neg hl,zero_mul,zero_smul,Finset.sum_const_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- Genuine G identity for the actual adaptive Gmat, including factor2. -/
theorem G_flux (j : Fin 9) (a : Fin 4) :
    G j a = 2*inner ℝ (F a j) (SourceRelativeAdaptiveConsumer.tangent j) := by
  unfold G FlashLocal.Gmat FlashLocal.Tmat F ResumeAnchorFlux.flux
  rw [sum_inner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [real_inner_smul_left]
  unfold SourceRelativeAdaptiveConsumer.D
  change 2*ResumeAnchorFlux.anchorIncidence e j*
      inner ℝ (edgeVector sourceAnchors sourceCenters sourceAux e)
        (SourceRelativeAdaptiveConsumer.tangent j)*canonicalN e a = _
  ring

def anchorNode (k : Fin 9) : Fin 29 := ⟨k.val,by omega⟩
def spokeNode (k : Fin 9) (s : Fin 2) : Fin 29 :=
  ⟨9+(SourceTieForceTransport.spokeSite k s).val,by omega⟩

def chordBox (k : Fin 9) (s : Fin 2) (c : Fin 2) : RatInterval :=
  sub (pointI (anchorNode k) c) (pointI (spokeNode k s) c)

theorem chordBox_mem (k : Fin 9) (s : Fin 2) (c : Fin 2) :
    (chordBox k s c).Mem
      ((arcEnd SourceExactRoot.sourceRoot k-
        centersOfRoot SourceExactRoot.sourceRoot (SourceTieForceTransport.spokeSite k s)).ofLp c) := by
  have hU := pointI_mem (anchorNode k) c
  have hC := pointI_mem (spokeNode k s) c
  dsimp only [anchorNode] at hU
  dsimp only [spokeNode] at hC
  rw [SourceN2.srcX2_anchor] at hU
  rw [SourceN2.srcX2_site] at hC
  exact sub_mem hU hC

def fluxBox (k : Fin 9) (a : Fin 4) (c : Fin 2) : RatInterval :=
  sumI (fun s : Fin 2 =>
    mul (NB (HarmonicSourceTransport.srcFlat (.inl (k,s))) a) (chordBox k s c))

/-- ALL72 actual flux-coordinate memberships, no hflux premise. -/
theorem fluxBox_mem (k : Fin 9) (a : Fin 4) (c : Fin 2) :
    (fluxBox k a c).Mem ((F a (siteMap k)).ofLp c) := by
  rw [flux_source_spokes]
  have h := sumI_mem (fun s : Fin 2 =>
    mul_mem (NB_mem (HarmonicSourceTransport.srcFlat (.inl (k,s))) a) (chordBox_mem k s c))
  simpa only [fluxBox,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,
    smul_eq_mul] using h

theorem tangent_source_zero (k : Fin 9) :
    (SourceRelativeAdaptiveConsumer.tangent (siteMap k)).ofLp 0 =
      -(arcEnd SourceExactRoot.sourceRoot k).ofLp 1 := by
  have h := sourceAnchors_circle (siteMap k)
  change FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot (siteMap k)=_ at h
  rw [FlashRootNetwork.hU_siteMap] at h
  rw [h]
  simp [SourceRelativeAdaptiveConsumer.tangent,FlashLocal.circleTangent,circleMap]

theorem tangent_source_one (k : Fin 9) :
    (SourceRelativeAdaptiveConsumer.tangent (siteMap k)).ofLp 1 =
      (arcEnd SourceExactRoot.sourceRoot k).ofLp 0 := by
  have h := sourceAnchors_circle (siteMap k)
  change FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot (siteMap k)=_ at h
  rw [FlashRootNetwork.hU_siteMap] at h
  rw [h]
  simp [SourceRelativeAdaptiveConsumer.tangent,FlashLocal.circleTangent,circleMap]

def GBox (k : Fin 9) (a : Fin 4) : RatInterval :=
  mul (ofRat 2) (add
    (mul (fluxBox k a 0) (neg (pointI (anchorNode k) 1)))
    (mul (fluxBox k a 1) (pointI (anchorNode k) 0)))

theorem GBox_mem (k : Fin 9) (a : Fin 4) :
    (GBox k a).Mem (G (siteMap k) a) := by
  rw [G_flux,PinTangentGeometry.inner_coords,tangent_source_zero,tangent_source_one]
  have hU0 := pointI_mem (anchorNode k) 0
  have hU1 := pointI_mem (anchorNode k) 1
  dsimp only [anchorNode] at hU0 hU1
  rw [SourceN2.srcX2_anchor] at hU0 hU1
  exact mul_mem (ofRat_mem 2) (add_mem
    (mul_mem (fluxBox_mem k a 0) (neg_mem hU1))
    (mul_mem (fluxBox_mem k a 1) hU0))

end
end N11Formalization.SourceRelativeFluxGeometry
#check @N11Formalization.SourceRelativeFluxGeometry.flux_source_spokes
#check @N11Formalization.SourceRelativeFluxGeometry.G_flux
#check @N11Formalization.SourceRelativeFluxGeometry.fluxBox_mem
#check @N11Formalization.SourceRelativeFluxGeometry.GBox_mem
#print axioms N11Formalization.SourceRelativeFluxGeometry.G_flux
#print axioms N11Formalization.SourceRelativeFluxGeometry.GBox_mem
