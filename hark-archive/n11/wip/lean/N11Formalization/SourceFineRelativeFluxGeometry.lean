import N11Formalization.SourceFineRelativeNIntervals
import N11Formalization.SourceRelativeFluxGeometry

/-! Finer providers for UNCHANGED actual SAME9R/10 flux/G. Actual two-spoke
identity and G factor2 are reused, not replaced by proposed coefficients. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineRelativeFluxGeometry
open N11Formalization RatInterval ResumeLocalIncidence SourceActiveMatrixIntervals
open SourceFineBPointPacket SourceFineRelativeNIntervals
open _root_.N11Formalization.SourceRelativeFluxGeometry hiding
  chordBox chordBox_mem fluxBox fluxBox_mem GBox GBox_mem
noncomputable section

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
theorem fluxBox_mem (k : Fin 9) (a : Fin 4) (c : Fin 2) :
    (fluxBox k a c).Mem ((F a (siteMap k)).ofLp c) := by
  rw [flux_source_spokes]
  have h := sumI_mem (fun s : Fin 2 =>
    mul_mem (NB_mem (HarmonicSourceTransport.srcFlat (.inl (k,s))) a) (chordBox_mem k s c))
  simpa only [fluxBox,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,
    smul_eq_mul] using h

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
end N11Formalization.SourceFineRelativeFluxGeometry
#check @N11Formalization.SourceFineRelativeFluxGeometry.GBox_mem
#print axioms N11Formalization.SourceFineRelativeFluxGeometry.GBox_mem
