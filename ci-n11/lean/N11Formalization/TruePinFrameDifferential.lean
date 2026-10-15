import N11Formalization.TruePinChartConsumer
import N11Formalization.PhysicalFrameSmooth
import N11Formalization.ResidualDerivJT

/-!
Actual smooth equal-circle pins in the independent width/direction frame.
Their derivative discrepancy with the reflected extension vanishes on the
boundary kernel and factors through the five boundary rows. This is a local
source differential result, not Cartesian stationarity or a global lower bound.
-/
set_option autoImplicit false
namespace N11Formalization.TruePinFrameDifferential
open N11Formalization BoundaryChartLinear BoundaryChartSource
open BoundaryChartDifferential PhysicalResidualFrame TrueCirclePinSmooth
noncomputable section

abbrev Frame := Fin 12 → ℝ
def sourcePoint : Frame := sourceFrame SourceExactRoot.sourceRoot

def frameData (k : Fin 9) (x : Frame) : Data :=
  ![(center x k) 0, (center x k) 1,
    (center x (k+1)) 0, (center x (k+1)) 1, x 11]

def framePin (k : Fin 9) (x : Frame) : Point :=
  pinData (sourceSeed k) (frameData k x)

theorem frameData_sourceFrame (k : Fin 9) (u : Frame) :
    frameData k (sourceFrame u) = TruePinChartConsumer.dataOf k u := by
  simp only [frameData, center_source, TruePinChartConsumer.dataOf]
  rfl

theorem framePin_sourceFrame (k : Fin 9) (u : Frame) :
    framePin k (sourceFrame u) = TruePinChartConsumer.truePin k u := by
  rw [framePin, frameData_sourceFrame]
  rfl

theorem frameData_source (k : Fin 9) : frameData k sourcePoint = sourceData k := by
  rw [sourcePoint, frameData_sourceFrame]
  rfl

theorem framePin_source (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    framePin k sourcePoint = pin sourcePoint k := by
  rw [sourcePoint, framePin_sourceFrame, pin_source]
  exact TruePinChartConsumer.truePin_source k hk

private theorem widths_smooth (k : Fin 9) :
    ContDiffAt ℝ 1 (fun x : Frame => widths x k) sourcePoint := by
  fin_cases k <;> simp [widths] <;> fun_prop

private theorem directions_smooth (k : Fin 9) :
    ContDiffAt ℝ 1 (fun x : Frame => directions x k) sourcePoint := by
  fin_cases k <;> simp [directions] <;> fun_prop

theorem center_source_smooth (k : Fin 9) :
    ContDiffAt ℝ 1 (fun x : Frame => center x k) sourcePoint := by
  have hr : (sourcePoint 11)^2 - Real.sin (widths sourcePoint k)^2 ≠ 0 := by
    change (SourceExactRoot.sourceRoot 6)^2 -
      Real.sin (widths (sourceFrame SourceExactRoot.sourceRoot) k)^2 ≠ 0
    rw [widths_source]
    exact ne_of_gt (SourceWidthNondegenerate.source_radicand_pos k)
  have hR : ContDiffAt ℝ 1 (fun x : Frame => x 11) sourcePoint := by fun_prop
  have hrad : ContDiffAt ℝ 1 (fun x : Frame => radial x k) sourcePoint :=
    (contDiffAt_cos_comp (widths_smooth k)).sub
      (((hR.pow 2).sub ((contDiffAt_sin_comp (widths_smooth k)).pow 2)).sqrt hr)
  rw [contDiffAt_piLp 2]
  intro i
  fin_cases i
  · exact hrad.mul (contDiffAt_cos_comp (directions_smooth k))
  · exact hrad.mul (contDiffAt_sin_comp (directions_smooth k))

theorem pin_source_smooth (k : Fin 9) :
    ContDiffAt ℝ 1 (fun x : Frame => pin x k) sourcePoint := by
  have he : ContDiffAt ℝ 1 (fun x : Frame => endpoint x k) sourcePoint := by
    rw [contDiffAt_piLp 2]
    intro i
    fin_cases i
    · exact contDiffAt_cos_comp ((directions_smooth k).add (widths_smooth k))
    · exact contDiffAt_sin_comp ((directions_smooth k).add (widths_smooth k))
  exact ((center_source_smooth k).add (center_source_smooth (k+1))).sub he

theorem frameData_source_smooth (k : Fin 9) :
    ContDiffAt ℝ 1 (frameData k) sourcePoint := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact ((contDiffAt_piLp 2).mp (center_source_smooth k)) 0
  · exact ((contDiffAt_piLp 2).mp (center_source_smooth k)) 1
  · exact ((contDiffAt_piLp 2).mp (center_source_smooth (k+1))) 0
  · exact ((contDiffAt_piLp 2).mp (center_source_smooth (k+1))) 1
  · exact contDiffAt_coord 11 _

theorem framePin_source_smooth (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (framePin k) sourcePoint := by
  have h := source_pinData_smooth k hk
  rw [← frameData_source k] at h
  exact h.comp sourcePoint (frameData_source_smooth k)

/-- The derivative of the actual source frame, with all seven TC coordinates retained. -/
theorem sourceFrame_hasFDerivAt (u : Frame) :
    HasFDerivAt sourceFrame (chartCLM.comp proj7CLM) u := by
  have h := (hasFDerivAt_affineChart (first7 u)).comp u (hasFDerivAt_first7 u)
  have he : (fun v : Frame => affineChart (first7 v)) = sourceFrame :=
    funext (fun v => (sourceFrame_eq_affineChart v).symm)
  change HasFDerivAt (fun v : Frame => affineChart (first7 v))
    (chartCLM.comp proj7CLM) u at h
  rwa [he] at h

/-- Real consumer of the TC bridge: equality on all seven boundary-chart directions. -/
theorem framePin_chart_derivative (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (z : Fin 7 → ℝ) :
    fderiv ℝ (framePin k) sourcePoint (chart z) =
      fderiv ℝ (fun x : Frame => pin x k) sourcePoint (chart z) := by
  have ht := ((framePin_source_smooth k hk).differentiableAt (by norm_num)).hasFDerivAt
  have hp := ((pin_source_smooth k).differentiableAt (by norm_num)).hasFDerivAt
  have htcomp := ht.comp SourceExactRoot.sourceRoot
    (sourceFrame_hasFDerivAt SourceExactRoot.sourceRoot)
  have hpcomp := hp.comp SourceExactRoot.sourceRoot
    (sourceFrame_hasFDerivAt SourceExactRoot.sourceRoot)
  have het : (fun u : Frame => framePin k (sourceFrame u)) =
      TruePinChartConsumer.truePin k := funext (framePin_sourceFrame k)
  have hep : (fun u : Frame => pin (sourceFrame u) k) =
      (fun u : Frame => Uvec u k) := funext (fun u => pin_source u k)
  change HasFDerivAt (fun u : Frame => framePin k (sourceFrame u))
    ((fderiv ℝ (framePin k) sourcePoint).comp (chartCLM.comp proj7CLM))
    SourceExactRoot.sourceRoot at htcomp
  change HasFDerivAt (fun u : Frame => pin (sourceFrame u) k)
    ((fderiv ℝ (fun x : Frame => pin x k) sourcePoint).comp (chartCLM.comp proj7CLM))
    SourceExactRoot.sourceRoot at hpcomp
  rw [het] at htcomp
  rw [hep] at hpcomp
  have hcomp := htcomp.fderiv.symm.trans
    ((TruePinChartConsumer.truePin_source_fderiv k hk).trans hpcomp.fderiv)
  let du : Frame := fun i => if h : (i : ℕ) < 7 then z ⟨i,h⟩ else 0
  have hdu : proj7CLM du = z := by
    rw [proj7CLM_apply_eq_first7]
    funext i
    simp [du, first7, i.isLt]
  have he := congrArg (fun d : Frame →L[ℝ] Point => d du) hcomp
  simpa only [ContinuousLinearMap.comp_apply, hdu, chartCLM_apply] using he

def discrepancy (k : Fin 9) : Frame →L[ℝ] Point :=
  fderiv ℝ (framePin k) sourcePoint -
    fderiv ℝ (fun x : Frame => pin x k) sourcePoint

theorem discrepancy_kernel_zero (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (v : Frame) (hv : boundary v = 0) : discrepancy k v = 0 := by
  rw [← chart_extract_of_boundary_zero v hv]
  exact sub_eq_zero.mpr (framePin_chart_derivative k hk (extract v))

private theorem frame_decomposition (v : Frame) :
    v = chart (extract v) + rightInverse (boundary v) := by
  funext i
  fin_cases i <;> simp [chart, extract, rightInverse, boundary, Fin.reduceFinMk] <;> ring

private theorem rightInverse_basis (b : Fin 5 → ℝ) :
    rightInverse b = ∑ j : Fin 5, b j • rightInverse (Pi.single j 1) := by
  funext i
  fin_cases i <;>
    simp [rightInverse, Fin.sum_univ_succ, Pi.single_apply, Fin.reduceFinMk] <;> ring

/-- No unproved annihilator premise: the actual vector discrepancy is a sum of the
five boundary rows with explicitly defined Point coefficients. -/
theorem discrepancy_boundary_factorization (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) (v : Frame) :
    discrepancy k v =
      ∑ j : Fin 5, boundary v j • discrepancy k (rightInverse (Pi.single j 1)) := by
  have hz : discrepancy k (chart (extract v)) = 0 :=
    sub_eq_zero.mpr (framePin_chart_derivative k hk (extract v))
  calc
    discrepancy k v =
        discrepancy k (chart (extract v) + rightInverse (boundary v)) :=
      congrArg (discrepancy k) (frame_decomposition v)
    _ = discrepancy k (rightInverse (boundary v)) := by rw [map_add, hz, zero_add]
    _ = ∑ j : Fin 5, boundary v j • discrepancy k (rightInverse (Pi.single j 1)) := by
      rw [rightInverse_basis, map_sum]
      simp only [map_smul]

end
end N11Formalization.TruePinFrameDifferential
#check @N11Formalization.TruePinFrameDifferential.discrepancy_boundary_factorization
#print axioms N11Formalization.TruePinFrameDifferential.discrepancy_boundary_factorization
