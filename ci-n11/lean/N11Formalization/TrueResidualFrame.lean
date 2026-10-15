import N11Formalization.TruePinFrameDifferential

/-!
The actual length residual objective made from genuine equal-circle ring pins.
The central pin is kept explicitly as the existing true two-hub construction.
Source smoothness and the complete boundary-chart derivative are discharged,
giving an unconditional five-boundary-covector source dual. This does not yet
identify independent Cartesian force rows or establish unrestricted optimality.
-/
set_option autoImplicit false
namespace N11Formalization.TrueResidualFrame
open N11Formalization BoundaryChartLinear BoundaryChartSource BoundaryChartDifferential
open PhysicalResidualFrame TruePinFrameDifferential
noncomputable section

def contact (j : Fin 4) : Fin 9 := ![1,2,3,8] j
def contactHub (j : Fin 4) (x : Frame) : Point :=
  if j=0 ∨ j=3 then hubB x else hubA x

theorem contact_active (j : Fin 4) :
    contact j=1 ∨ contact j=2 ∨ contact j=3 ∨ contact j=8 := by
  fin_cases j <;> simp [contact]

theorem hub_source_smooth (j : Fin 4) :
    ContDiffAt ℝ 1 (contactHub j) sourcePoint := by
  unfold contactHub
  split_ifs <;> rw [contDiffAt_piLp 2] <;> intro i <;>
    fin_cases i <;> simp [hubA, hubB] <;> fun_prop

theorem contact_source_ne (j : Fin 4) :
    pin sourcePoint (contact j) ≠ contactHub j sourcePoint := by
  obtain ⟨h1,h2,h3,h8,_⟩ := nd_all_via_dist
  have hb := TCChartStationarityRoot.sourceRoot_mem_ball
  fin_cases j
  · simpa [contact, contactHub, sourcePoint, pin_source, hubB_source] using h1 _ hb
  · simpa [contact, contactHub, sourcePoint, pin_source, hubA_source] using h2 _ hb
  · simpa [contact, contactHub, sourcePoint, pin_source, hubA_source] using h3 _ hb
  · simpa [contact, contactHub, sourcePoint, pin_source, hubB_source] using h8 _ hb

def residualTrue (x : Frame) : Fin 5 → ℝ :=
  ![dist (framePin 1 x) (hubB x) - x 11,
    dist (framePin 2 x) (hubA x) - x 11,
    dist (framePin 3 x) (hubA x) - x 11,
    dist (framePin 8 x) (hubB x) - x 11,
    dist (centralPin x) (center x 6) - x 11]

theorem residualTrue_source : residualTrue sourcePoint = residualFrame sourcePoint := by
  unfold residualTrue residualFrame
  rw [framePin_source 1 (by simp), framePin_source 2 (by simp),
    framePin_source 3 (by simp), framePin_source 8 (by simp)]

theorem residualTrue_source_smooth : ContDiffAt ℝ 1 residualTrue sourcePoint := by
  have hrow (j : Fin 4) : ContDiffAt ℝ 1
      (fun x : Frame => dist (framePin (contact j) x) (contactHub j x) - x 11)
      sourcePoint :=
    ((framePin_source_smooth (contact j) (contact_active j)).dist ℝ
      (hub_source_smooth j) (by
        rw [framePin_source _ (contact_active j)]
        exact contact_source_ne j)).sub (contDiffAt_coord 11 _)
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact hrow 0
  · exact hrow 1
  · exact hrow 2
  · exact hrow 3
  · exact (contDiffAt_pi.mp PhysicalFrameSmooth.sourceRoot_frame_smooth) 4

private theorem distance_chart_derivative {f g h : Frame → Point}
    (hf : DifferentiableAt ℝ f sourcePoint)
    (hg : DifferentiableAt ℝ g sourcePoint)
    (hh : DifferentiableAt ℝ h sourcePoint)
    (hvalue : f sourcePoint = g sourcePoint)
    (hne : g sourcePoint ≠ h sourcePoint)
    (heq : ∀ z : Fin 7 → ℝ,
      fderiv ℝ f sourcePoint (chart z) = fderiv ℝ g sourcePoint (chart z))
    (z : Fin 7 → ℝ) :
    fderiv ℝ (fun x => dist (f x) (h x)) sourcePoint (chart z) =
      fderiv ℝ (fun x => dist (g x) (h x)) sourcePoint (chart z) := by
  have hn : DifferentiableAt ℝ (fun p : Point => ‖p‖)
      (g sourcePoint - h sourcePoint) :=
    differentiableAt_id.norm ℝ (sub_ne_zero.mpr hne)
  have hnf : HasFDerivAt (fun p : Point => ‖p‖)
      (fderiv ℝ (fun p : Point => ‖p‖) (g sourcePoint - h sourcePoint))
      (f sourcePoint - h sourcePoint) := by
    rw [hvalue]
    exact hn.hasFDerivAt
  have hdF := hnf.comp sourcePoint (hf.hasFDerivAt.sub hh.hasFDerivAt)
  have hdG := hn.hasFDerivAt.comp sourcePoint (hg.hasFDerivAt.sub hh.hasFDerivAt)
  have hF : fderiv ℝ (fun x => dist (f x) (h x)) sourcePoint =
      (fderiv ℝ (fun p : Point => ‖p‖) (g sourcePoint-h sourcePoint)).comp
        (fderiv ℝ f sourcePoint - fderiv ℝ h sourcePoint) := by
    simpa only [dist_eq_norm, Function.comp_def, Pi.sub_apply] using hdF.fderiv
  have hG : fderiv ℝ (fun x => dist (g x) (h x)) sourcePoint =
      (fderiv ℝ (fun p : Point => ‖p‖) (g sourcePoint-h sourcePoint)).comp
        (fderiv ℝ g sourcePoint - fderiv ℝ h sourcePoint) := by
    simpa only [dist_eq_norm, Function.comp_def, Pi.sub_apply] using hdG.fderiv
  rw [hF, hG]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, heq z]

theorem contact_length_chart_derivative (j : Fin 4) (z : Fin 7 → ℝ) :
    fderiv ℝ (fun x : Frame =>
      dist (framePin (contact j) x) (contactHub j x) - x 11) sourcePoint (chart z) =
    fderiv ℝ (fun x : Frame =>
      dist (pin x (contact j)) (contactHub j x) - x 11) sourcePoint (chart z) := by
  have ht := (framePin_source_smooth (contact j) (contact_active j)).differentiableAt
    (by norm_num)
  have hp := (pin_source_smooth (contact j)).differentiableAt (by norm_num)
  have hh := (hub_source_smooth j).differentiableAt (by norm_num)
  have hval := framePin_source (contact j) (contact_active j)
  have hne := contact_source_ne j
  have hd := distance_chart_derivative ht hp hh hval hne
    (framePin_chart_derivative (contact j) (contact_active j)) z
  have hdt := ht.dist ℝ hh (by rw [hval]; exact hne)
  have hdp := hp.dist ℝ hh hne
  have hR : DifferentiableAt ℝ (fun x : Frame => x 11) sourcePoint := by fun_prop
  change fderiv ℝ
    ((fun x : Frame => dist (framePin (contact j) x) (contactHub j x)) -
      (fun x : Frame => x 11)) sourcePoint (chart z) =
    fderiv ℝ
    ((fun x : Frame => dist (pin x (contact j)) (contactHub j x)) -
      (fun x : Frame => x 11)) sourcePoint (chart z)
  rw [fderiv_sub hdt hR, fderiv_sub hdp hR]
  simp only [ContinuousLinearMap.sub_apply, hd]

/-- All five actual length rows agree on the full boundary kernel, including the
unchanged central-contact row; no residual derivative premise is left. -/
theorem residualTrue_chart_derivative (z : Fin 7 → ℝ) :
    fderiv ℝ residualTrue sourcePoint (chart z) =
      fderiv ℝ residualFrame sourcePoint (chart z) := by
  have ht := residualTrue_source_smooth.differentiableAt (by norm_num)
  have hp := PhysicalFrameSmooth.sourceRoot_frame_smooth.differentiableAt (by norm_num)
  have hrow (i : Fin 5) (f : Frame → (Fin 5 → ℝ))
      (hf : DifferentiableAt ℝ f sourcePoint) :
      fderiv ℝ (fun x => f x i) sourcePoint =
        (ContinuousLinearMap.proj i).comp (fderiv ℝ f sourcePoint) := by
    have h := (ContinuousLinearMap.proj i :
      (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp sourcePoint hf.hasFDerivAt
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using h.fderiv
  funext i
  change ((ContinuousLinearMap.proj i).comp (fderiv ℝ residualTrue sourcePoint)) (chart z) =
    ((ContinuousLinearMap.proj i).comp (fderiv ℝ residualFrame sourcePoint)) (chart z)
  rw [← hrow i residualTrue ht, ← hrow i residualFrame hp]
  fin_cases i
  · exact contact_length_chart_derivative 0 z
  · exact contact_length_chart_derivative 1 z
  · exact contact_length_chart_derivative 2 z
  · exact contact_length_chart_derivative 3 z
  · rfl

def objectiveTrue (x : Frame) : ℝ :=
  x 11 - ∑ k : Fin 5, last5 SourceExactRoot.sourceRoot k * residualTrue x k

theorem objectiveTrue_source_smooth : ContDiffAt ℝ 1 objectiveTrue sourcePoint := by
  exact (contDiffAt_coord 11 _).sub
    (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 5))) (fun k _ =>
      ((contDiffAt_pi.mp residualTrue_source_smooth) k).const_smul
        (last5 SourceExactRoot.sourceRoot k)))

def objectiveDerivative (f : Frame → (Fin 5 → ℝ)) : Frame →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (11 : Fin 12) -
    ∑ k : Fin 5, last5 SourceExactRoot.sourceRoot k •
      (ContinuousLinearMap.proj k).comp (fderiv ℝ f sourcePoint)

private theorem objective_hasFDerivAt (f : Frame → (Fin 5 → ℝ))
    (hf : DifferentiableAt ℝ f sourcePoint) :
    HasFDerivAt (fun x : Frame => x 11 -
      ∑ k : Fin 5, last5 SourceExactRoot.sourceRoot k * f x k)
      (objectiveDerivative f) sourcePoint := by
  have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 5))) (fun k _ =>
    ((ContinuousLinearMap.proj k).hasFDerivAt.comp sourcePoint hf.hasFDerivAt).const_smul
      (last5 SourceExactRoot.sourceRoot k))
  exact (ContinuousLinearMap.proj (11 : Fin 12)).hasFDerivAt.sub hs

theorem objectiveTrue_chart_derivative (z : Fin 7 → ℝ) :
    fderiv ℝ objectiveTrue sourcePoint (chart z) =
      fderiv ℝ (objectiveFrame SourceExactRoot.sourceRoot) sourcePoint (chart z) := by
  change fderiv ℝ (fun x : Frame => x 11 -
      ∑ k : Fin 5, last5 SourceExactRoot.sourceRoot k * residualTrue x k)
      sourcePoint (chart z) =
    fderiv ℝ (fun x : Frame => x 11 -
      ∑ k : Fin 5, last5 SourceExactRoot.sourceRoot k * residualFrame x k)
      sourcePoint (chart z)
  rw [(objective_hasFDerivAt residualTrue
    (residualTrue_source_smooth.differentiableAt (by norm_num))).fderiv,
    (objective_hasFDerivAt residualFrame
      (PhysicalFrameSmooth.sourceRoot_frame_smooth.differentiableAt (by norm_num))).fderiv]
  simp only [objectiveDerivative, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, residualTrue_chart_derivative]

theorem objectiveTrue_chart_stationarity :
    fderiv ℝ (fun z : Fin 7 → ℝ => objectiveTrue (affineChart z))
      (first7 SourceExactRoot.sourceRoot) = 0 := by
  have hd := (objectiveTrue_source_smooth.differentiableAt (by norm_num)).hasFDerivAt
  have he : sourcePoint = affineChart (first7 SourceExactRoot.sourceRoot) :=
    sourceFrame_eq_affineChart SourceExactRoot.sourceRoot
  have hd' : HasFDerivAt objectiveTrue (fderiv ℝ objectiveTrue sourcePoint)
      (affineChart (first7 SourceExactRoot.sourceRoot)) := by
    rw [← he]
    exact hd
  have hcomp := hd'.comp (first7 SourceExactRoot.sourceRoot)
    (hasFDerivAt_affineChart (first7 SourceExactRoot.sourceRoot))
  change fderiv ℝ (objectiveTrue ∘ affineChart)
    (first7 SourceExactRoot.sourceRoot) = 0
  rw [hcomp.fderiv]
  apply ContinuousLinearMap.ext
  intro z
  change fderiv ℝ objectiveTrue sourcePoint (chart z) = 0
  rw [objectiveTrue_chart_derivative]
  have hb := PhysicalFrameSmooth.sourceRoot_objective_dual (chart z)
  simpa only [sourcePoint, boundary_chart, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero] using hb

/-- Actual source dual for TRUE intersection length residuals, with differentiability
and chart stationarity discharged. Not yet a Cartesian23/B2 force equation. -/
theorem objectiveTrue_boundary_dual (v : Frame) :
    fderiv ℝ objectiveTrue sourcePoint v =
      ∑ j : Fin 5, BoundaryChartDual.multiplier
        (fun i => fderiv ℝ objectiveTrue sourcePoint (Pi.single i 1)) j * boundary v j :=
  RootBoundaryDualConsumer.physical_dual_factorization
    (objectiveTrue_source_smooth.differentiableAt (by norm_num)).hasFDerivAt
    objectiveTrue_chart_stationarity v

end
end N11Formalization.TrueResidualFrame
#check @N11Formalization.TrueResidualFrame.objectiveTrue_boundary_dual
#print axioms N11Formalization.TrueResidualFrame.objectiveTrue_boundary_dual
