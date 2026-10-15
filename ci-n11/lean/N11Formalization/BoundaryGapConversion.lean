import N11Formalization.BoundaryPolarRows

/-! Positive gap-to-ACTUAL-unit-circle-tie gradient conversion. Independent
Frame directions are first consumed through the true Cartesian Jacobian,
then inverted to fixed Cartesian coordinates, and orbit-averaged to all23.
No assumed radius branch / hgradient / fixed-R shortcut is used. -/
set_option autoImplicit false
namespace N11Formalization.BoundaryGapConversion
open N11Formalization PhysicalResidualFrame CartesianReflectionSpace
open SourceFrameVelocity SourceBoundaryWeights
noncomputable section

def representative (j : Fin 5) : Fin 9 := ![0,1,2,3,8] j

theorem representative_active (j : Fin 5) :
    representative j=0 ∨ representative j=1 ∨ representative j=2 ∨
      representative j=3 ∨ representative j=8 := by
  fin_cases j <;> simp [representative]

def gap (v : Frame) (k : Fin 9) : ℝ :=
  directions v (k+1)-directions v k-widths v k-widths v (k+1)

theorem gap_boundary (v : Frame) (j : Fin 5) :
    gap v (representative j)=BoundaryChartLinear.boundary v j := by
  fin_cases j <;> simp [gap,representative,directions,widths,
    BoundaryChartLinear.boundary,Fin.reduceFinMk,nd_fin_succ_0,nd_fin_succ_1,
    nd_fin_succ_2,nd_fin_succ_3,nd_fin_succ_8] <;> ring

theorem excess_source_smooth (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (SourceBoundaryTie.radiusExcess k) FullCartesianResidual.sourcePoint := by
  have hr : ContDiffAt ℝ 1 (fun x : Full => x 22) FullCartesianResidual.sourcePoint := by fun_prop
  exact (SourceBoundaryTie.radiusFull_source_smooth k hk).sub hr

theorem excess_source_fderiv (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (x : Full) :
    fderiv ℝ (SourceBoundaryTie.radiusExcess k) FullCartesianResidual.sourcePoint x =
      fderiv ℝ (SourceBoundaryTie.radiusFull k) FullCartesianResidual.sourcePoint x-x 22 := by
  have h := ((SourceBoundaryTie.radiusFull_source_smooth k hk).differentiableAt
    (by norm_num)).hasFDerivAt.sub
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt
  have he := congrArg (fun d : Full →L[ℝ] ℝ => d x) h.fderiv
  exact he

/-- Actual full source tie derivative on the entire independent Frame Jacobian.
The coupled radius column cancels explicitly against -dR, including wrap8→0. -/
theorem gap_frameJac (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) (v : Frame) :
    gap v k=radiusScale k *
      fderiv ℝ (SourceBoundaryTie.radiusExcess k) FullCartesianResidual.sourcePoint (frameJac v) := by
  rw [excess_source_fderiv k hk,SourceBoundaryTieDerivative.radiusFull_source_fderiv k hk,
    ring_frameJac,ring_frameJac,frameJac_radius,
    BoundaryPolarRows.left_velocity_row,BoundaryPolarRows.right_velocity_row,
    BoundaryPolarRows.coupled_radial_row,BoundaryPolarRows.coupled_radial_row,
    eta_eq]
  have hp : SourceBoundaryWeights.slope k≠0 := ne_of_gt (slope_pos k)
  have hq : SourceBoundaryWeights.slope (k+1)≠0 := ne_of_gt (slope_pos (k+1))
  have hs : SourceBoundaryWeights.slope k+SourceBoundaryWeights.slope (k+1)≠0 :=
    ne_of_gt (add_pos (slope_pos k) (slope_pos (k+1)))
  have hR : SourceExactRoot.sourceRoot 6≠0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  unfold radiusScale gap
  field_simp [hp,hq,hs,hR]
  ring

/-- No derivative/coordinate premise: the transported fixed-space row IS the
positive scale times the derivative of the actual constructed tie excess. -/
theorem fixed_cartesian_gap (j : Fin 5) (q : Fixed) :
    BoundaryChartLinear.boundary
      (CoupledRadialFrame.triangularInv
        (CoupledRadialFrame.slopeA CoupledRadialFrame.sourcePoint)
        (CoupledRadialFrame.slopeB CoupledRadialFrame.sourcePoint)
        (CartesianPolarFrame.sourceJacobian.symm q)) j =
      radiusScale (representative j) *
        fderiv ℝ (SourceBoundaryTie.radiusExcess (representative j))
          FullCartesianResidual.sourcePoint (embed q) := by
  let v : Frame := CoupledRadialFrame.sourceJacobian.symm (CartesianPolarFrame.sourceJacobian.symm q)
  have he : frameJac v=embed q := by
    unfold frameJac v
    rw [ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]
  have h := gap_frameJac (representative j) (representative_active j) v
  rw [gap_boundary,he] at h
  simpa only [v,CoupledRadialFrame.sourceJacobian_symm_apply] using h

def rawDerivative (k : Fin 9) : Full →L[ℝ] ℝ :=
  fderiv ℝ (SourceBoundaryTie.radiusExcess k) FullCartesianResidual.sourcePoint
def averagedTieExcess (k : Fin 9) (x : Full) : ℝ :=
  (SourceBoundaryTie.radiusExcess k x+SourceBoundaryTie.radiusExcess k (reflect x))/2
def averagedTieDerivative (k : Fin 9) : Full →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • (rawDerivative k+(rawDerivative k).comp reflectCLM)

theorem averagedTie_hasFDerivAt (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    HasFDerivAt (averagedTieExcess k) (averagedTieDerivative k) FullCartesianResidual.sourcePoint := by
  have hf := ((excess_source_smooth k hk).differentiableAt (by norm_num)).hasFDerivAt
  have hf' : HasFDerivAt (SourceBoundaryTie.radiusExcess k) (rawDerivative k)
      (reflect FullCartesianResidual.sourcePoint) := by
    rw [show reflect FullCartesianResidual.sourcePoint=FullCartesianResidual.sourcePoint from source_fixed]
    exact hf
  have h := (hf.add (hf'.comp FullCartesianResidual.sourcePoint reflectCLM.hasFDerivAt)).const_smul
    ((2 : ℝ)⁻¹)
  have he : averagedTieExcess k=(fun x : Full => (2 : ℝ)⁻¹ *
      (SourceBoundaryTie.radiusExcess k x+SourceBoundaryTie.radiusExcess k (reflect x))) := by
    funext x
    simp only [averagedTieExcess,div_eq_mul_inv]
    ring
  change HasFDerivAt (fun x : Full => (2 : ℝ)⁻¹ *
      (SourceBoundaryTie.radiusExcess k x+SourceBoundaryTie.radiusExcess k (reflect x)))
      (averagedTieDerivative k) FullCartesianResidual.sourcePoint at h
  rwa [← he] at h

theorem averagedTie_embed (k : Fin 9) (q : Fixed) :
    averagedTieDerivative k (embed q)=rawDerivative k (embed q) := by
  simp only [averagedTieDerivative,smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    reflectCLM_apply,reflect_embed,smul_eq_mul]
  ring

theorem averagedTie_invariant (k : Fin 9) (x : Full) :
    averagedTieDerivative k (reflect x)=averagedTieDerivative k x := by
  simp only [averagedTieDerivative,smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    reflectCLM_apply,reflect_involution,smul_eq_mul]
  ring

theorem averagedTie_fixedProjection (k : Fin 9) (x : Full) :
    averagedTieDerivative k (FullCartesianDual.fixedProjection x)=averagedTieDerivative k x := by
  rw [FullCartesianDual.fixedProjection,map_smul,map_add,averagedTie_invariant]
  simp [smul_eq_mul]
  ring

/-- The previously transported invariantBoundary rows are now bound to
ACTUAL independent-centre unit-circle tie-radius excess gradients on all23.
Scale positivity is separately proved by radiusScale_pos. -/
theorem full_gap_to_tie (j : Fin 5) (x : Full) :
    FullCartesianDual.invariantBoundary x j=radiusScale (representative j) *
      fderiv ℝ (averagedTieExcess (representative j)) FullCartesianResidual.sourcePoint x := by
  rw [(averagedTie_hasFDerivAt (representative j) (representative_active j)).fderiv,
    ← averagedTie_fixedProjection (representative j) x]
  rw [← embed_extract_of_fixed (FullCartesianDual.fixedProjection x)
    (FullCartesianDual.fixedProjection_fixed x),averagedTie_embed]
  exact fixed_cartesian_gap j (extract (FullCartesianDual.fixedProjection x))

end
end N11Formalization.BoundaryGapConversion
#check @N11Formalization.BoundaryGapConversion.gap_frameJac
#check @N11Formalization.BoundaryGapConversion.full_gap_to_tie
#print axioms N11Formalization.BoundaryGapConversion.full_gap_to_tie
