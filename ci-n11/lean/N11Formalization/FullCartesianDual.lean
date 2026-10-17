import N11Formalization.FullCartesianResidual

/-!
Actual full-coordinate contact objective, averaged over the site/geometric
reflection. Source derivative invariance is proved, not assumed.
The restriction of this actual covector to all fixed Cartesian directions is
identified with the TRUE Cartesian dual. Physical boundary-branch multiplier
conversion remains separate; this is not yet a B2 stress-balance theorem.
-/
set_option autoImplicit false
namespace N11Formalization.FullCartesianDual
open N11Formalization CartesianReflectionSpace
noncomputable section

def fullDerivative : Full →L[ℝ] ℝ :=
  fderiv ℝ FullCartesianResidual.objectiveFull FullCartesianResidual.sourcePoint

def averagedObjective (x : Full) : ℝ :=
  (FullCartesianResidual.objectiveFull x +
    FullCartesianResidual.objectiveFull (reflect x)) / 2

def averagedDerivative : Full →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • (fullDerivative + fullDerivative.comp reflectCLM)

theorem averagedObjective_invariant (x : Full) :
    averagedObjective (reflect x) = averagedObjective x := by
  simp only [averagedObjective, reflect_involution]
  ring

theorem averagedDerivative_hasFDerivAt :
    HasFDerivAt averagedObjective averagedDerivative FullCartesianResidual.sourcePoint := by
  have hf := (FullCartesianResidual.objectiveFull_source_smooth.differentiableAt
    (by norm_num)).hasFDerivAt
  have hs : reflect FullCartesianResidual.sourcePoint = FullCartesianResidual.sourcePoint :=
    source_fixed
  have hf' : HasFDerivAt FullCartesianResidual.objectiveFull fullDerivative
      (reflect FullCartesianResidual.sourcePoint) := by
    rw [hs]
    exact hf
  have hc := hf'.comp FullCartesianResidual.sourcePoint
    reflectCLM.hasFDerivAt
  have h := (hf.add hc).const_smul ((2 : ℝ)⁻¹)
  change HasFDerivAt (fun x : Full => (2 : ℝ)⁻¹ *
      (FullCartesianResidual.objectiveFull x +
        FullCartesianResidual.objectiveFull (reflect x)))
      averagedDerivative FullCartesianResidual.sourcePoint at h
  have he : averagedObjective = (fun x : Full => (2 : ℝ)⁻¹ *
      (FullCartesianResidual.objectiveFull x +
        FullCartesianResidual.objectiveFull (reflect x))) := by
    funext x
    simp only [averagedObjective, div_eq_mul_inv]
    ring
  rwa [← he] at h

theorem averagedDerivative_invariant (x : Full) :
    averagedDerivative (reflect x) = averagedDerivative x := by
  simp only [averagedDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, reflectCLM_apply,
    reflect_involution]
  module

theorem averagedDerivative_embed (q : Fixed) :
    averagedDerivative (embed q) = fullDerivative (embed q) := by
  simp only [averagedDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, reflectCLM_apply, reflect_embed]
  simp [smul_eq_mul]
  ring

theorem frameCartesian_hasFDerivAt :
    HasFDerivAt frameCartesian
      ((CartesianPolarFrame.sourceJacobian :
          Fixed →L[ℝ] Fixed).comp
        (CoupledRadialFrame.sourceJacobian : Fixed →L[ℝ] Fixed))
      CoupledRadialFrame.sourcePoint := by
  exact CartesianPolarFrame.source_strict_derivative.hasFDerivAt.comp
    CoupledRadialFrame.sourcePoint CoupledRadialFrame.source_strict_derivative.hasFDerivAt

/-- Actual full geometry → source frame covector, using a full function identity. -/
theorem fullDerivative_frame (v : Fixed) :
    fullDerivative
      (embed (CartesianPolarFrame.sourceJacobian (CoupledRadialFrame.sourceJacobian v))) =
      fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint v := by
  have hf : HasFDerivAt FullCartesianResidual.objectiveFull fullDerivative
      (embed (frameCartesian CoupledRadialFrame.sourcePoint)) := by
    rw [show embed (frameCartesian CoupledRadialFrame.sourcePoint) =
      FullCartesianResidual.sourcePoint from embed_frame_source SourceExactRoot.sourceRoot]
    exact (FullCartesianResidual.objectiveFull_source_smooth.differentiableAt
      (by norm_num)).hasFDerivAt
  have hi := embedCLM.hasFDerivAt.comp CoupledRadialFrame.sourcePoint
    frameCartesian_hasFDerivAt
  have h := hf.comp CoupledRadialFrame.sourcePoint hi
  have he : (fun x : Fixed => FullCartesianResidual.objectiveFull
      (embed (frameCartesian x))) = TrueResidualFrame.objectiveTrue :=
    funext FullCartesianResidual.objectiveFull_frame
  change HasFDerivAt (fun x : Fixed => FullCartesianResidual.objectiveFull
      (embed (frameCartesian x)))
      (fullDerivative.comp (embedCLM.comp
        ((CartesianPolarFrame.sourceJacobian : Fixed →L[ℝ] Fixed).comp
          (CoupledRadialFrame.sourceJacobian : Fixed →L[ℝ] Fixed))))
      CoupledRadialFrame.sourcePoint at h
  rw [he] at h
  have hv := congrArg (fun d : Fixed →L[ℝ] ℝ => d v) h.fderiv
  exact hv.symm

/-- The actual averaged full-space covector agrees with the already-proved TRUE
Cartesian objective on every fixed direction, without any invariance premise. -/
theorem averagedDerivative_fixed_cartesian (q : Fixed) :
    averagedDerivative (embed q) =
      fderiv ℝ TrueCartesianDualConsumer.objectiveCartesian
        (CartesianPolarFrame.cartesian CartesianPolarFrame.sourceRho) q := by
  rw [averagedDerivative_embed, TrueCartesianDualConsumer.objectiveCartesian_hasFDerivAt.fderiv]
  have hv := fullDerivative_frame
    (CoupledRadialFrame.sourceJacobian.symm (CartesianPolarFrame.sourceJacobian.symm q))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hv
  exact hv

/-- Concrete full-coordinate consumer: the same five boundary coefficients control
the actual averaged source contact objective on ALL fixed Cartesian directions. -/
theorem actual_fixed_cartesian_dual (q : Fixed) :
    averagedDerivative (embed q) =
      ∑ j : Fin 5, BoundaryChartDual.multiplier
        (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
          CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
        BoundaryChartLinear.boundary
          (CoupledRadialFrame.triangularInv
            (CoupledRadialFrame.slopeA CoupledRadialFrame.sourcePoint)
            (CoupledRadialFrame.slopeB CoupledRadialFrame.sourcePoint)
            (CartesianPolarFrame.sourceJacobian.symm q)) j := by
  rw [averagedDerivative_fixed_cartesian]
  exact TrueCartesianDualConsumer.sourceRoot_true_cartesian_dual q

def fixedProjection (x : Full) : Full := (2 : ℝ)⁻¹ • (x + reflect x)

theorem fixedProjection_fixed (x : Full) :
    reflect (fixedProjection x) = fixedProjection x := by
  change reflectLinear ((2 : ℝ)⁻¹ • (x + reflectLinear x)) =
    (2 : ℝ)⁻¹ • (x + reflectLinear x)
  rw [map_smul, map_add]
  change (2 : ℝ)⁻¹ • (reflect x + reflect (reflect x)) =
    (2 : ℝ)⁻¹ • (x + reflect x)
  rw [reflect_involution, add_comm]

theorem averagedDerivative_fixedProjection (x : Full) :
    averagedDerivative (fixedProjection x) = averagedDerivative x := by
  rw [fixedProjection, map_smul, map_add, averagedDerivative_invariant]
  simp [smul_eq_mul]
  ring

/-- These are explicitly transported invariant boundary rows, not yet asserted to
be the gradients of the physical boundary covering-radius constraints. -/
def invariantBoundary (x : Full) : Fin 5 → ℝ :=
  BoundaryChartLinear.boundary
    (CoupledRadialFrame.triangularInv
      (CoupledRadialFrame.slopeA CoupledRadialFrame.sourcePoint)
      (CoupledRadialFrame.slopeB CoupledRadialFrame.sourcePoint)
      (CartesianPolarFrame.sourceJacobian.symm (extract (fixedProjection x))))

/-- Unconditional covector factorization for every FULL Cartesian23 direction.
The real full objective and its reflection invariance were proved above; no
full-space invariance or fixed-space stationarity hypothesis is supplied here.
Physical row/scale identification and B2 force conversion are still separate. -/
theorem actual_full_cartesian_dual (x : Full) :
    fderiv ℝ averagedObjective FullCartesianResidual.sourcePoint x =
      ∑ j : Fin 5, BoundaryChartDual.multiplier
        (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
          CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
        invariantBoundary x j := by
  rw [averagedDerivative_hasFDerivAt.fderiv, ← averagedDerivative_fixedProjection x]
  rw [← embed_extract_of_fixed (fixedProjection x) (fixedProjection_fixed x)]
  exact actual_fixed_cartesian_dual (extract (fixedProjection x))

end
end N11Formalization.FullCartesianDual
#check @N11Formalization.FullCartesianDual.averagedDerivative_hasFDerivAt
#check @N11Formalization.FullCartesianDual.actual_fixed_cartesian_dual
#check @N11Formalization.FullCartesianDual.actual_full_cartesian_dual
#print axioms N11Formalization.FullCartesianDual.actual_fixed_cartesian_dual
#print axioms N11Formalization.FullCartesianDual.actual_full_cartesian_dual
