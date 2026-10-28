import N11Formalization.SourceBoundaryWeights
import N11Formalization.FullCartesianDual

/-! Actual independent width/direction frame centre derivative. The coupled
variable-R derivative is reused with the explicit width coordinate index;
the polar direction derivative and full Cartesian embedding are consumed.
No assumed centre/Jacobian identity remains. -/
set_option autoImplicit false
namespace N11Formalization.SourceFrameVelocity
open N11Formalization PhysicalResidualFrame CartesianReflectionSpace
noncomputable section

abbrev Frame := CoupledRadialFrame.Frame
def base : Frame := CoupledRadialFrame.sourcePoint
def widthIndex (k : Fin 9) : Fin 12 := ![0,1,2,3,4,3,2,1,0] k
private def coord (i : Fin 12) : Frame →L[ℝ] ℝ := ContinuousLinearMap.proj i

theorem widths_coord (x : Frame) (k : Fin 9) : widths x k=x (widthIndex k) := by
  fin_cases k <;> rfl

def directionCLM (k : Fin 9) : Frame →L[ℝ] ℝ :=
  ![coord 5,coord 6,coord 7,coord 8,0,-coord 8,-coord 7,-coord 6,-coord 5] k

theorem directionCLM_apply (k : Fin 9) (x : Frame) :
    directionCLM k x=directions x k := by
  fin_cases k <;> rfl

theorem direction_hasFDerivAt (k : Fin 9) :
    HasFDerivAt (fun x : Frame => directions x k) (directionCLM k) base := by
  have h := (directionCLM k).hasFDerivAt (x := base)
  have he : (fun x : Frame => directionCLM k x)=(fun x : Frame => directions x k) :=
    funext (directionCLM_apply k)
  change HasFDerivAt (fun x : Frame => directionCLM k x) (directionCLM k) base at h
  rwa [he] at h

def slopeA (k : Fin 9) : ℝ :=
  WidthRadialDerivative.widthSlope (SourceExactRoot.sourceRoot 6) (angleVec SourceExactRoot.sourceRoot k)
def slopeB (k : Fin 9) : ℝ :=
  CoupledRadialFrame.radiusSlope (SourceExactRoot.sourceRoot 6) (angleVec SourceExactRoot.sourceRoot k)
def radialCLM (k : Fin 9) : Frame →L[ℝ] ℝ :=
  slopeA k • coord (widthIndex k)+slopeB k • coord 11

theorem base_width (k : Fin 9) : base (widthIndex k)=angleVec SourceExactRoot.sourceRoot k := by
  rw [← widths_coord base k]
  exact congrFun (widths_source SourceExactRoot.sourceRoot) k
theorem base_direction (k : Fin 9) : directions base k=thetaOf (angleVec SourceExactRoot.sourceRoot) k :=
  congrFun (directions_source SourceExactRoot.sourceRoot) k
theorem base_radial (k : Fin 9) : radial base k=rhoK SourceExactRoot.sourceRoot k :=
  radial_source SourceExactRoot.sourceRoot k

theorem radial_hasFDerivAt (k : Fin 9) :
    HasFDerivAt (fun x : Frame => radial x k) (radialCLM k) base := by
  have harg : 0<(base 11)^2-Real.sin (base (widthIndex k))^2 := by
    rw [base_width]
    exact SourceWidthNondegenerate.source_radicand_pos k
  have h := CoupledRadialFrame.hasFDerivAt_component base (widthIndex k) harg
  rw [base_width] at h
  change HasFDerivAt (fun x : Frame => WidthRadialDerivative.rhoMinus (x 11) (x (widthIndex k)))
    (radialCLM k) base at h
  have he : (fun x : Frame => radial x k) =
      (fun x : Frame => WidthRadialDerivative.rhoMinus (x 11) (x (widthIndex k))) := by
    funext x
    rw [radial,widths_coord]
    rfl
  rwa [← he] at h

def radialVelocity (k : Fin 9) (v : Frame) : ℝ :=
  slopeA k*widths v k+slopeB k*v 11

theorem radialCLM_apply (k : Fin 9) (v : Frame) : radialCLM k v=radialVelocity k v := by
  simp only [radialCLM,add_apply,smul_apply,smul_eq_mul,coord,ContinuousLinearMap.proj_apply,
    radialVelocity,widths_coord]

def velocity (k : Fin 9) (v : Frame) : Point :=
  !₂[radialVelocity k v*Real.cos (thetaOf (angleVec SourceExactRoot.sourceRoot) k) -
      rhoK SourceExactRoot.sourceRoot k*Real.sin (thetaOf (angleVec SourceExactRoot.sourceRoot) k)*directions v k,
    radialVelocity k v*Real.sin (thetaOf (angleVec SourceExactRoot.sourceRoot) k) +
      rhoK SourceExactRoot.sourceRoot k*Real.cos (thetaOf (angleVec SourceExactRoot.sourceRoot) k)*directions v k]

private theorem point_component_derivative {f : Frame → Point}
    (hf : DifferentiableAt ℝ f base) (v : Frame) (i : Fin 2) :
    (fderiv ℝ f base v) i=fderiv ℝ (fun x : Frame => f x i) base v := by
  have h := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : Point →L[ℝ] ℝ).hasFDerivAt.comp base hf.hasFDerivAt
  have he := congrArg (fun d : Frame →L[ℝ] ℝ => d v) h.fderiv
  exact he.symm

/-- Actual Frechet derivative, for all9 centres and all independent Frame directions. -/
theorem center_source_fderiv (k : Fin 9) (v : Frame) :
    fderiv ℝ (fun x : Frame => PhysicalResidualFrame.center x k) base v=velocity k v := by
  have hr := radial_hasFDerivAt k
  have hd := direction_hasFDerivAt k
  have hx := hr.mul hd.cos
  have hy := hr.mul hd.sin
  change HasFDerivAt (fun x : Frame => radial x k*Real.cos (directions x k)) _ base at hx
  change HasFDerivAt (fun x : Frame => radial x k*Real.sin (directions x k)) _ base at hy
  have hc := (TruePinFrameDifferential.center_source_smooth k).differentiableAt (by norm_num)
  ext i
  rw [point_component_derivative hc v i]
  fin_cases i
  · change fderiv ℝ (fun x : Frame => radial x k*Real.cos (directions x k)) base v =
      radialVelocity k v*Real.cos (thetaOf (angleVec SourceExactRoot.sourceRoot) k) -
        rhoK SourceExactRoot.sourceRoot k*Real.sin (thetaOf (angleVec SourceExactRoot.sourceRoot) k)*directions v k
    rw [hx.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,radialCLM_apply,directionCLM_apply,
      base_radial,base_direction]
    ring
  · change fderiv ℝ (fun x : Frame => radial x k*Real.sin (directions x k)) base v =
      radialVelocity k v*Real.sin (thetaOf (angleVec SourceExactRoot.sourceRoot) k) +
        rhoK SourceExactRoot.sourceRoot k*Real.cos (thetaOf (angleVec SourceExactRoot.sourceRoot) k)*directions v k
    rw [hy.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,radialCLM_apply,directionCLM_apply,
      base_radial,base_direction]
    ring

def frameJac (v : Frame) : Full :=
  embed (CartesianPolarFrame.sourceJacobian (CoupledRadialFrame.sourceJacobian v))

/-- The analytic centre velocity is the actual embedded Cartesian Jacobian,
not a standalone unattached derivative formula. -/
theorem ring_frameJac (k : Fin 9) (v : Frame) :
    FullCartesianResidual.ring (frameJac v) k=velocity k v := by
  have hp := SourceFanRadiusDerivative.left_ring_derivative k
    (embed (frameCartesian base))
  have hi := embedCLM.hasFDerivAt.comp base FullCartesianDual.frameCartesian_hasFDerivAt
  have h := hp.comp base hi
  have he : (fun x : Frame => FullCartesianResidual.ring (embed (frameCartesian x)) k) =
      (fun x : Frame => PhysicalResidualFrame.center x k) :=
    funext (fun x => FullCartesianResidual.ring_frame x k)
  change HasFDerivAt (fun x : Frame => FullCartesianResidual.ring (embed (frameCartesian x)) k)
    ((TruePinCartesianDifferential.leftCLM.comp (SourceFanLengthCovector.dataCLM k)).comp
      (embedCLM.comp ((CartesianPolarFrame.sourceJacobian : Frame →L[ℝ] Frame).comp
        (CoupledRadialFrame.sourceJacobian : Frame →L[ℝ] Frame)))) base at h
  rw [he] at h
  have hv := congrArg (fun d : Frame →L[ℝ] Point => d v) h.fderiv
  rw [center_source_fderiv] at hv
  simp only [ContinuousLinearMap.comp_apply,TruePinCartesianDifferential.leftCLM_apply,
    SourceFanLengthCovector.dataCLM_apply,SourceFanRadiusDerivative.left_ringData,embedCLM_apply,frameJac]
    at hv
  change velocity k v=FullCartesianResidual.ring (frameJac v) k at hv
  exact hv.symm

theorem frameJac_radius (v : Frame) : frameJac v 22=v 11 := by
  change (CartesianPolarFrame.sourceJacobian (CoupledRadialFrame.sourceJacobian v)) 11=v 11
  change (CoupledRadialFrame.sourceJacobian v) 11=v 11
  simp only [CoupledRadialFrame.sourceJacobian,CoupledRadialFrame.triangularCLE_apply,
    CoupledRadialFrame.triangular]
  rfl

end
end N11Formalization.SourceFrameVelocity
#check @N11Formalization.SourceFrameVelocity.center_source_fderiv
#check @N11Formalization.SourceFrameVelocity.ring_frameJac
#print axioms N11Formalization.SourceFrameVelocity.ring_frameJac
