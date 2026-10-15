import N11Formalization.SourceBoundaryMultiplierIntervals

/-! Staged exact endpoint readouts. Each literal is checked against the sound
root-expression interval, not accepted from diagnostic floating-point output.
The stages prevent repeated transcendental expansion in the final inequalities. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundaryIntervalReadout
open N11Formalization RatInterval SourceBoundaryMultiplierIntervals

macro "geometry_endpoint_eval" : tactic =>
  `(tactic| (simp only [ringBox,pinBox,wBox,rounded]; nd_eval))

theorem ring00 : ringBox 0 0=intv (-76471/100000) (-76470/100000) := by geometry_endpoint_eval
theorem ring01 : ringBox 0 1=intv (-29837/100000) (-29836/100000) := by geometry_endpoint_eval
theorem ring10 : ringBox 1 0=intv (-35579/100000) (-35578/100000) := by geometry_endpoint_eval
theorem ring11 : ringBox 1 1=intv (-67362/100000) (-67361/100000) := by geometry_endpoint_eval
theorem ring20 : ringBox 2 0=intv (9483/100000) (9484/100000) := by geometry_endpoint_eval
theorem ring21 : ringBox 2 1=intv (-69443/100000) (-69442/100000) := by geometry_endpoint_eval
theorem ring30 : ringBox 3 0=intv (61581/100000) (61582/100000) := by geometry_endpoint_eval
theorem ring31 : ringBox 3 1=intv (-59861/100000) (-59860/100000) := by geometry_endpoint_eval
theorem ring40 : ringBox 4 0=intv (89252/100000) (89253/100000) := by geometry_endpoint_eval
theorem ring41 : ringBox 4 1=intv 0 0 := by geometry_endpoint_eval
theorem ring50 : ringBox 5 0=intv (61581/100000) (61582/100000) := by geometry_endpoint_eval
theorem ring51 : ringBox 5 1=intv (59860/100000) (59861/100000) := by geometry_endpoint_eval
theorem ring60 : ringBox 6 0=intv (9483/100000) (9484/100000) := by geometry_endpoint_eval
theorem ring61 : ringBox 6 1=intv (69442/100000) (69443/100000) := by geometry_endpoint_eval
theorem ring70 : ringBox 7 0=intv (-35579/100000) (-35578/100000) := by geometry_endpoint_eval
theorem ring71 : ringBox 7 1=intv (67361/100000) (67362/100000) := by geometry_endpoint_eval
theorem ring80 : ringBox 8 0=intv (-76471/100000) (-76470/100000) := by geometry_endpoint_eval
theorem ring81 : ringBox 8 1=intv (29836/100000) (29837/100000) := by geometry_endpoint_eval

theorem pin10 : pinBox 1 0=intv (-11637/100000) (-11636/100000) := by geometry_endpoint_eval
theorem pin11 : pinBox 1 1=intv (-37855/100000) (-37854/100000) := by geometry_endpoint_eval
theorem pin20 : pinBox 2 0=intv (30603/100000) (30604/100000) := by geometry_endpoint_eval
theorem pin21 : pinBox 2 1=intv (-37855/100000) (-37854/100000) := by geometry_endpoint_eval
theorem pin30 : pinBox 3 0=intv (58274/100000) (58275/100000) := by geometry_endpoint_eval
theorem pin31 : pinBox 3 1=intv (-22007/100000) (-22006/100000) := by geometry_endpoint_eval
theorem pin80 : pinBox 8 0=intv (-52942/100000) (-52941/100000) := by geometry_endpoint_eval
theorem pin81 : pinBox 8 1=intv (-1/100000) (1/100000) := by geometry_endpoint_eval
theorem w0 : wBox 0=intv (6177/100000) (6178/100000) := by geometry_endpoint_eval
theorem w1 : wBox 1=intv (31588/100000) (31589/100000) := by geometry_endpoint_eval

theorem sine4 :
    rounded (sinTotLag (ndAngleBox ndBox 4))=intv (37854/100000) (37855/100000) := by
  simp only [rounded]
  nd_eval
theorem rho4 :
    rounded (ndRhoBox ndBox 4)=intv (89252/100000) (89253/100000) := by
  simp only [rounded]
  nd_eval
theorem den4 : slopeDen=intv (3306/100000) (3307/100000) := by
  simp only [slopeDen,rounded]
  nd_eval
theorem slope4 : slopeBox=intv (1021634/100000) (1021982/100000) := by
  unfold slopeBox
  rw [sine4,rho4]
  unfold div inv
  rw [den4]
  norm_num [rounded,mul,intv]

end N11Formalization.SourceBoundaryIntervalReadout
#print axioms N11Formalization.SourceBoundaryIntervalReadout.slope4
