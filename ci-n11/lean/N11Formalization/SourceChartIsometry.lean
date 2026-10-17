import N11Formalization.SourceLocalSharpGain
import N11Formalization.Patch120K5Actual
import N11Formalization.ResumeNetworkIsometry

/-! True circle-chart gauge. The SAME rotation acts on anchors/C/Z, retains
all51 primal constraints and does not assume chart points are local.
The local norm remains explicit until paid by actual DBM cells. -/
set_option autoImplicit false
namespace N11Formalization.SourceChartIsometry
open N11Formalization ResumeNetwork ResumeGlobal FlashLeafRootChart
open SourceResponseFluxIdentity
noncomputable section

def rotate (a : ℝ) (p : Point) : Point :=
  !₂[Real.cos a*p 0-Real.sin a*p 1,Real.sin a*p 0+Real.cos a*p 1]

theorem rotate_circle (a t : ℝ) : rotate a (N11Formalization.circleMap t)=
    N11Formalization.circleMap (a+t) := by
  apply PiLp.ext
  intro q
  fin_cases q <;> simp [rotate,N11Formalization.circleMap,Real.cos_add,Real.sin_add]

theorem rotate_inverse (a : ℝ) (p : Point) : rotate (-a) (rotate a p)=p := by
  have h := Real.cos_sq_add_sin_sq a
  apply PiLp.ext
  intro q
  fin_cases q <;> simp [rotate,Real.cos_neg,Real.sin_neg]
  · nlinarith [congrArg (fun t => t*p 0) h]
  · nlinarith [congrArg (fun t => t*p 1) h]

def rotation (a : ℝ) : Point ≃ Point where
  toFun := rotate a
  invFun := rotate (-a)
  left_inv := rotate_inverse a
  right_inv := by intro p; simpa only [neg_neg] using rotate_inverse (-a) p

theorem rotate_dist (a : ℝ) (p q : Point) : dist (rotate a p) (rotate a q)=dist p q := by
  have ht := Real.cos_sq_add_sin_sq a
  have hs : ‖rotate a p-rotate a q‖^2=‖p-q‖^2 := by
    rw [PinTangentGeometry.norm_sq_coords,PinTangentGeometry.norm_sq_coords]
    simp only [PiLp.sub_apply,rotate,Matrix.cons_val_zero,Matrix.cons_val_one]
    nlinarith [congrArg (fun t => t*(p 0-q 0)^2) ht,
      congrArg (fun t => t*(p 1-q 1)^2) ht]
  rw [dist_eq_norm,dist_eq_norm]
  nlinarith [norm_nonneg (rotate a p-rotate a q),norm_nonneg (p-q)]

def cellAngles (y : Fin 9 → ℝ) (j : Fin 9) : ℝ :=
  anchorAngle Patch120K5Actual.L Patch120K5Actual.D y j.val
def chartAnchors (y : Fin 9 → ℝ) (j : Fin 9) : Point :=
  N11Formalization.circleMap (cellAngles y j)
def displacement (y : Fin 9 → ℝ) (j : Fin 9) : ℝ :=
  (cellAngles y j-cellAngles y 6)-
    (cellAngles (chartY SourceExactRoot.sourceRoot Patch120K5Actual.L Patch120K5Actual.D) j-
      cellAngles (chartY SourceExactRoot.sourceRoot Patch120K5Actual.L Patch120K5Actual.D) 6)

theorem displacement_pin (y : Fin 9 → ℝ) : displacement y 6=0 := by
  simp [displacement]

theorem displacement_eq_h (y : Fin 9 → ℝ) (j : Fin 9) :
    displacement y j=Patch120K5Actual.h SourceExactRoot.sourceRoot y j :=
  (Patch120K5Actual.h_eq_actual_perturbation _ _ _).symm

def rootChart : Fin 9 → ℝ :=
  chartY SourceExactRoot.sourceRoot Patch120K5Actual.L Patch120K5Actual.D
def gauge (y : Fin 9 → ℝ) : ℝ :=
  rawAnchorAngle SourceExactRoot.sourceRoot 2+
    cellAngles rootChart 6-cellAngles y 6

/-- Exact source chart branch, including periodic wrap. No false equality
between different lifts of the sourceAngle real values is assumed. -/
theorem rotation_chart (y : Fin 9 → ℝ) (j : Fin 9) :
    rotation (gauge y) (chartAnchors y j)=
      SourceLocalSharpGain.displacedAnchors (displacement y) j := by
  have hsrc := canonAnchors_eq_circleMap_chart SourceExactRoot.sourceRoot
    Patch120K5Actual.L Patch120K5Actual.D
    (show Patch120K5Actual.D≠0 from FlashLeafRootChart.D_pos.ne') j
  change SourcePositiveHarmonicConsumer.sourceAnchors j=
    N11Formalization.circleMap
      (rawAnchorAngle SourceExactRoot.sourceRoot 2+cellAngles rootChart j) at hsrc
  have hc : rotate (displacement y j) (SourcePositiveHarmonicConsumer.sourceAnchors j)=
      SourceLocalSharpGain.displacedAnchors (displacement y) j := by
    rw [sourceAnchors_circle,rotate_circle,SourceLocalSharpGain.displacedAnchors_circle]
    congr 1
    ring
  rw [← hc,hsrc,rotate_circle]
  change rotate (gauge y) (N11Formalization.circleMap (cellAngles y j))=_
  rw [rotate_circle]
  congr 1
  simp only [gauge,displacement,rootChart]
  ring

theorem oracle_gauge (y : Fin 9 → ℝ) :
    V2 (chartAnchors y)=V2 (SourceLocalSharpGain.displacedAnchors (displacement y)) := by
  have he : rotation (gauge y) ∘ chartAnchors y=
      SourceLocalSharpGain.displacedAnchors (displacement y) :=
    funext (rotation_chart y)
  have h := ResumeNetworkIsometry.oracle_isometry (rotation (gauge y))
    (rotate_dist (gauge y)) (chartAnchors y)
  rw [he] at h
  exact h.symm

/-- Cell-independent actual oracle consumer. ONLY the pinned ball membership
is left, not source geometry/rotation/H/N/G/remainders. -/
theorem chart_gain_of_norm (y : Fin 9 → ℝ)
    (hr : Real.sqrt (∑ j : Fin 9,displacement y j^2)≤(729/50000 : ℝ)) :
    (∑ j : Fin 9,displacement y j^2)/100000≤
      V2 (chartAnchors y)-SourceExactRoot.sourceRadius^2 := by
  rw [oracle_gauge]
  exact SourceLocalSharpGain.actual_local_gain _ (displacement_pin y) hr

/-- Actual51 constraints transported together, including all slack face rows. -/
theorem chart_radius_of_norm (y : Fin 9 → ℝ)
    (hr : Real.sqrt (∑ j : Fin 9,displacement y j^2)≤(729/50000 : ℝ))
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius≤r := by
  have h := (ResumeNetworkIsometry.feasible_map (rotation (gauge y))
    (rotate_dist (gauge y)) (chartAnchors y) C Z r).mpr hf
  have he : rotation (gauge y) ∘ chartAnchors y=
      SourceLocalSharpGain.displacedAnchors (displacement y) :=
    funext (rotation_chart y)
  rw [he] at h
  exact SourceLocalSharpGain.feasible_radius_lower _ (displacement_pin y) hr _ _ r h

end
end N11Formalization.SourceChartIsometry
#check @N11Formalization.SourceChartIsometry.rotation_chart
#check @N11Formalization.SourceChartIsometry.chart_gain_of_norm
#check @N11Formalization.SourceChartIsometry.chart_radius_of_norm
#print axioms N11Formalization.SourceChartIsometry.chart_radius_of_norm
