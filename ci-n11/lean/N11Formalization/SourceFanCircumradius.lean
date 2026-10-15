import N11Formalization.CircumcenterGeometry
import N11Formalization.SourceFanConversion

/-! Actual circumcentre/radius of independently moving fan triples, using the
EXISTING source formula shared by SourceN2. Source noncollinearity, source
value, C1 and all three circle equations are proved from the SAME frozen root.
No source table from legacy SourceN is consumed. -/
set_option autoImplicit false
namespace N11Formalization.SourceFanCircumradius
open N11Formalization PinTangentGeometry CircumcenterGeometry
open SourceFanLengthCovector SourceFanConversion CartesianReflectionSpace
noncomputable section

theorem triangleDet_from_normals (P Q H U : Point) (a b : ℝ)
    (he : U-H = a • (U-P) + b • (U-Q)) :
    triangleDet P Q H = (1-a-b) * det (U-P) (U-Q) := by
  have hQP : Q-P = (U-P)-(U-Q) := by abel
  have hHP : H-P = (U-P)-(U-H) := by abel
  rw [triangleDet, hQP, hHP, he]
  unfold det
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem source_triangle_det (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    triangleDet (ringCenter SourceExactRoot.sourceRoot k)
      (ringCenter SourceExactRoot.sourceRoot (k+1)) (sourceHub k) ≠ 0 := by
  have he := triangleDet_from_normals
    (ringCenter SourceExactRoot.sourceRoot k)
    (ringCenter SourceExactRoot.sourceRoot (k+1)) (sourceHub k)
    (Uvec SourceExactRoot.sourceRoot k) (sourceA k) (sourceB k)
    (source_normalH_expansion k hk)
  rw [he]
  exact mul_ne_zero (ne_of_gt (sourceConversion_pos k hk))
    (RootPinNormalConsumer.source_contact_normals_independent k hk)

def center (k : Fin 9) (x : Full) : Point :=
  circumcenter (FullCartesianResidual.ring x k)
    (FullCartesianResidual.ring x (k+1)) (fullHub k x)

def fanRadius (k : Fin 9) (x : Full) : ℝ :=
  ‖center k x - FullCartesianResidual.ring x k‖

theorem center_source (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    center k FullCartesianResidual.sourcePoint = Uvec SourceExactRoot.sourceRoot k := by
  unfold center FullCartesianResidual.sourcePoint
  rw [FullCartesianResidual.ring_pack, FullCartesianResidual.ring_pack]
  change circumcenter _ _ (sourceHub k) = _
  have hP := (TrueCirclePinSmooth.source_distances k).1
  have hH := source_normalH_norm k hk
  apply circumcenter_eq_of_equidistant _ _ _ _ (source_triangle_det k hk)
  · exact RootPinNormalConsumer.source_contact_equidistant k
  · exact hP.trans hH.symm

theorem fanRadius_source (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    fanRadius k FullCartesianResidual.sourcePoint = SourceExactRoot.sourceRoot 6 := by
  rw [fanRadius, center_source k hk]
  rw [FullCartesianResidual.sourcePoint, FullCartesianResidual.ring_pack]
  exact (TrueCirclePinSmooth.source_distances k).1

theorem fullHub_smooth (k : Fin 9) (x : Full) : ContDiffAt ℝ 1 (fullHub k) x := by
  unfold fullHub
  split_ifs
  · exact FullCartesianResidual.hubB_smooth x
  · exact FullCartesianResidual.hubA_smooth x

theorem center_source_smooth (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (center k) FullCartesianResidual.sourcePoint := by
  apply circumcenter_smooth (FullCartesianResidual.ring_smooth k _)
    (FullCartesianResidual.ring_smooth (k+1) _) (fullHub_smooth k _)
  simpa only [FullCartesianResidual.sourcePoint, FullCartesianResidual.ring_pack,
    ← fullHub_source k] using source_triangle_det k hk

theorem fanRadius_source_smooth (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (fanRadius k) FullCartesianResidual.sourcePoint := by
  apply ((center_source_smooth k hk).sub (FullCartesianResidual.ring_smooth k _)).norm ℝ
  apply norm_ne_zero_iff.mp
  change fanRadius k FullCartesianResidual.sourcePoint ≠ 0
  rw [fanRadius_source k hk]
  exact ne_of_gt SourceExactRoot.sourceRadius_pos

theorem source_circle_equations_eventually (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ∀ᶠ x in nhds FullCartesianResidual.sourcePoint,
      ‖center k x-FullCartesianResidual.ring x k‖^2 = (fanRadius k x)^2 ∧
      ‖center k x-FullCartesianResidual.ring x (k+1)‖^2 = (fanRadius k x)^2 ∧
      ‖center k x-fullHub k x‖^2 = (fanRadius k x)^2 := by
  have hs := triangleDet_smooth (FullCartesianResidual.ring_smooth k FullCartesianResidual.sourcePoint)
    (FullCartesianResidual.ring_smooth (k+1) FullCartesianResidual.sourcePoint)
    (fullHub_smooth k FullCartesianResidual.sourcePoint)
  have hn : triangleDet (FullCartesianResidual.ring FullCartesianResidual.sourcePoint k)
      (FullCartesianResidual.ring FullCartesianResidual.sourcePoint (k+1))
      (fullHub k FullCartesianResidual.sourcePoint) ≠ 0 := by
    simpa only [FullCartesianResidual.sourcePoint, FullCartesianResidual.ring_pack,
      ← fullHub_source k] using source_triangle_det k hk
  filter_upwards [hs.continuousAt.eventually_ne hn] with x hx
  obtain ⟨hQ,hH⟩ := circumcenter_equidistant
    (FullCartesianResidual.ring x k) (FullCartesianResidual.ring x (k+1)) (fullHub k x) hx
  exact ⟨rfl, congrArg (fun r : ℝ => r^2) hQ.symm, congrArg (fun r : ℝ => r^2) hH.symm⟩

end
end N11Formalization.SourceFanCircumradius
#check @N11Formalization.SourceFanCircumradius.source_triangle_det
#check @N11Formalization.SourceFanCircumradius.center_source
#check @N11Formalization.SourceFanCircumradius.fanRadius_source_smooth
#check @N11Formalization.SourceFanCircumradius.source_circle_equations_eventually
#print axioms N11Formalization.SourceFanCircumradius.fanRadius_source_smooth
