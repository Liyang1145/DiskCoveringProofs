import N11Formalization.SourceFanCircumradius
import N11Formalization.ResumeAttainmentFace2

/-! Central triple (hub0,hub1,ring6) is paid independently. Source equal distances,
normal independence, positive LENGTH conversion, actual circumcentre/radius C1
and three circle equations are proved. No ring-contact premise is reused as if
it supplied the central geometry. -/
set_option autoImplicit false
namespace N11Formalization.SourceCentralGeometry
open N11Formalization PinTangentGeometry PinBranchBind CircumcenterGeometry
open SourceFanLengthCovector SourceFanConversion SourceFanCircumradius
open CartesianReflectionSpace
noncomputable section

def P : Point := hub0 SourceExactRoot.sourceRoot
def Q : Point := hub1 SourceExactRoot.sourceRoot
def H : Point := ringCenter SourceExactRoot.sourceRoot 6
def U : Point := wPoint SourceExactRoot.sourceRoot
def R : ℝ := SourceExactRoot.sourceRoot 6
def nP : Point := U-P
def nQ : Point := U-Q
def nH : Point := U-H

theorem source_distances : ‖U-P‖=R ∧ ‖U-Q‖=R ∧ ‖U-H‖=R := by
  have hR : 0 ≤ SourceExactRoot.sourceRoot 6 := le_of_lt SourceExactRoot.sourceRadius_pos
  have hW : ((SourceExactRoot.sourceRoot 5-SourceExactRoot.sourceRoot 4)/2)^2 ≤
      (SourceExactRoot.sourceRoot 6)^2 := by
    linarith [HorizontalTruePin.source_central_radicand_pos]
  have hres : residual SourceExactRoot.sourceRoot = 0 := by
    funext i
    have hi := congrFun SourceExactRoot.sourceRoot_mem.2 (⟨i.val,by omega⟩ : Fin 12)
    simpa [TCSystem] using hi
  exact ⟨by simpa only [P, U, R, dist_eq_norm] using ResumeAttainment.dist_W_hub0 _ hR hW,
    by simpa only [Q, U, R, dist_eq_norm] using ResumeAttainment.dist_W_hub1 _ hR hW,
    by simpa only [H, U, R, dist_eq_norm] using ResumeAttainment.dist_W_C6 _ hres⟩

theorem height_coordinate_pos : 0 < U 1 := by
  change 0 < Real.sqrt ((SourceExactRoot.sourceRoot 6)^2 -
    ((SourceExactRoot.sourceRoot 5-SourceExactRoot.sourceRoot 4)/2)^2)
  exact Real.sqrt_pos.mpr HorizontalTruePin.source_central_radicand_pos

theorem source_height_pos : 0 < pinHeight P Q U := by
  apply norm_pos_iff.mpr
  intro hzero
  have hi := congrArg (fun p : Point => p 1) hzero
  have hp := height_coordinate_pos
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply,
    P, Q, chordMid, hub0, hub1, Matrix.cons_val_one, zero_add, smul_zero] at hi
  have hi' : U 1 = 0 := by simpa using hi
  rw [hi'] at hp
  exact (lt_irrefl 0) hp

theorem source_normals_independent : det nP nQ ≠ 0 :=
  pin_normals_independent HorizontalTruePin.source_hubs_distinct
    (source_distances.1.trans source_distances.2.1.symm) source_height_pos

theorem source_ring_above : U 1 + (1 : ℝ)/10 ≤ H 1 := by
  have hmem := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hRing := (ndRingBox_mem hmem 6 1).1
  have hPin := (ndWPointBox_mem hmem 1).2
  have hmargin : (1 : ℝ)/10 ≤
      (ndRingBox ndBox 6 1).lo - (ndWPointBox ndBox 1).hi := by
    have he : (((1/10 : ℚ) : ℝ)) ≤
        (((ndRingBox ndBox 6 1).lo-(ndWPointBox ndBox 1).hi : ℚ) : ℝ) :=
      (Rat.cast_le).mpr ndWp_read
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using he
  change U 1 + (1 : ℝ)/10 ≤ H 1
  change (ndRingBox ndBox 6 1).lo ≤ H 1 at hRing
  change U 1 ≤ (ndWPointBox ndBox 1).hi at hPin
  linarith

theorem sourceY_pos : 0 < hubCoord P Q U H := by
  apply (sameBranch_iff P Q U H source_height_pos).mpr
  rw [inner_coords]
  have hmid0 : (U-chordMid P Q) 0=0 := by
    simp [U, P, Q, wPoint, chordMid, hub0, hub1, smul_eq_mul]
    ring
  have hmid1 : (U-chordMid P Q) 1=U 1 := by
    simp [P, Q, chordMid, hub0, hub1]
  have hh1 : (H-chordMid P Q) 1=H 1 := by
    simp [P, Q, chordMid, hub0, hub1]
  rw [hmid0, hmid1, hh1, mul_zero, zero_add]
  have hHpos : 0 < H 1 := by linarith [height_coordinate_pos, source_ring_above]
  exact mul_pos hHpos height_coordinate_pos

def a : ℝ := coefficientA nP nQ nH
def b : ℝ := coefficientB nP nQ nH
def conversion : ℝ := 1-a-b

theorem normalH_expansion : nH = a • nP+b • nQ :=
  normal_expansion _ _ _ source_normals_independent

theorem conversion_eq : conversion = hubCoord P Q U H/pinHeight P Q U :=
  conversion_eq_hubCoord_div_height P Q U H
    (source_distances.1.trans source_distances.2.1.symm)
    source_normals_independent source_height_pos

theorem conversion_pos : 0 < conversion := by
  rw [conversion_eq]
  exact div_pos sourceY_pos source_height_pos

theorem source_triangle_det : triangleDet P Q H ≠ 0 := by
  rw [triangleDet_from_normals P Q H U a b normalH_expansion]
  exact mul_ne_zero (ne_of_gt conversion_pos) source_normals_independent

def betaP : ℝ := -a/conversion
def betaQ : ℝ := -b/conversion
def betaH : ℝ := 1/conversion

theorem beta_sum_one : betaP+betaQ+betaH=1 := by
  have hne := ne_of_gt conversion_pos
  unfold betaP betaQ betaH
  field_simp [hne]
  unfold conversion
  ring

theorem beta_center_identity : U=betaP • P+betaQ • Q+betaH • H := by
  have hne := ne_of_gt conversion_pos
  ext i
  have he := congrArg (fun n : Point => n i) normalH_expansion
  simp only [nH, nP, nQ, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at he
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  unfold betaP betaQ betaH
  field_simp [hne]
  unfold conversion
  linear_combination he

def center (x : Full) : Point :=
  circumcenter (FullCartesianResidual.hubA x) (FullCartesianResidual.hubB x)
    (FullCartesianResidual.ring x 6)
def centralRadius (x : Full) : ℝ := ‖center x-FullCartesianResidual.hubA x‖

theorem center_source : center FullCartesianResidual.sourcePoint=U :=
  circumcenter_eq_of_equidistant P Q H U source_triangle_det
    (source_distances.1.trans source_distances.2.1.symm)
    (source_distances.1.trans source_distances.2.2.symm)

theorem centralRadius_source : centralRadius FullCartesianResidual.sourcePoint=R := by
  rw [centralRadius, center_source]
  exact source_distances.1

theorem center_source_smooth :
    ContDiffAt ℝ 1 center FullCartesianResidual.sourcePoint := by
  apply circumcenter_smooth (FullCartesianResidual.hubA_smooth _)
    (FullCartesianResidual.hubB_smooth _) (FullCartesianResidual.ring_smooth 6 _)
  simpa only [FullCartesianResidual.sourcePoint, FullCartesianResidual.hubA_pack,
    FullCartesianResidual.hubB_pack, FullCartesianResidual.ring_pack, P, Q, H]
    using source_triangle_det

theorem centralRadius_source_smooth :
    ContDiffAt ℝ 1 centralRadius FullCartesianResidual.sourcePoint := by
  apply (center_source_smooth.sub (FullCartesianResidual.hubA_smooth _)).norm ℝ
  apply norm_ne_zero_iff.mp
  change centralRadius FullCartesianResidual.sourcePoint ≠ 0
  rw [centralRadius_source]
  exact ne_of_gt SourceExactRoot.sourceRadius_pos

theorem circle_equations_eventually :
    ∀ᶠ x in nhds FullCartesianResidual.sourcePoint,
      ‖center x-FullCartesianResidual.hubA x‖^2=(centralRadius x)^2 ∧
      ‖center x-FullCartesianResidual.hubB x‖^2=(centralRadius x)^2 ∧
      ‖center x-FullCartesianResidual.ring x 6‖^2=(centralRadius x)^2 := by
  have hs := triangleDet_smooth (FullCartesianResidual.hubA_smooth FullCartesianResidual.sourcePoint)
    (FullCartesianResidual.hubB_smooth FullCartesianResidual.sourcePoint)
    (FullCartesianResidual.ring_smooth 6 FullCartesianResidual.sourcePoint)
  have hn : triangleDet (FullCartesianResidual.hubA FullCartesianResidual.sourcePoint)
      (FullCartesianResidual.hubB FullCartesianResidual.sourcePoint)
      (FullCartesianResidual.ring FullCartesianResidual.sourcePoint 6) ≠ 0 := by
    simpa only [FullCartesianResidual.sourcePoint, FullCartesianResidual.hubA_pack,
      FullCartesianResidual.hubB_pack, FullCartesianResidual.ring_pack, P, Q, H]
      using source_triangle_det
  filter_upwards [hs.continuousAt.eventually_ne hn] with x hx
  obtain ⟨hQ,hH⟩ := circumcenter_equidistant _ _ _ hx
  exact ⟨rfl, congrArg (fun r : ℝ => r^2) hQ.symm, congrArg (fun r : ℝ => r^2) hH.symm⟩

end
end N11Formalization.SourceCentralGeometry
#check @N11Formalization.SourceCentralGeometry.conversion_pos
#check @N11Formalization.SourceCentralGeometry.centralRadius_source_smooth
#print axioms N11Formalization.SourceCentralGeometry.conversion_pos
#print axioms N11Formalization.SourceCentralGeometry.centralRadius_source_smooth
