import N11Formalization.ActualOwnedSectorDecomposition

/-! Actual real face and ownership-sector angle atoms.
The nonnegative determinant picks the correct sine branch, including
flat ownership sectors. No angle sum at a site is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualMetricAngleAtoms
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualRingDirectionOrder ActualRingLinkBoundaryData
open ActualBoundaryCyclicOrder ActualOwnedSectorDecomposition FlashTiling

theorem determinant_eq_norm_sin {x y : Point} (hdet : 0 ≤ det2 x y) :
    det2 x y = ‖x‖*‖y‖*Real.sin (InnerProductGeometry.angle x y) := by
  have hs := InnerProductGeometry.sin_angle_mul_norm_mul_norm x y
  have hg := ActualSwitchWedgeArea.determinant_gram x y
  have he : inner ℝ x x*inner ℝ y y-inner ℝ x y*inner ℝ x y=det2 x y^2 := by
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    nlinarith [hg]
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hdet] at hs
  simpa only [mul_comm,mul_assoc,mul_left_comm] using hs.symm

def faceAngle {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : ℝ :=
  EuclideanGeometry.angle (c (R.labels A (s+1))) (c (R.labels A s))
    (c (R.labels A (s+2)))

theorem actual_face_angle_bounds {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    0 ≤ faceAngle R A s ∧ faceAngle R A s ≤ Real.pi :=
  ⟨EuclideanGeometry.angle_nonneg _ _ _,EuclideanGeometry.angle_le_pi _ _ _⟩

theorem actual_face_angle_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (R : Refinement c r) (A : R.Index) :
    ∑ s : Fin 3, faceAngle R A s=Real.pi := by
  have hn : c (R.labels A 0) ≠ c (R.labels A 1) :=
    h.injective.ne ((Refinement.labels_injective R A).ne (by decide : (0 : Fin 3) ≠ 1))
  have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c (R.labels A 1)) (p₂ := c (R.labels A 0)) (c (R.labels A 2)) hn
  rw [Fin.sum_univ_three]
  change EuclideanGeometry.angle (c (R.labels A 1)) (c (R.labels A 0)) (c (R.labels A 2)) +
      EuclideanGeometry.angle (c (R.labels A 2)) (c (R.labels A 1)) (c (R.labels A 0)) +
      EuclideanGeometry.angle (c (R.labels A 0)) (c (R.labels A 2)) (c (R.labels A 1))=Real.pi
  linarith

theorem actual_face_area_angle {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) :
    orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2))/2 =
      dist (c (R.labels A 1)) (c (R.labels A 0)) *
        dist (c (R.labels A 2)) (c (R.labels A 0)) *
          Real.sin (faceAngle R A 0)/2 := by
  have hh := determinant_eq_norm_sin (Refinement.real_triangle R A).2.2.le
  simpa only [orient,dist_eq_norm,faceAngle,EuclideanGeometry.angle,
    vsub_eq_sub,zero_add] using congrArg (fun t : ℝ => t/2) hh

def sectorAngle {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  EuclideanGeometry.angle (switchPoint v i) (c (nextSite i))
    (switchPoint v (nextRing i))

theorem actual_sector_angle_bounds {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    0 ≤ sectorAngle v i ∧ sectorAngle v i ≤ Real.pi := by
  exact ⟨InnerProductGeometry.angle_nonneg _ _,InnerProductGeometry.angle_le_pi _ _⟩

theorem actual_sector_area_angle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    orient (c (nextSite i)) (switchPoint v i) (switchPoint v (nextRing i))/2 =
      dist (switchPoint v i) (c (nextSite i)) *
        dist (switchPoint v (nextRing i)) (c (nextSite i)) *
          Real.sin (sectorAngle v i)/2 := by
  have hh := determinant_eq_norm_sin
    (ActualOwnedChordGeometry.actual_owned_chord_triangle_nonneg h hr v i)
  simpa only [orient,dist_eq_norm,sectorAngle,EuclideanGeometry.angle,
    vsub_eq_sub,nextSite,switchPoint] using congrArg (fun t : ℝ => t/2) hh

def leftRadius {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  dist (switchPoint v i) (c (nextSite i))

def rightRadius {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  dist (switchPoint v (nextRing i)) (c (nextSite i))

theorem actual_sector_endpoint_radii {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    0 ≤ leftRadius v i ∧ leftRadius v i ≤ r ∧
      0 ≤ rightRadius v i ∧ rightRadius v i ≤ r := by
  refine ⟨dist_nonneg,?_,dist_nonneg,?_⟩
  · have hr := (v.tie i).radius
    rw [(v.tie i).equidistant] at hr
    exact hr
  · exact (v.tie (nextRing i)).radius

theorem cosine_law (a b C : Point) :
    dist a b^2 = dist a C^2+dist b C^2 -
      2*dist a C*dist b C*Real.cos (EuclideanGeometry.angle a C b) := by
  have hv : a-b=(a-C)-(b-C) := by module
  have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm (a-C) (b-C)
  simp only [dist_eq_norm,EuclideanGeometry.angle,vsub_eq_sub]
  rw [hv,norm_sub_sq_real]
  nlinarith only [hc]

theorem actual_sector_cosine_law {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    dist (switchPoint v i) (switchPoint v (nextRing i))^2 =
      leftRadius v i^2+rightRadius v i^2 -
        2*leftRadius v i*rightRadius v i*Real.cos (sectorAngle v i) :=
  cosine_law _ _ _

end N11Formalization.ActualMetricAngleAtoms
#check @N11Formalization.ActualMetricAngleAtoms.actual_face_angle_sum
#check @N11Formalization.ActualMetricAngleAtoms.actual_face_area_angle
#check @N11Formalization.ActualMetricAngleAtoms.actual_sector_angle_bounds
#check @N11Formalization.ActualMetricAngleAtoms.actual_sector_area_angle
#check @N11Formalization.ActualMetricAngleAtoms.actual_sector_endpoint_radii
#check @N11Formalization.ActualMetricAngleAtoms.actual_sector_cosine_law
#print axioms N11Formalization.ActualMetricAngleAtoms.actual_face_angle_sum
#print axioms N11Formalization.ActualMetricAngleAtoms.actual_sector_area_angle
#print axioms N11Formalization.ActualMetricAngleAtoms.actual_sector_cosine_law
