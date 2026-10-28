import N11Formalization.ActualEdgeAreaAtoms
import N11Formalization.ActualBoundaryDelaunayAngle

/-! Boundary paired area atoms from the genuine selected face and switch.
The switch angle is the half-apex `SwitchData.angle`; both original
circumradii remain in the exact sine product. Half-side cotangent atoms
have no additional factor `1/4`. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryEdgeAreaAtoms

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualMetricAngleAtoms
open ActualFaceCircumradiusAtoms ActualSharedFactorArea ActualSquaredSideMatching
open ActualBoundaryNineTies ActualSwitchAtomAggregate ActualBoundarySwitchMetric
open ActualBoundarySwitchAngles ActualSwitchSineAtoms ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualEdgeAreaAtoms ActualBoundaryDelaunayAngle

def boundaryEdgeAngle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) (A : R.Index) (s : Fin 3) : ℝ :=
  Real.pi - (faceAngle R A s + SwitchData.angle (switchData h hr v i))

def boundaryEdgeAreaAtom {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) (A : R.Index) (s : Fin 3) : ℝ :=
  faceSideSquared R A s * cotangent (faceAngle R A s) +
    switchSideSquared h hr v i * cotangent (SwitchData.angle (switchData h hr v i))

theorem actual_switch_squared_radius_units {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (i : Fin 9) :
    (19 / 50 : ℝ) ^ 2 * switchSquared h hr v i =
      (switchData h hr v i).radius ^ 2 := by
  unfold switchSquared
  ring

/-- The actual switch triangle contributes one half-side cotangent atom. -/
theorem actual_switch_area_eq_half_side_cotangent {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (i : Fin 9) :
    switchArea h hr v i =
      switchSideSquared h hr v i * cotangent (SwitchData.angle (switchData h hr v i)) := by
  have hb := SwitchData.angle_bounds (switchData h hr v i)
  have hs := Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [Real.pi_pos])
  unfold switchArea switchSideSquared
  simp only [actual_switch_squared_radius_units, Real.sin_two_mul]
  calc
    _ = (switchData h hr v i).radius ^ 2 *
        (Real.sin (SwitchData.angle (switchData h hr v i)) *
          Real.cos (SwitchData.angle (switchData h hr v i))) := by ring
    _ = (switchData h hr v i).radius ^ 2 *
        (Real.sin (SwitchData.angle (switchData h hr v i)) ^ 2 *
          cotangent (SwitchData.angle (switchData h hr v i))) := by
      rw [sin_sq_cotangent hs.ne']
    _ = _ := by ring

theorem actual_boundary_side_radius_sine_match {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    faceRadius R A * Real.sin (faceAngle R A s) =
      (switchData h hr v i).radius * Real.sin (SwitchData.angle (switchData h hr v i)) := by
  have hside : dist (c (R.labels A (s + 1))) (c (R.labels A (s + 2))) =
      dist (c (ringSite i)) (c (nextSite i)) := by
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  have hface := actual_face_sine_rule R A s
  rw [hside] at hface
  rw [SwitchData.chord_sine, (switchData h hr v i).chord_exact]
  unfold halfChord
  linarith

theorem actual_boundary_edge_angle_strict {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    0 < boundaryEdgeAngle h hr R v i A s ∧
      boundaryEdgeAngle h hr R v i A s < Real.pi := by
  have hsum := actual_boundary_side_angle_sum_lt_pi h hr R v i hs
  have hface := (actual_face_angle_strict R A s).1
  have hb := (SwitchData.angle_bounds (switchData h hr v i)).1
  unfold boundaryEdgeAngle
  constructor <;> linarith

/-- The closed sine-envelope domain is produced from actual boundary geometry. -/
theorem actual_boundary_edge_angle_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    0 ≤ boundaryEdgeAngle h hr R v i A s ∧
      boundaryEdgeAngle h hr R v i A s ≤ Real.pi := by
  have hd := actual_boundary_edge_angle_strict h hr R v i hs
  exact ⟨hd.1.le, hd.2.le⟩

/-- Exact area keeps the product of the original face and switch radii. -/
theorem actual_boundary_edge_area_atom_eq {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    boundaryEdgeAreaAtom h hr R v i A s =
      faceRadius R A * (switchData h hr v i).radius *
        Real.sin (boundaryEdgeAngle h hr R v i A s) := by
  have hA := actual_face_angle_strict R A s
  have hb := SwitchData.angle_bounds (switchData h hr v i)
  have hsA := (Real.sin_pos_of_pos_of_lt_pi hA.1 hA.2).ne'
  have hsb := (Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [Real.pi_pos])).ne'
  have hm := actual_boundary_side_radius_sine_match h hr R v i hs
  unfold boundaryEdgeAreaAtom boundaryEdgeAngle faceSideSquared switchSideSquared
  rw [actual_face_squared_units, actual_switch_squared_radius_units]
  exact matched_radius_cotangent_identity hsA hsb hm

theorem actual_boundary_edge_area_atom_eq_face_atom_add_switch_area
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) (A : R.Index) (s : Fin 3) :
    boundaryEdgeAreaAtom h hr R v i A s =
      faceSideSquared R A s * cotangent (faceAngle R A s) + switchArea h hr v i := by
  unfold boundaryEdgeAreaAtom
  rw [actual_switch_area_eq_half_side_cotangent]

/-- Uniform-radius bounds are inequalities; neither true radius is saturated. -/
theorem actual_boundary_edge_area_atom_bounds {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite i) (nextSite i)) :
    0 ≤ boundaryEdgeAreaAtom h hr R v i A s ∧
      boundaryEdgeAreaAtom h hr R v i A s ≤
        (19 / 50 : ℝ) ^ 2 * Real.sin (boundaryEdgeAngle h hr R v i A s) := by
  have hA := actual_face_radius_bounds h R A
  have hb := (switchData h hr v i).radius_pos
  have hθ := actual_boundary_edge_angle_domain h hr R v i hs
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hprod : faceRadius R A * (switchData h hr v i).radius ≤ (19 / 50 : ℝ) ^ 2 := by
    have ha : faceRadius R A ≤ (19 / 50 : ℝ) := hA.2.trans hr.le
    have hsrad : (switchData h hr v i).radius ≤ (19 / 50 : ℝ) :=
      (switchData h hr v i).original_radius.trans hr.le
    calc
      _ ≤ (19 / 50 : ℝ) * (19 / 50 : ℝ) :=
        mul_le_mul ha hsrad hb.le (by norm_num)
      _ = _ := by ring
  rw [actual_boundary_edge_area_atom_eq h hr R v i hs]
  exact ⟨mul_nonneg (mul_pos hA.1 hb).le hsin,
    mul_le_mul_of_nonneg_right hprod hsin⟩

/-- Select the genuine boundary opposite slot and produce every paired-atom
domain and equality needed for the finite edge-area aggregation. -/
theorem actual_boundary_edge_area_producer {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) :
    ∃ A : R.Index, ∃ s : Fin 3, SideAt R A s (ringSite i) (nextSite i) ∧
      faceSideSquared R A s = switchSideSquared h hr v i ∧
      0 ≤ boundaryEdgeAngle h hr R v i A s ∧
      boundaryEdgeAngle h hr R v i A s ≤ Real.pi ∧
      boundaryEdgeAreaAtom h hr R v i A s =
        faceRadius R A * (switchData h hr v i).radius *
          Real.sin (boundaryEdgeAngle h hr R v i A s) ∧
      boundaryEdgeAreaAtom h hr R v i A s =
        faceSideSquared R A s * cotangent (faceAngle R A s) + switchArea h hr v i ∧
      0 ≤ boundaryEdgeAreaAtom h hr R v i A s ∧
      boundaryEdgeAreaAtom h hr R v i A s ≤
        (19 / 50 : ℝ) ^ 2 * Real.sin (boundaryEdgeAngle h hr R v i A s) := by
  obtain ⟨A, s, hs, he, _⟩ := actual_boundary_side_metric_producer h hr R v i
  have hd := actual_boundary_edge_angle_domain h hr R v i hs
  have hb := actual_boundary_edge_area_atom_bounds h hr R v i hs
  exact ⟨A, s, hs, he, hd.1, hd.2,
    actual_boundary_edge_area_atom_eq h hr R v i hs,
    actual_boundary_edge_area_atom_eq_face_atom_add_switch_area h hr R v i A s,
    hb.1, hb.2⟩

end N11Formalization.ActualBoundaryEdgeAreaAtoms

#check @N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_switch_area_eq_half_side_cotangent
#check @N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_boundary_edge_area_producer
#print axioms N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_switch_area_eq_half_side_cotangent
#print axioms N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_boundary_edge_angle_domain
#print axioms N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_boundary_edge_area_atom_eq
#print axioms N11Formalization.ActualBoundaryEdgeAreaAtoms.actual_boundary_edge_area_producer
