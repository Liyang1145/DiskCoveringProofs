import N11Formalization.ActualDelaunayAngleConsumer

/-! Cotangent area atoms from the actual selected faces.
`faceSideSquared` is a half-side square, so its cotangent contribution
has no factor `1/4`. The full-side version has that factor. Shared-side
atoms retain both genuine circumradii, including unsaturated faces and
flat artificial diagonals. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualEdgeAreaAtoms

open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualCoverStructuralReduction ActualMetricAngleAtoms
open ActualFaceCircumradiusAtoms ActualSharedFactorArea
open ActualSquaredSideMatching ActualDelaunayAngleConsumer

def cotangent (a : ℝ) : ℝ := Real.cos a / Real.sin a

theorem sin_sq_cotangent {a : ℝ} (ha : Real.sin a ≠ 0) :
    Real.sin a ^ 2 * cotangent a = Real.sin a * Real.cos a := by
  unfold cotangent
  field_simp [ha]

theorem triangle_sin_cos_identity {a b d : ℝ}
    (hsum : a + b + d = Real.pi) :
    Real.sin a * Real.cos a + Real.sin b * Real.cos b +
      Real.sin d * Real.cos d = 2 * Real.sin a * Real.sin b * Real.sin d := by
  have hd : d = Real.pi - (a + b) := by linarith
  rw [hd, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_add, Real.cos_add]
  calc
    _ = Real.sin a * Real.cos a *
          (1 - (Real.sin b ^ 2 + Real.cos b ^ 2)) +
        Real.sin b * Real.cos b *
          (1 - (Real.sin a ^ 2 + Real.cos a ^ 2)) +
        2 * Real.sin a * Real.sin b *
          (Real.sin a * Real.cos b + Real.cos a * Real.sin b) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring

theorem actual_half_side_cotangent_atom {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    faceSideSquared R A s * cotangent (faceAngle R A s) =
      faceRadius R A ^ 2 * Real.sin (faceAngle R A s) *
        Real.cos (faceAngle R A s) := by
  have hd := actual_face_angle_strict R A s
  have hs := Real.sin_pos_of_pos_of_lt_pi hd.1 hd.2
  unfold faceSideSquared
  rw [actual_face_squared_units, mul_assoc, sin_sq_cotangent hs.ne']
  ring

/-- The true face area is the sum of its three half-side cotangent atoms. -/
theorem actual_face_area_eq_half_side_cotangent_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (R : Refinement c r) (A : R.Index) :
    faceArea R A = ∑ s : Fin 3,
      faceSideSquared R A s * cotangent (faceAngle R A s) := by
  have hsum := actual_face_angle_sum h R A
  rw [Fin.sum_univ_three] at hsum
  have hid := triangle_sin_cos_identity hsum
  rw [Fin.sum_univ_three]
  simp only [actual_half_side_cotangent_atom]
  unfold faceArea
  rw [show 2 * (19 / 50 : ℝ) ^ 2 * faceSquaredNormalized R A =
    2 * ((19 / 50 : ℝ) ^ 2 * faceSquaredNormalized R A) by ring,
    actual_face_squared_units]
  calc
    _ = faceRadius R A ^ 2 *
        (2 * Real.sin (faceAngle R A 0) * Real.sin (faceAngle R A 1) *
          Real.sin (faceAngle R A 2)) := by ring
    _ = _ := by rw [← hid]; ring

/-- In full-side units the same formula has the usual factor `1/4`. -/
theorem actual_face_area_eq_full_side_cotangent_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (R : Refinement c r) (A : R.Index) :
    faceArea R A = ∑ s : Fin 3,
      dist (c (R.labels A (s + 1))) (c (R.labels A (s + 2))) ^ 2 *
        cotangent (faceAngle R A s) / 4 := by
  rw [actual_face_area_eq_half_side_cotangent_sum h R A]
  apply Finset.sum_congr rfl
  intro s _
  rw [actual_face_half_side]
  ring

theorem matched_radius_cotangent_identity {a b ρ σ : ℝ}
    (ha : Real.sin a ≠ 0) (hb : Real.sin b ≠ 0)
    (hmatch : ρ * Real.sin a = σ * Real.sin b) :
    ρ ^ 2 * Real.sin a ^ 2 * cotangent a +
      σ ^ 2 * Real.sin b ^ 2 * cotangent b =
        ρ * σ * Real.sin (Real.pi - (a + b)) := by
  rw [mul_assoc (ρ ^ 2), sin_sq_cotangent ha,
    mul_assoc (σ ^ 2), sin_sq_cotangent hb, Real.sin_pi_sub, Real.sin_add]
  calc
    _ = ρ * (ρ * Real.sin a) * Real.cos a +
        σ * (σ * Real.sin b) * Real.cos b := by ring
    _ = ρ * (σ * Real.sin b) * Real.cos a +
        σ * (ρ * Real.sin a) * Real.cos b := by
      linear_combination (ρ * Real.cos a - σ * Real.cos b) * hmatch
    _ = _ := by ring

def sharedEdgeAngle {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A B : R.Index) (s t : Fin 3) : ℝ :=
  Real.pi - (faceAngle R A s + faceAngle R B t)

def sharedEdgeAreaAtom {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A B : R.Index) (s t : Fin 3) : ℝ :=
  faceSideSquared R A s * cotangent (faceAngle R A s) +
    faceSideSquared R B t * cotangent (faceAngle R B t)

theorem actual_shared_side_radius_sine_match {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A B : R.Index} {s t : Fin 3} {i j : Fin 11}
    (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    faceRadius R A * Real.sin (faceAngle R A s) =
      faceRadius R B * Real.sin (faceAngle R B t) := by
  have hside (D : R.Index) (u : Fin 3) (hu : SideAt R D u i j) :
      dist (c (R.labels D (u + 1))) (c (R.labels D (u + 2))) =
        dist (c i) (c j) := by
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  have hA := actual_face_sine_rule R A s
  have hB := actual_face_sine_rule R B t
  rw [hside A s hs] at hA
  rw [hside B t ht] at hB
  linarith

/-- The paired atom keeps the product of the two actual circumradii. -/
theorem actual_shared_edge_area_atom_eq {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A B : R.Index} {s t : Fin 3} {i j : Fin 11}
    (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    sharedEdgeAreaAtom R A B s t =
      faceRadius R A * faceRadius R B * Real.sin (sharedEdgeAngle R A B s t) := by
  have hA := actual_face_angle_strict R A s
  have hB := actual_face_angle_strict R B t
  have hsA := (Real.sin_pos_of_pos_of_lt_pi hA.1 hA.2).ne'
  have hsB := (Real.sin_pos_of_pos_of_lt_pi hB.1 hB.2).ne'
  have hm := actual_shared_side_radius_sine_match R hs ht
  unfold sharedEdgeAreaAtom sharedEdgeAngle faceSideSquared
  rw [actual_face_squared_units, actual_face_squared_units]
  exact matched_radius_cotangent_identity hsA hsB hm

theorem actual_shared_edge_angle_domain {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) {s t : Fin 3} {i j : Fin 11}
    (hij : i ≠ j) (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    0 ≤ sharedEdgeAngle R A B s t ∧ sharedEdgeAngle R A B s t < Real.pi := by
  have hsum := actual_shared_side_angle_sum_le_pi hc R hAB hij hs ht
  have hA := (actual_face_angle_strict R A s).1
  have hB := (actual_face_angle_strict R B t).1
  unfold sharedEdgeAngle
  constructor <;> linarith

/-- No face-radius saturation is required for the sine envelope. -/
theorem actual_shared_edge_area_atom_bounds {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) {s t : Fin 3} {i j : Fin 11}
    (hij : i ≠ j) (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    0 ≤ sharedEdgeAreaAtom R A B s t ∧
      sharedEdgeAreaAtom R A B s t ≤
        (19 / 50 : ℝ) ^ 2 * Real.sin (sharedEdgeAngle R A B s t) := by
  have hA := actual_face_radius_bounds h R A
  have hB := actual_face_radius_bounds h R B
  have hθ := actual_shared_edge_angle_domain h.injective R hAB hij hs ht
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2.le
  have hprod : faceRadius R A * faceRadius R B ≤ (19 / 50 : ℝ) ^ 2 := by
    have ha : faceRadius R A ≤ (19 / 50 : ℝ) := hA.2.trans hr.le
    have hb : faceRadius R B ≤ (19 / 50 : ℝ) := hB.2.trans hr.le
    calc
      _ ≤ (19 / 50 : ℝ) * (19 / 50 : ℝ) :=
        mul_le_mul ha hb hB.1.le (by norm_num)
      _ = _ := by ring
  rw [actual_shared_edge_area_atom_eq R hs ht]
  exact ⟨mul_nonneg (mul_pos hA.1 hB.1).le hsin,
    mul_le_mul_of_nonneg_right hprod hsin⟩

/-- Select true opposite slots and supply matching, the Delaunay domain,
the exact paired atom, and its nonnegative universal-radius envelope. -/
theorem actual_shared_edge_area_producer {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) {i j : Fin 11} (hij : i ≠ j)
    (hAi : i ∈ labelSet R A) (hAj : j ∈ labelSet R A)
    (hBi : i ∈ labelSet R B) (hBj : j ∈ labelSet R B) :
    ∃ s t : Fin 3, SideAt R A s i j ∧ SideAt R B t i j ∧
      faceSideSquared R A s = faceSideSquared R B t ∧
      0 ≤ sharedEdgeAngle R A B s t ∧ sharedEdgeAngle R A B s t < Real.pi ∧
      sharedEdgeAreaAtom R A B s t =
        faceRadius R A * faceRadius R B * Real.sin (sharedEdgeAngle R A B s t) ∧
      0 ≤ sharedEdgeAreaAtom R A B s t ∧
      sharedEdgeAreaAtom R A B s t ≤
        (19 / 50 : ℝ) ^ 2 * Real.sin (sharedEdgeAngle R A B s t) := by
  obtain ⟨s, t, hs, ht, he, _⟩ :=
    actual_shared_side_metric_producer h.injective R hAB hij hAi hAj hBi hBj
  have hd := actual_shared_edge_angle_domain h.injective R hAB hij hs ht
  have hb := actual_shared_edge_area_atom_bounds h hr R hAB hij hs ht
  exact ⟨s, t, hs, ht, he, hd.1, hd.2,
    actual_shared_edge_area_atom_eq R hs ht, hb.1, hb.2⟩

end N11Formalization.ActualEdgeAreaAtoms

#check @N11Formalization.ActualEdgeAreaAtoms.actual_face_area_eq_half_side_cotangent_sum
#check @N11Formalization.ActualEdgeAreaAtoms.actual_face_area_eq_full_side_cotangent_sum
#check @N11Formalization.ActualEdgeAreaAtoms.actual_shared_edge_area_producer
#print axioms N11Formalization.ActualEdgeAreaAtoms.actual_face_area_eq_half_side_cotangent_sum
#print axioms N11Formalization.ActualEdgeAreaAtoms.actual_face_area_eq_full_side_cotangent_sum
#print axioms N11Formalization.ActualEdgeAreaAtoms.actual_shared_edge_area_producer
