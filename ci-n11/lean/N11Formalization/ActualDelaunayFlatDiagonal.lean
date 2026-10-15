import N11Formalization.ActualDelaunayAngleConsumer

/-! Exact metric equalities for artificial refinement diagonals.
Coincident actual primal witnesses give four points on one empty circle.
The opposite-side signs keep the angle sum on the correct real branch.
No positive primal-edge length or generic-position assumption is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualDelaunayFlatDiagonal

open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementSideMultiplicity ActualSelectedEdgeOrientation
open ActualDelaunayAngleBounds ActualDelaunayAngleConsumer
open ActualSquaredSideMatching ActualMetricAngleAtoms FlashTiling

theorem orient_edge_swap (a b p : Point) : orient b a p = -orient a b p := by
  simp only [orient, det2, PiLp.sub_apply]
  ring

theorem positive_orient_sine {a b p : Point} (hp : 0 < orient a b p) :
    orient a b p = dist a p * dist b p *
      Real.sin (EuclideanGeometry.angle a p b) := by
  have he : orient a b p = det2 (a-p) (b-p) := by
    simp only [orient, det2, PiLp.sub_apply]
    ring
  have hh := determinant_eq_norm_sin (show 0 ≤ det2 (a-p) (b-p) by
    rw [← he]
    exact hp.le)
  rw [he]
  simpa only [dist_eq_norm, EuclideanGeometry.angle, vsub_eq_sub] using hh

theorem negative_orient_sine {a b p : Point} (hp : orient a b p < 0) :
    -orient a b p = dist a p * dist b p *
      Real.sin (EuclideanGeometry.angle a p b) := by
  have hh := positive_orient_sine (a := b) (b := a) (p := p)
    (by rw [orient_edge_swap]; linarith)
  rw [orient_edge_swap] at hh
  simpa only [EuclideanGeometry.angle_comm, mul_comm, mul_assoc, mul_left_comm] using hh

theorem edge_dot_cosine (a b p : Point) :
    edgeDot a b p = dist a p * dist b p *
      Real.cos (EuclideanGeometry.angle a p b) := by
  have hh := InnerProductGeometry.cos_angle_mul_norm_mul_norm (a-p) (b-p)
  calc
    edgeDot a b p = inner ℝ (a-p) (b-p) := rfl
    _ = Real.cos (InnerProductGeometry.angle (a-p) (b-p)) * (‖a-p‖ * ‖b-p‖) := hh.symm
    _ = _ := by
      simp only [dist_eq_norm, EuclideanGeometry.angle, vsub_eq_sub]
      ring

theorem angle_sum_eq_pi_of_common_circle {a b p q u : Point}
    (hp : 0 < orient a b p) (hq : orient a b q < 0)
    (hua : dist u a = dist u b) (hup : dist u a = dist u p)
    (huq : dist u a = dist u q) :
    EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b = Real.pi := by
  have hsP := positive_orient_sine hp
  have hsQ := negative_orient_sine hq
  have hcP := edge_dot_cosine a b p
  have hcQ := edge_dot_cosine a b q
  have hzero : edgeDot a b p * (-orient a b q) + edgeDot a b q * orient a b p = 0 := by
    rw [point_circle_gap_identity hua hup, ← huq, sub_self, mul_zero]
  have hproduct :
      (dist a p * dist b p) * (dist a q * dist b q) *
        Real.sin (EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b) =
      edgeDot a b p * (-orient a b q) + edgeDot a b q * orient a b p := by
    rw [Real.sin_add, hcP, hsQ, hcQ, hsP]
    ring
  have hP : 0 < dist a p * dist b p := by
    apply lt_of_le_of_ne (mul_nonneg dist_nonneg dist_nonneg)
    intro hz
    rw [← hz, zero_mul] at hsP
    linarith
  have hQ : 0 < dist a q * dist b q := by
    apply lt_of_le_of_ne (mul_nonneg dist_nonneg dist_nonneg)
    intro hz
    rw [← hz, zero_mul] at hsQ
    linarith
  have hsin : Real.sin (EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b) = 0 :=
    (mul_eq_zero.mp (hproduct.trans hzero)).resolve_left (mul_pos hP hQ).ne'
  have hle := angle_sum_le_pi_of_empty_circle hp hq hua hup huq.le
  apply le_antisymm hle
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  have ho : orient p a b = orient a b p := ActualIncidentFacetAdjacency.orient_cycle _ _ _
  have hpa := (ActualFaceCircumradiusAtoms.actual_angle_strict_of_positive_orient
    (a := p) (b := a) (k := b) (ho ▸ hp)).1
  have hsum : 0 < EuclideanGeometry.angle a p b + EuclideanGeometry.angle a q b :=
    add_pos_of_pos_of_nonneg hpa (EuclideanGeometry.angle_nonneg _ _ _)
  have hpositive := Real.sin_pos_of_pos_of_lt_pi hsum hlt
  rw [hsin] at hpositive
  exact (lt_irrefl 0) hpositive

theorem actual_same_witness_edge_angle_sum_eq_pi {c : Fin 11 → Point}
    {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) (hw : R.witness A = R.witness B)
    {i j k l : Fin 11} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j)
    (hAi : i ∈ labelSet R A) (hAj : j ∈ labelSet R A) (hAk : k ∈ labelSet R A)
    (hBi : i ∈ labelSet R B) (hBj : j ∈ labelSet R B) (hBl : l ∈ labelSet R B) :
    EuclideanGeometry.angle (c i) (c k) (c j) +
      EuclideanGeometry.angle (c i) (c l) (c j) = Real.pi := by
  have hNi := nearest_of_label_mem R hAi
  have hNj := nearest_of_label_mem R hAj
  have hNk := nearest_of_label_mem R hAk
  have hMi := nearest_of_label_mem R hBi
  have hMl := nearest_of_label_mem R hBl
  have heij : dist (R.witness A) (c i) = dist (R.witness A) (c j) :=
    le_antisymm (hNi j) (hNj i)
  have heik : dist (R.witness A) (c i) = dist (R.witness A) (c k) :=
    le_antisymm (hNi k) (hNk i)
  have heil : dist (R.witness A) (c i) = dist (R.witness A) (c l) := by
    rw [hw]
    exact le_antisymm (hMi l) (hMl i)
  have hop := same_witness_edge_opposite R hAB hw hij hki hkj hli hlj
    hAi hAj hAk hBi hBj hBl
  rcases mul_neg_iff.mp hop with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · exact angle_sum_eq_pi_of_common_circle hp hq heij heik heil
  · have hp' : 0 < orient (c j) (c i) (c k) := by rw [orient_edge_swap]; linarith
    have hq' : orient (c j) (c i) (c l) < 0 := by rw [orient_edge_swap]; linarith
    have hh := angle_sum_eq_pi_of_common_circle hp' hq' heij.symm
      (heij.symm.trans heik) (heij.symm.trans heil)
    simpa only [EuclideanGeometry.angle_comm] using hh

theorem actual_same_witness_side_angle_sum_eq_pi {c : Fin 11 → Point}
    {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) (hw : R.witness A = R.witness B)
    {s t : Fin 3} {i j : Fin 11} (hij : i ≠ j)
    (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    faceAngle R A s + faceAngle R B t = Real.pi := by
  have hd : ∀ u : Fin 3, u ≠ u+1 ∧ u ≠ u+2 := by decide
  have hside (D : R.Index) (u : Fin 3) (hu : SideAt R D u i j) :
      i ∈ labelSet R D ∧ j ∈ labelSet R D ∧
        R.labels D u ≠ i ∧ R.labels D u ≠ j := by
    have h1 := (Refinement.labels_injective R D).ne (hd u).1
    have h2 := (Refinement.labels_injective R D).ne (hd u).2
    rcases hu with ⟨hu1,hu2⟩ | ⟨hu1,hu2⟩
    · exact ⟨mem_labelSet.mpr ⟨u+1,hu1⟩,mem_labelSet.mpr ⟨u+2,hu2⟩,
        hu1 ▸ h1,hu2 ▸ h2⟩
    · exact ⟨mem_labelSet.mpr ⟨u+2,hu2⟩,mem_labelSet.mpr ⟨u+1,hu1⟩,
        hu2 ▸ h2,hu1 ▸ h1⟩
  obtain ⟨hAi,hAj,hki,hkj⟩ := hside A s hs
  obtain ⟨hBi,hBj,hli,hlj⟩ := hside B t ht
  rw [face_angle_at_side R hs, face_angle_at_side R ht]
  exact actual_same_witness_edge_angle_sum_eq_pi R hAB hw hij hki hkj hli hlj
    hAi hAj (mem_labelSet.mpr ⟨s,rfl⟩) hBi hBj (mem_labelSet.mpr ⟨t,rfl⟩)

theorem cos_div_sin_sum_eq_zero {α β : ℝ}
    (hα0 : 0 < α) (hαπ : α < Real.pi)
    (hβ0 : 0 < β) (hβπ : β < Real.pi) (hsum : α+β = Real.pi) :
    Real.cos α / Real.sin α + Real.cos β / Real.sin β = 0 := by
  have hα := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have hβ := Real.sin_pos_of_pos_of_lt_pi hβ0 hβπ
  have he : Real.cos α / Real.sin α + Real.cos β / Real.sin β =
      Real.sin (α+β) / (Real.sin α * Real.sin β) := by
    rw [Real.sin_add]
    field_simp [hα.ne',hβ.ne']
    ring
  rw [he, hsum, Real.sin_pi, zero_div]

theorem actual_same_witness_side_cotangent_sum_eq_zero {c : Fin 11 → Point}
    {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) (hw : R.witness A = R.witness B)
    {s t : Fin 3} {i j : Fin 11} (hij : i ≠ j)
    (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    Real.cos (faceAngle R A s) / Real.sin (faceAngle R A s) +
      Real.cos (faceAngle R B t) / Real.sin (faceAngle R B t) = 0 := by
  have hA := ActualFaceCircumradiusAtoms.actual_face_angle_strict R A s
  have hB := ActualFaceCircumradiusAtoms.actual_face_angle_strict R B t
  exact cos_div_sin_sum_eq_zero hA.1 hA.2 hB.1 hB.2
    (actual_same_witness_side_angle_sum_eq_pi R hAB hw hij hs ht)

theorem actual_same_witness_side_metric_producer {c : Fin 11 → Point}
    {r : ℝ} (R : Refinement c r) {A B : R.Index}
    (hAB : A ≠ B) (hw : R.witness A = R.witness B)
    {i j : Fin 11} (hij : i ≠ j)
    (hAi : i ∈ labelSet R A) (hAj : j ∈ labelSet R A)
    (hBi : i ∈ labelSet R B) (hBj : j ∈ labelSet R B) :
    ∃ s t : Fin 3, SideAt R A s i j ∧ SideAt R B t i j ∧
      faceSideSquared R A s = faceSideSquared R B t ∧
      faceAngle R A s + faceAngle R B t = Real.pi ∧
      Real.cos (faceAngle R A s) / Real.sin (faceAngle R A s) +
        Real.cos (faceAngle R B t) / Real.sin (faceAngle R B t) = 0 := by
  obtain ⟨s,t,hs,ht,he⟩ := actual_shared_side_match_producer R hij hAi hAj hBi hBj
  exact ⟨s,t,hs,ht,he,actual_same_witness_side_angle_sum_eq_pi R hAB hw hij hs ht,
    actual_same_witness_side_cotangent_sum_eq_zero R hAB hw hij hs ht⟩

end N11Formalization.ActualDelaunayFlatDiagonal
#check @N11Formalization.ActualDelaunayFlatDiagonal.angle_sum_eq_pi_of_common_circle
#check @N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_edge_angle_sum_eq_pi
#check @N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_angle_sum_eq_pi
#check @N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_cotangent_sum_eq_zero
#check @N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_metric_producer
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.angle_sum_eq_pi_of_common_circle
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_edge_angle_sum_eq_pi
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_angle_sum_eq_pi
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_cotangent_sum_eq_zero
#print axioms N11Formalization.ActualDelaunayFlatDiagonal.actual_same_witness_side_metric_producer
