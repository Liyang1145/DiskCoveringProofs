import N11Formalization.ActualDelaunayAngleBounds
import N11Formalization.ActualSquaredSideMatching

/-! Actual opposite-angle inequalities on every selected shared edge.
The common-circle equations, empty-circle inequality and opposite-side
signs are produced from the actual refinement. Artificial fan diagonals
remain covered, including the case of a common primal witness.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualDelaunayAngleConsumer

open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementSideMultiplicity ActualSelectedEdgeOrientation
open ActualDelaunayAngleBounds ActualSquaredSideMatching ActualMetricAngleAtoms
open FlashTiling

theorem actual_shared_edge_angle_sum_le_pi {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B)
    {i j k l : Fin 11} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j)
    (hAi : i ∈ labelSet R A) (hAj : j ∈ labelSet R A)
    (hAk : k ∈ labelSet R A)
    (hBi : i ∈ labelSet R B) (hBj : j ∈ labelSet R B)
    (hBl : l ∈ labelSet R B) :
    EuclideanGeometry.angle (c i) (c k) (c j) +
      EuclideanGeometry.angle (c i) (c l) (c j) ≤ Real.pi := by
  have hNi := nearest_of_label_mem R hAi
  have hNj := nearest_of_label_mem R hAj
  have hNk := nearest_of_label_mem R hAk
  have heij : dist (R.witness A) (c i) = dist (R.witness A) (c j) :=
    le_antisymm (hNi j) (hNj i)
  have heik : dist (R.witness A) (c i) = dist (R.witness A) (c k) :=
    le_antisymm (hNi k) (hNk i)
  have hgap : dist (R.witness A) (c i) ≤ dist (R.witness A) (c l) := hNi l
  have hop := actual_shared_edge_opposite hc R hAB hij hki hkj hli hlj
    hAi hAj hAk hBi hBj hBl
  rcases mul_neg_iff.mp hop with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · exact angle_sum_le_pi_of_empty_circle hp hq heij heik hgap
  · have hswap (p : Point) : orient (c j) (c i) p = -orient (c i) (c j) p := by
      simp only [orient,det2,PiLp.sub_apply]
      ring
    have hp' : 0 < orient (c j) (c i) (c k) := by
      rw [hswap]
      linarith
    have hq' : orient (c j) (c i) (c l) < 0 := by
      rw [hswap]
      linarith
    have hejk : dist (R.witness A) (c j) = dist (R.witness A) (c k) :=
      heij.symm.trans heik
    have hh := angle_sum_le_pi_of_empty_circle hp' hq' heij.symm hejk
      (by rwa [← heij])
    simpa only [EuclideanGeometry.angle_comm] using hh

theorem face_angle_at_side {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {s : Fin 3} {i j : Fin 11}
    (hs : SideAt R A s i j) :
    faceAngle R A s = EuclideanGeometry.angle (c i) (c (R.labels A s)) (c j) := by
  unfold faceAngle
  rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2,EuclideanGeometry.angle_comm]

theorem actual_shared_side_angle_sum_le_pi {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) {s t : Fin 3} {i j : Fin 11}
    (hij : i ≠ j) (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    faceAngle R A s + faceAngle R B t ≤ Real.pi := by
  have hd : ∀ s : Fin 3, s ≠ s+1 ∧ s ≠ s+2 := by decide
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
  rw [face_angle_at_side R hs,face_angle_at_side R ht]
  exact actual_shared_edge_angle_sum_le_pi hc R hAB hij hki hkj hli hlj
    hAi hAj (mem_labelSet.mpr ⟨s,rfl⟩) hBi hBj (mem_labelSet.mpr ⟨t,rfl⟩)

theorem actual_shared_side_metric_producer {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) {i j : Fin 11} (hij : i ≠ j)
    (hAi : i ∈ labelSet R A) (hAj : j ∈ labelSet R A)
    (hBi : i ∈ labelSet R B) (hBj : j ∈ labelSet R B) :
    ∃ s t : Fin 3, SideAt R A s i j ∧ SideAt R B t i j ∧
      faceSideSquared R A s = faceSideSquared R B t ∧
      faceAngle R A s + faceAngle R B t ≤ Real.pi := by
  obtain ⟨s,t,hs,ht,he⟩ := actual_shared_side_match_producer R hij hAi hAj hBi hBj
  exact ⟨s,t,hs,ht,he,actual_shared_side_angle_sum_le_pi hc R hAB hij hs ht⟩

theorem cos_div_sin_sum_nonneg {α β : ℝ}
    (hα0 : 0 < α) (hαπ : α < Real.pi)
    (hβ0 : 0 < β) (hβπ : β < Real.pi)
    (hsum : α+β ≤ Real.pi) :
    0 ≤ Real.cos α / Real.sin α + Real.cos β / Real.sin β := by
  have hα := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have hβ := Real.sin_pos_of_pos_of_lt_pi hβ0 hβπ
  have hn := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ α+β) hsum
  have he : Real.cos α / Real.sin α + Real.cos β / Real.sin β =
      Real.sin (α+β) / (Real.sin α * Real.sin β) := by
    rw [Real.sin_add]
    field_simp [hα.ne',hβ.ne']
    <;> ring
  rw [he]
  exact div_nonneg hn (mul_pos hα hβ).le

theorem actual_shared_side_cotangent_sum_nonneg {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {A B : R.Index} (hAB : A ≠ B) {s t : Fin 3} {i j : Fin 11}
    (hij : i ≠ j) (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    0 ≤ Real.cos (faceAngle R A s) / Real.sin (faceAngle R A s) +
      Real.cos (faceAngle R B t) / Real.sin (faceAngle R B t) := by
  have hA := ActualFaceCircumradiusAtoms.actual_face_angle_strict R A s
  have hB := ActualFaceCircumradiusAtoms.actual_face_angle_strict R B t
  exact cos_div_sin_sum_nonneg hA.1 hA.2 hB.1 hB.2
    (actual_shared_side_angle_sum_le_pi hc R hAB hij hs ht)

end N11Formalization.ActualDelaunayAngleConsumer
#check @N11Formalization.ActualDelaunayAngleConsumer.actual_shared_edge_angle_sum_le_pi
#check @N11Formalization.ActualDelaunayAngleConsumer.actual_shared_side_metric_producer
#check @N11Formalization.ActualDelaunayAngleConsumer.actual_shared_side_cotangent_sum_nonneg
#print axioms N11Formalization.ActualDelaunayAngleConsumer.actual_shared_edge_angle_sum_le_pi
#print axioms N11Formalization.ActualDelaunayAngleConsumer.actual_shared_side_metric_producer
#print axioms N11Formalization.ActualDelaunayAngleConsumer.actual_shared_side_cotangent_sum_nonneg
