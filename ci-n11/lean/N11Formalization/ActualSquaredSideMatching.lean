import N11Formalization.ActualSharedFactorArea

/-! Actual squared-side matching, including artificial refinement edges.
The producer selects opposite slots from true shared label membership;
it does not assume a source/canonical triangle table. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSquaredSideMatching
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualCoverStructuralReduction ActualMetricAngleAtoms ActualFaceCircumradiusAtoms
open ActualSharedFactorArea ActualSwitchAtomAggregate ActualSwitchSineAtoms
open ActualBoundarySwitchMetric ActualBoundarySwitchAngles ActualBoundaryNineTies
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualRefinementBoundaryCount

def faceSideSquared {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : ℝ :=
  (19/50 : ℝ)^2*faceSquaredNormalized R A*Real.sin (faceAngle R A s)^2

def switchSideSquared {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) : ℝ :=
  (19/50 : ℝ)^2*switchSquared h hr v i*
    Real.sin (SwitchData.angle (switchData h hr v i))^2

def SideAt {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) (i j : Fin 11) : Prop :=
  (R.labels A (s+1)=i ∧ R.labels A (s+2)=j) ∨
    (R.labels A (s+1)=j ∧ R.labels A (s+2)=i)

theorem finite_opposite_slot : ∀ I J : Fin 3, I≠J →
    ∃ s : Fin 3, (s+1=I ∧ s+2=J) ∨ (s+1=J ∧ s+2=I) := by
  decide +kernel

theorem actual_opposite_slot {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {i j : Fin 11} (hij : i≠j)
    (hi : i ∈ labelSet R A) (hj : j ∈ labelSet R A) :
    ∃ s : Fin 3, SideAt R A s i j := by
  obtain ⟨I,hI⟩ := mem_labelSet.mp hi
  obtain ⟨J,hJ⟩ := mem_labelSet.mp hj
  have hIJ : I≠J := fun he => hij (by rw [← hI,← hJ,he])
  obtain ⟨s,hs⟩ := finite_opposite_slot I J hIJ
  refine ⟨s,?_⟩
  unfold SideAt
  rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨by rw [h1,hI],by rw [h2,hJ]⟩
  · exact Or.inr ⟨by rw [h1,hJ],by rw [h2,hI]⟩

theorem actual_face_half_side {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    faceSideSquared R A s =
      (dist (c (R.labels A (s+1))) (c (R.labels A (s+2)))/2)^2 := by
  unfold faceSideSquared
  rw [actual_face_squared_units]
  have hs := congrArg (fun t : ℝ => t^2) (actual_face_sine_rule R A s)
  nlinarith only [hs]

theorem actual_side_at_half_chord {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {s : Fin 3} {i j : Fin 11}
    (hs : SideAt R A s i j) :
    faceSideSquared R A s=halfChord (c i) (c j)^2 := by
  rw [actual_face_half_side]
  rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]
    rfl
  · rw [h1,h2,dist_comm (c j) (c i)]
    rfl

theorem actual_switch_half_chord {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchSideSquared h hr v i=halfChord (c (ringSite i)) (c (nextSite i))^2 := by
  have hu : (19/50 : ℝ)^2*switchSquared h hr v i=(switchData h hr v i).radius^2 := by
    unfold switchSquared
    ring
  unfold switchSideSquared
  rw [hu]
  exact SwitchData.squared_side_atom (switchData h hr v i)

theorem actual_shared_side_match_producer {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A B : R.Index} {i j : Fin 11} (hij : i≠j)
    (hAi : i ∈ labelSet R A) (hAj : j ∈ labelSet R A)
    (hBi : i ∈ labelSet R B) (hBj : j ∈ labelSet R B) :
    ∃ s t : Fin 3, SideAt R A s i j ∧ SideAt R B t i j ∧
      faceSideSquared R A s=faceSideSquared R B t := by
  obtain ⟨s,hs⟩ := actual_opposite_slot R hij hAi hAj
  obtain ⟨t,ht⟩ := actual_opposite_slot R hij hBi hBj
  refine ⟨s,t,hs,ht,?_⟩
  rw [actual_side_at_half_chord R hs,actual_side_at_half_chord R ht]

theorem actual_boundary_side_match_producer {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) :
    ∃ A : R.Index, ∃ s : Fin 3, SideAt R A s (ringSite i) (nextSite i) ∧
      faceSideSquared R A s=switchSideSquared h hr v i := by
  classical
  have hc := actual_boundary_triangle_count h hr R i
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (by rw [hc]; decide)
  have hmem := (Finset.mem_filter.mp hA).2
  obtain ⟨s,hs⟩ := actual_opposite_slot R (boundary_sites_distinct i).2.1.symm
    hmem.1 hmem.2
  refine ⟨A,s,hs,?_⟩
  rw [actual_side_at_half_chord R hs,actual_switch_half_chord]

end N11Formalization.ActualSquaredSideMatching
#check @N11Formalization.ActualSquaredSideMatching.actual_shared_side_match_producer
#check @N11Formalization.ActualSquaredSideMatching.actual_boundary_side_match_producer
#print axioms N11Formalization.ActualSquaredSideMatching.actual_shared_side_match_producer
#print axioms N11Formalization.ActualSquaredSideMatching.actual_boundary_side_match_producer
