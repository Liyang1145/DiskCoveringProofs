import N11Formalization.ActualQ0FanTransitions

/-! Every actual q0 selected triangle is one of the nine true boundary
hub triangles or one of the two true central triangles. All11 are distinct.
No frozen canonical face table is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ0FacePartition
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualHubTriangleCensus
open ActualQ0BoundaryFans ActualRefinementHubCount ActualRefinementEulerCount
open ActualRingDirectionOrder ActualRingLinkBoundaryData

local instance {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    DecidableEq R.Index := Classical.decEq _

theorem ring_hub_triple_unique : ∀ i j : Fin 9, ∀ b d : Bool,
    ({ringSite i,nextSite i,hubSite b} : Finset (Fin 11)) =
      {ringSite j,nextSite j,hubSite d} → i=j ∧ b=d := by decide +kernel

theorem ring_hub_triple_not_central : ∀ i : Fin 9, ∀ b : Bool,
    ¬ ((9 : Fin 11) ∈ ({ringSite i,nextSite i,hubSite b} : Finset (Fin 11)) ∧
      (10 : Fin 11) ∈ ({ringSite i,nextSite i,hubSite b} : Finset (Fin 11))) := by
  decide +kernel

theorem hub_mem_ring_hub_triple : ∀ i : Fin 9, ∀ b d : Bool,
    hubSite b ∈ ({ringSite i,nextSite i,hubSite d} : Finset (Fin 11)) ↔ b=d := by
  decide +kernel

theorem FanData.faces_injective {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (F : FanData R) : Function.Injective F.faces := by
  intro i j he
  have hs := congrArg (labelSet R) he
  rw [F.labels,F.labels] at hs
  exact (ring_hub_triple_unique i j _ _ hs).1

def fanFaces {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r} (F : FanData R) :
    Finset R.Index := by
  classical
  exact Finset.univ.image F.faces

def colorFaces {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r} (F : FanData R)
    (b : Bool) : Finset R.Index := by
  classical
  exact (Finset.univ.filter (fun i => F.colors i=b)).image F.faces

theorem FanData.fan_central_disjoint {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (F : FanData R) : Disjoint (fanFaces F) (hubTriangles R) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hc
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  have hh := (Finset.mem_filter.mp hc).2
  rw [F.labels] at hh
  exact ring_hub_triple_not_central i (F.colors i) hh

theorem actual_q0_all_faces {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r} (F : FanData R) :
    fanFaces F ∪ hubTriangles R = Finset.univ := by
  classical
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint (FanData.fan_central_disjoint F),
    actual_hub_triangle_count h hr R,Finset.card_univ,actual_faces_eleven h hr R]
  unfold fanFaces
  rw [Finset.card_image_of_injective _ (FanData.faces_injective F),Finset.card_univ]
  decide

theorem actual_q0_hub_triangle_partition {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : FanData R) (b : Bool) :
    siteTriangles R (hubSite b) = colorFaces F b ∪ hubTriangles R := by
  classical
  ext a
  rw [mem_siteTriangles]
  constructor
  · intro ha
    have hm : a ∈ fanFaces F ∪ hubTriangles R := by rw [actual_q0_all_faces h hr F]; simp
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
      rw [F.labels,hub_mem_ring_hub_triple] at ha
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha.symm⟩,rfl⟩)
    · exact Finset.mem_union_right _ hm
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      rw [F.labels,hub_mem_ring_hub_triple]
      exact (Finset.mem_filter.mp hi).2.symm
    · have hh := (Finset.mem_filter.mp ha).2
      cases b
      · exact hh.2
      · exact hh.1

theorem actual_q0_hub_degree_color_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : FanData R) (b : Bool) :
    (neighbors R (hubSite b)).card =
      (Finset.univ.filter (fun i : Fin 9 => F.colors i=b)).card+2 := by
  classical
  rw [← actual_hub_face_neighbor_count h hr R (hubSite_hub b),
    actual_q0_hub_triangle_partition h hr F b]
  have hd : Disjoint (colorFaces F b) (hubTriangles R) := by
    apply (FanData.fan_central_disjoint F).mono_left
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [Finset.card_union_of_disjoint hd,actual_hub_triangle_count h hr R,colorFaces,
    Finset.card_image_of_injective _ (FanData.faces_injective F)]

end N11Formalization.ActualQ0FacePartition
#check @N11Formalization.ActualQ0FacePartition.actual_q0_all_faces
#check @N11Formalization.ActualQ0FacePartition.actual_q0_hub_degree_color_count
#print axioms N11Formalization.ActualQ0FacePartition.actual_q0_all_faces
#print axioms N11Formalization.ActualQ0FacePartition.actual_q0_hub_degree_color_count
