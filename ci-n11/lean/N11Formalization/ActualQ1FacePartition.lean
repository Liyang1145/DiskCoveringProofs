import N11Formalization.ActualQ1OrderedCoreFans

/-! Productive actual q1 all-face partition: eight core hub faces,
two central faces and one selected ring ear, exactly all11 indices.
Hub degree equals core owner-edge count+2. No metric exclusion premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ1FacePartition
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementHubCount ActualRefinementEulerCount
open ActualHubTriangleCensus ActualSelectedRingEdges
open ActualQ1CoreFans ActualQ1CoreTransitions ActualQ1CoreCycle ActualQ0BoundaryFans

local instance {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    DecidableEq R.Index := Classical.decEq _

def coreFaces {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r} (F : CoreFans R) :
    Finset R.Index := Finset.univ.image F.faces

def colorFaces {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r} (F : CoreFans R)
    (b : Bool) : Finset R.Index := by
  classical
  exact (Finset.univ.filter (fun i => F.colors i=b)).image F.faces

theorem CoreFans.core_central_disjoint {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (F : CoreFans R) : Disjoint (coreFaces F) (hubTriangles R) := by
  classical
  apply Finset.disjoint_left.mpr
  intro A hA hc
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
  have hh := (Finset.mem_filter.mp hc).2
  rw [F.labels] at hh
  exact core_triangle_not_central F.ear.center i (F.colors i) hh

theorem CoreFans.core_ear_disjoint {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (F : CoreFans R) : Disjoint (coreFaces F) ({F.ear.index} : Finset R.Index) := by
  classical
  apply Finset.disjoint_left.mpr
  intro A hA he
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
  exact F.no_ear_face i (Finset.mem_singleton.mp he)

theorem CoreFans.central_ear_disjoint {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (F : CoreFans R) : Disjoint (hubTriangles R) ({F.ear.index} : Finset R.Index) := by
  classical
  apply Finset.disjoint_left.mpr
  intro A hA he
  have heq := Finset.mem_singleton.mp he
  subst A
  have hh := (Finset.mem_filter.mp hA).2.1
  rw [F.ear.labels] at hh
  exact (ear_set_no_hubs F.ear.center).1 hh

theorem actual_q1_all_faces {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r} (F : CoreFans R) :
    (coreFaces F ∪ hubTriangles R) ∪ {F.ear.index} = Finset.univ := by
  classical
  have hd : Disjoint (coreFaces F ∪ hubTriangles R) ({F.ear.index} : Finset R.Index) :=
    Finset.disjoint_union_left.mpr ⟨CoreFans.core_ear_disjoint F,CoreFans.central_ear_disjoint F⟩
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_union_of_disjoint (CoreFans.core_central_disjoint F),
    actual_hub_triangle_count h hr R,Finset.card_singleton,Finset.card_univ,
    actual_faces_eleven h hr R,coreFaces,
    Finset.card_image_of_injective _ (ActualQ1CoreTransitions.CoreFans.faces_injective F),
    Finset.card_univ]
  decide

theorem core_hub_membership : ∀ e : Fin 9, ∀ i : Fin 8, ∀ b d : Bool,
    hubSite b ∈ ({ActualRingDirectionOrder.ringSite (coreSite e i),
      ActualRingDirectionOrder.ringSite (coreSite e (coreNext i)),hubSite d} : Finset (Fin 11)) ↔
        b=d := by decide +kernel

theorem hub_not_in_ear : ∀ e : Fin 9, ∀ b : Bool,
    hubSite b ∉ ({ActualRingLinkBoundaryData.prevSite e,ActualRingDirectionOrder.ringSite e,
      ActualRingLinkBoundaryData.nextSite e} : Finset (Fin 11)) := by decide +kernel

theorem actual_q1_hub_face_partition {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : CoreFans R) (b : Bool) :
    siteTriangles R (hubSite b)=colorFaces F b ∪ hubTriangles R := by
  classical
  ext A
  rw [mem_siteTriangles]
  constructor
  · intro hA
    have hm : A ∈ (coreFaces F ∪ hubTriangles R) ∪ {F.ear.index} := by
      rw [actual_q1_all_faces h hr F]; simp
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
        rw [F.labels,core_hub_membership] at hA
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA.symm⟩,rfl⟩)
      · exact Finset.mem_union_right _ hm
    · have he := Finset.mem_singleton.mp hm
      subst A
      rw [F.ear.labels] at hA
      exact (hub_not_in_ear F.ear.center b hA).elim
  · intro hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hA
      rw [F.labels,core_hub_membership]
      exact (Finset.mem_filter.mp hi).2.symm
    · have hh := (Finset.mem_filter.mp hA).2
      cases b
      · exact hh.2
      · exact hh.1

theorem actual_q1_hub_degree_owner_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : CoreFans R) (b : Bool) :
    (neighbors R (hubSite b)).card =
      (Finset.univ.filter (fun i : Fin 8 => F.colors i=b)).card+2 := by
  classical
  rw [← actual_hub_face_neighbor_count h hr R (hubSite_hub b),
    actual_q1_hub_face_partition h hr F b]
  have hd : Disjoint (colorFaces F b) (hubTriangles R) := by
    apply (CoreFans.core_central_disjoint F).mono_left
    intro A hA
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [Finset.card_union_of_disjoint hd,actual_hub_triangle_count h hr R,colorFaces,
    Finset.card_image_of_injective _ (ActualQ1CoreTransitions.CoreFans.faces_injective F)]

end N11Formalization.ActualQ1FacePartition
#check @N11Formalization.ActualQ1FacePartition.actual_q1_all_faces
#check @N11Formalization.ActualQ1FacePartition.actual_q1_hub_degree_owner_count
#print axioms N11Formalization.ActualQ1FacePartition.actual_q1_all_faces
#print axioms N11Formalization.ActualQ1FacePartition.actual_q1_hub_degree_owner_count
