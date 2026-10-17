import N11Formalization.ActualCanonicalSitePermutation
import N11Formalization.ActualQ0OrderedTwoFans
import N11Formalization.ActualQ0FacePartition
import N11Formalization.ActualQ1FacePartition
import N11Formalization.ActualQ0FourRunNormalization
import N11Formalization.ActualQ1RunDegrees
import N11Formalization.ActualRefinementDoubleCounting

/-! Exact actual q0/q1 graph transport by whole-label permutations.
Run lengths and the q1 core cut remain finite parameters. No symmetry of
the original metric configuration and no graph-matching premise is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualOrderedMetricGraphs
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementEarCount
open ActualRefinementHubCount ActualRefinementDoubleCounting
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualCanonicalSitePermutation ActualQ0BoundaryFans ActualQ0OrderedTwoFans
open ActualQ1CoreCycle ActualQ1CoreFans ActualQ1OrderedCoreFans
open ActualHubTriangleCensus

def labelMap (p : Equiv.Perm (Fin 11)) (s : Finset (Fin 11)) : Finset (Fin 11) :=
  s.image p

def faceEdges (s : Finset (Finset (Fin 11))) : Finset (Finset (Fin 11)) :=
  s.biUnion (fun f => f.powersetCard 2)

def actualFaces {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    Finset (Finset (Fin 11)) := by
  classical
  exact Finset.univ.image (labelSet R)

theorem actual_edges_from_faces {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    edges R = faceEdges (actualFaces R) := by
  classical
  simp only [faceEdges,actualFaces,Finset.image_biUnion,edges]

theorem labelMap_powersetCard (p : Equiv.Perm (Fin 11)) (s : Finset (Fin 11)) :
    (labelMap p s).powersetCard 2 = (s.powersetCard 2).image (labelMap p) := by
  have he := Finset.powersetCard_map p.toEmbedding 2 s
  rw [Finset.map_eq_image,Finset.map_eq_image] at he
  change (s.image p).powersetCard 2 =
    (s.powersetCard 2).image (fun t => t.map p.toEmbedding) at he
  simp only [Finset.map_eq_image] at he
  change (labelMap p s).powersetCard 2 = (s.powersetCard 2).image (labelMap p) at he
  exact he

theorem faceEdges_labelMap (p : Equiv.Perm (Fin 11)) (s : Finset (Finset (Fin 11))) :
    faceEdges (s.image (labelMap p)) = (faceEdges s).image (labelMap p) := by
  simp only [faceEdges,Finset.image_biUnion,Finset.biUnion_image,labelMap_powersetCard]

def centralFace (i : Fin 9) : Finset (Fin 11) := {9,10,ringSite i}

def q0Fan (m i : Fin 9) : Finset (Fin 11) :=
  {ringSite i,nextSite i,if i.val < m.val then 9 else 10}

def q0Faces (m : Fin 9) : Finset (Finset (Fin 11)) :=
  Finset.univ.image (q0Fan m) ∪ {centralFace 0,centralFace m}

def q0Edges (m : Fin 9) : Finset (Finset (Fin 11)) := faceEdges (q0Faces m)

theorem centralFace_ne : ∀ i j : Fin 9, i ≠ j → centralFace i ≠ centralFace j := by
  decide +kernel

theorem centralFace_mem_hubs : ∀ i : Fin 9,
    (9 : Fin 11) ∈ centralFace i ∧ (10 : Fin 11) ∈ centralFace i := by
  intro i
  simp [centralFace]

theorem labelMap_central (k : Fin 9) (b : Bool) (i : Fin 9) :
    labelMap (canonicalPerm k b) (centralFace i) = centralFace (i+k) := by
  simp only [labelMap,centralFace,Finset.image_insert,Finset.image_singleton,
    canonicalPerm_hub9,canonicalPerm_hub10,canonicalPerm_ring]
  cases b <;> simp only [hubSite,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
  · ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto

theorem q0_fan_transport {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedData R) (i : Fin 9) :
    labelMap (canonicalPerm O.cut (O.fans.colors O.cut)) (q0Fan O.run_length i) =
      labelSet R (O.fans.faces (i+O.cut)) := by
  rw [O.true_shifted_fan]
  simp only [labelMap,q0Fan,Finset.image_insert,Finset.image_singleton,
    canonicalPerm_ring,nextSite,canonicalPerm_ring,next_shift]
  split_ifs <;> simp only [canonicalPerm_hub9,canonicalPerm_hub10]

theorem q0_second {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedData R) : O.run_length+O.cut = O.second := by
  rw [O.length_exact]
  abel

theorem q0_faces_transport {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedData R) :
    actualFaces R = (q0Faces O.run_length).image
      (labelMap (canonicalPerm O.cut (O.fans.colors O.cut))) := by
  classical
  ext f
  constructor
  · rintro hf
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hf
    have ha : a ∈ ActualQ0FacePartition.fanFaces O.fans ∪ hubTriangles R := by
      rw [ActualQ0FacePartition.actual_q0_all_faces h hr O.fans]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
      let i : Fin 9 := j-O.cut
      have hi : i+O.cut=j := by dsimp [i]; abel
      refine Finset.mem_image.mpr ⟨q0Fan O.run_length i,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),?_⟩
      rw [q0_fan_transport,hi]
    · rcases O.central_labels a ha with ha | ha
      · refine Finset.mem_image.mpr ⟨centralFace 0,
          Finset.mem_union_right _ (by simp),?_⟩
        rw [labelMap_central,zero_add]
        exact ha.symm
      · refine Finset.mem_image.mpr ⟨centralFace O.run_length,
          Finset.mem_union_right _ (by simp),?_⟩
        rw [labelMap_central,q0_second]
        exact ha.symm
  · rintro hf
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hf
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_image.mpr ⟨O.fans.faces (i+O.cut),Finset.mem_univ _,
        (q0_fan_transport O i).symm⟩
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · obtain ⟨a,ha⟩ := O.central_first
        refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
        rw [labelMap_central,zero_add]
        exact ha
      · have he := Finset.mem_singleton.mp hs
        subst s
        obtain ⟨a,ha⟩ := O.central_second
        refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
        rw [labelMap_central,q0_second]
        exact ha

theorem q0_edges_transport {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedData R) :
    edges R = (q0Edges O.run_length).image
      (labelMap (canonicalPerm O.cut (O.fans.colors O.cut))) := by
  rw [actual_edges_from_faces,q0_faces_transport h hr O,faceEdges_labelMap]
  rfl

def q1Fan (k m i : Fin 8) : Finset (Fin 11) :=
  {ringSite (coreSite 0 (i+k)),ringSite (coreSite 0 (coreNext (i+k))),
    if i.val < m.val then 9 else 10}

def q1Ear : Finset (Fin 11) := {prevSite 0,ringSite 0,nextSite 0}

def q1Faces (k m : Fin 8) : Finset (Finset (Fin 11)) :=
  (Finset.univ.image (q1Fan k m) ∪
    {centralFace (coreSite 0 k),centralFace (coreSite 0 (m+k))}) ∪ {q1Ear}

def q1Edges (k m : Fin 8) : Finset (Finset (Fin 11)) := faceEdges (q1Faces k m)

theorem coreSite_shift (e : Fin 9) (i : Fin 8) : coreSite 0 i+e=coreSite e i := by
  unfold coreSite
  simp only [zero_add]
  abel

theorem labelMap_ear (e : Fin 9) (b : Bool) :
    labelMap (canonicalPerm e b) q1Ear = {prevSite e,ringSite e,nextSite e} := by
  simp only [labelMap,q1Ear,prevSite,nextSite,nextRing,Finset.image_insert,Finset.image_singleton,
    canonicalPerm_ring,zero_add]
  congr 2 <;> congr 1 <;> abel

theorem q1_fan_transport {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedCoreData R) (i : Fin 8) :
    labelMap (canonicalPerm O.fans.ear.center (O.fans.colors O.cut))
      (q1Fan O.cut O.run_length i) = labelSet R (O.fans.faces (i+O.cut)) := by
  rw [O.fans.labels,O.order]
  simp only [labelMap,q1Fan,Finset.image_insert,Finset.image_singleton,
    canonicalPerm_ring,coreSite_shift]
  split_ifs <;> simp only [canonicalPerm_hub9,canonicalPerm_hub10]

theorem q1_second {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (O : OrderedCoreData R) : O.run_length+O.cut = O.second := by
  rw [O.length_exact]
  abel

theorem q1_central_partition {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedCoreData R) :
    (hubTriangles R).image (labelSet R) =
      {centralFace (coreSite O.fans.ear.center O.cut),
       centralFace (coreSite O.fans.ear.center O.second)} := by
  classical
  obtain ⟨a,ha⟩ := O.central_first
  obtain ⟨b,hb⟩ := O.central_second
  have hlabels : labelSet R a ≠ labelSet R b := by
    rw [ha,hb]
    exact centralFace_ne _ _ (fun he => O.endpoints_ne (coreSite_injective _ he))
  have hab : a ≠ b := fun he => hlabels (congrArg (labelSet R) he)
  have hmem (t : R.Index) (i : Fin 9) (ht : labelSet R t=centralFace i) :
      t ∈ hubTriangles R := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht.symm ▸ centralFace_mem_hubs i⟩
  have hsub : ({a,b} : Finset R.Index) ⊆ hubTriangles R := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmem _ _ ha
    · exact Finset.mem_singleton.mp ht ▸ hmem b _ hb
  have heq : ({a,b} : Finset R.Index)=hubTriangles R :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [actual_hub_triangle_count h hr R,Finset.card_pair hab])
  rw [← heq,Finset.image_insert,Finset.image_singleton,ha,hb]
  rfl

theorem q1_faces_transport {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedCoreData R) :
    actualFaces R = (q1Faces O.cut O.run_length).image
      (labelMap (canonicalPerm O.fans.ear.center (O.fans.colors O.cut))) := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hf
    have ha : a ∈ (ActualQ1FacePartition.coreFaces O.fans ∪ hubTriangles R) ∪
        {O.fans.ear.index} := by
      rw [ActualQ1FacePartition.actual_q1_all_faces h hr O.fans]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
        let i : Fin 8 := j-O.cut
        have hi : i+O.cut=j := by dsimp [i]; abel
        refine Finset.mem_image.mpr ⟨q1Fan O.cut O.run_length i,
          Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)),?_⟩
        rw [q1_fan_transport,hi]
      · have hs : labelSet R a ∈
            ({centralFace (coreSite O.fans.ear.center O.cut),
             centralFace (coreSite O.fans.ear.center O.second)} : Finset (Finset (Fin 11))) := by
          rw [← q1_central_partition h hr O]
          exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
        rcases Finset.mem_insert.mp hs with hs | hs
        · refine Finset.mem_image.mpr ⟨centralFace (coreSite 0 O.cut),
            Finset.mem_union_left _ (Finset.mem_union_right _ (by simp)),?_⟩
          simpa only [labelMap_central,coreSite_shift] using hs.symm
        · have hs := Finset.mem_singleton.mp hs
          refine Finset.mem_image.mpr ⟨centralFace (coreSite 0 (O.run_length+O.cut)),
            Finset.mem_union_left _ (Finset.mem_union_right _ (by simp)),?_⟩
          simpa only [labelMap_central,coreSite_shift,q1_second] using hs.symm
    · have he := Finset.mem_singleton.mp ha
      subst a
      refine Finset.mem_image.mpr ⟨q1Ear,Finset.mem_union_right _ (by simp),?_⟩
      rw [labelMap_ear,O.fans.ear.labels]
  · intro hf
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hf
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_union.mp hs with hs | hs
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
        exact Finset.mem_image.mpr ⟨O.fans.faces (i+O.cut),Finset.mem_univ _,
          (q1_fan_transport O i).symm⟩
      · rcases Finset.mem_insert.mp hs with rfl | hs
        · obtain ⟨a,ha⟩ := O.central_first
          refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
          rw [labelMap_central,coreSite_shift]
          exact ha
        · have he := Finset.mem_singleton.mp hs
          subst s
          obtain ⟨a,ha⟩ := O.central_second
          refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
          rw [labelMap_central,coreSite_shift,q1_second]
          exact ha
    · have he := Finset.mem_singleton.mp hs
      subst s
      exact Finset.mem_image.mpr ⟨O.fans.ear.index,Finset.mem_univ _,by
        rw [labelMap_ear,O.fans.ear.labels]⟩

theorem q1_edges_transport {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (O : OrderedCoreData R) :
    edges R = (q1Edges O.cut O.run_length).image
      (labelMap (canonicalPerm O.fans.ear.center (O.fans.colors O.cut))) := by
  rw [actual_edges_from_faces,q1_faces_transport h hr O,faceEdges_labelMap]
  rfl

theorem actual_q0_explicit_graph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0) :
    ∃ len : Fin 9, 0 < len.val ∧ ∃ k : Fin 9, ∃ b : Bool,
      actualFaces R = (q0Faces len).image (labelMap (canonicalPerm k b)) ∧
      edges R = (q0Edges len).image (labelMap (canonicalPerm k b)) := by
  obtain ⟨O⟩ := actual_q0_ordered_two_fans h hr R hq
  exact ⟨O.run_length,O.positive,O.cut,O.fans.colors O.cut,
    q0_faces_transport h hr O,q0_edges_transport h hr O⟩

theorem actual_q1_explicit_graph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1) :
    ∃ len : Fin 8, 0 < len.val ∧ ∃ k : Fin 8, ∃ e : Fin 9, ∃ b : Bool,
      actualFaces R = (q1Faces k len).image (labelMap (canonicalPerm e b)) ∧
      edges R = (q1Edges k len).image (labelMap (canonicalPerm e b)) := by
  obtain ⟨O⟩ := actual_q1_ordered_core_fans h hr R hq
  exact ⟨O.run_length,O.positive,O.cut,O.fans.ear.center,O.fans.colors O.cut,
    q1_faces_transport h hr O,q1_edges_transport h hr O⟩

theorem actual_q0_degree_three_run {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0)
    (hd : (neighbors R 9).card=3 ∨ (neighbors R 10).card=3) :
    ∃ O : OrderedData R, O.run_length=(1 : Fin 9) := by
  obtain ⟨O⟩ := actual_q0_ordered_two_fans h hr R hq
  have hs := ActualQ0RunDegrees.actual_q0_run_degrees h hr O
  have hp := O.positive
  have hm := O.run_length.isLt
  have hlen : O.run_length.val=1 ∨ O.run_length.val=8 := by
    cases hc : O.fans.colors O.cut <;>
      simp only [hc,hubSite,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] at hs
    all_goals rcases hd with hd | hd <;> omega
  rcases hlen with hlen | hlen
  · exact ⟨O,Fin.ext hlen⟩
  · refine ⟨ActualQ0FourRunNormalization.OrderedData.swap O,Fin.ext ?_⟩
    have hg := ActualQ0FourRunNormalization.reverse_gap_sum O.cut O.second O.endpoints_ne
    rw [← O.length_exact] at hg
    change (O.cut-O.second).val=1
    omega

theorem actual_q1_degree_three_run {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1)
    (hd : (neighbors R 9).card=3 ∨ (neighbors R 10).card=3) :
    ∃ O : OrderedCoreData R, O.run_length=(1 : Fin 8) := by
  obtain ⟨O⟩ := actual_q1_ordered_core_fans h hr R hq
  have hs := ActualQ1RunDegrees.actual_q1_run_degrees h hr O
  have hp := O.positive
  have hm := O.run_length.isLt
  have hlen : O.run_length.val=1 ∨ O.run_length.val=7 := by
    cases hc : O.fans.colors O.cut <;>
      simp only [hc,hubSite,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] at hs
    all_goals rcases hd with hd | hd <;> omega
  rcases hlen with hlen | hlen
  · exact ⟨O,Fin.ext hlen⟩
  · refine ⟨ActualQ1RunDegrees.OrderedCoreData.swap O,Fin.ext ?_⟩
    have hg := ActualQ1RunDegrees.reverse_core_gap_sum O.cut O.second O.endpoints_ne
    rw [← O.length_exact] at hg
    change (O.cut-O.second).val=1
    omega

theorem actual_q0_degree_three_graph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0)
    (hd : (neighbors R 9).card=3 ∨ (neighbors R 10).card=3) :
    ∃ k : Fin 9, ∃ b : Bool,
      actualFaces R = (q0Faces 1).image (labelMap (canonicalPerm k b)) ∧
      edges R = (q0Edges 1).image (labelMap (canonicalPerm k b)) := by
  obtain ⟨O,hO⟩ := actual_q0_degree_three_run h hr R hq hd
  refine ⟨O.cut,O.fans.colors O.cut,?_,?_⟩
  · simpa only [hO] using q0_faces_transport h hr O
  · simpa only [hO] using q0_edges_transport h hr O

theorem actual_q1_degree_three_graph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1)
    (hd : (neighbors R 9).card=3 ∨ (neighbors R 10).card=3) :
    ∃ k : Fin 8, ∃ e : Fin 9, ∃ b : Bool,
      actualFaces R = (q1Faces k 1).image (labelMap (canonicalPerm e b)) ∧
      edges R = (q1Edges k 1).image (labelMap (canonicalPerm e b)) := by
  obtain ⟨O,hO⟩ := actual_q1_degree_three_run h hr R hq hd
  refine ⟨O.cut,O.fans.ear.center,O.fans.colors O.cut,?_,?_⟩
  · simpa only [hO] using q1_faces_transport h hr O
  · simpa only [hO] using q1_edges_transport h hr O

/-! The degree-three checker uses ear label 1 in q1 and the ordered core
0,2,3,4,5,6,7,8. Its eight short hub edges are 0→2,2→3,...,8→0.
The following finite identities match that exact graph convention. -/
def degreeThreeTableEdges (q : Bool) (u v : Fin 11) : Finset (Finset (Fin 11)) :=
  ((boundaryEdges ∪ (if q then {{0,2}} else ∅)) ∪ {{9,u},{9,v},{9,10}}) ∪
    ((Finset.univ.filter (fun i : Fin 9 => q=false ∨ i≠1)).image
      (fun i => ({10,ringSite i} : Finset (Fin 11))))

def q1TableEndpoint (k : Fin 8) : Fin 11 := ringSite (coreSite 0 k+1)

def q1DegreeThreeTableEdges (k : Fin 8) : Finset (Finset (Fin 11)) :=
  degreeThreeTableEdges true (q1TableEndpoint k) (q1TableEndpoint (coreNext k))

theorem q0_degree_three_table_identity :
    q0Edges 1=degreeThreeTableEdges false 0 1 := by decide +kernel

theorem q1_degree_three_table_identity : ∀ k : Fin 8,
    (q1Edges k 1).image (labelMap (canonicalPerm 1 true)) =
      q1DegreeThreeTableEdges k := by decide +kernel

theorem table_rotation_composition : ∀ e : Fin 9, ∀ b : Bool, ∀ i : Fin 11,
    canonicalPerm (e-1) b (canonicalPerm 1 true i) = canonicalPerm e b i := by
  decide +kernel

theorem table_rotation_back (e : Fin 9) (b : Bool) (s : Finset (Fin 11)) :
    labelMap (canonicalPerm (e-1) b) (labelMap (canonicalPerm 1 true) s) =
      labelMap (canonicalPerm e b) s := by
  simp only [labelMap,Finset.image_image]
  congr 1
  funext i
  exact table_rotation_composition e b i

theorem actual_q0_degree_three_table_graph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0)
    (hd : (neighbors R 9).card=3 ∨ (neighbors R 10).card=3) :
    ∃ k : Fin 9, ∃ b : Bool,
      edges R = (degreeThreeTableEdges false 0 1).image (labelMap (canonicalPerm k b)) := by
  obtain ⟨k,b,_,he⟩ := actual_q0_degree_three_graph h hr R hq hd
  exact ⟨k,b,by rw [← q0_degree_three_table_identity]; exact he⟩

theorem actual_q1_degree_three_table_graph {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1)
    (hd : (neighbors R 9).card=3 ∨ (neighbors R 10).card=3) :
    ∃ k : Fin 8, ∃ e : Fin 9, ∃ b : Bool,
      edges R = (q1DegreeThreeTableEdges k).image (labelMap (canonicalPerm e b)) := by
  obtain ⟨k,e,b,_,he⟩ := actual_q1_degree_three_graph h hr R hq hd
  refine ⟨k,e-1,b,?_⟩
  rw [← q1_degree_three_table_identity,Finset.image_image]
  simpa only [Function.comp_def,table_rotation_back] using he

end N11Formalization.ActualOrderedMetricGraphs
#check @N11Formalization.ActualOrderedMetricGraphs.q0_edges_transport
#check @N11Formalization.ActualOrderedMetricGraphs.q1_edges_transport
#check @N11Formalization.ActualOrderedMetricGraphs.actual_q0_explicit_graph
#check @N11Formalization.ActualOrderedMetricGraphs.actual_q1_explicit_graph
#check @N11Formalization.ActualOrderedMetricGraphs.actual_q0_degree_three_graph
#check @N11Formalization.ActualOrderedMetricGraphs.actual_q1_degree_three_graph
#check @N11Formalization.ActualOrderedMetricGraphs.actual_q0_degree_three_table_graph
#check @N11Formalization.ActualOrderedMetricGraphs.actual_q1_degree_three_table_graph
#print axioms N11Formalization.ActualOrderedMetricGraphs.q0_edges_transport
#print axioms N11Formalization.ActualOrderedMetricGraphs.q1_edges_transport
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q0_explicit_graph
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q1_explicit_graph
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q0_degree_three_graph
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q1_degree_three_graph
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q0_degree_three_table_graph
#print axioms N11Formalization.ActualOrderedMetricGraphs.actual_q1_degree_three_table_graph
