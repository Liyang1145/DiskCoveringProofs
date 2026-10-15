import N11Formalization.ActualQ1CoreTransitions
import N11Formalization.ActualFiniteBinaryCycleRuns

/-! Productive actual q1 ordered two-fan structure on the ear-deleted
eight-cycle, with actual unknown central endpoints and original nearest
witnesses. No closed metric exclusion is asserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ1OrderedCoreFans
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualRefinementEarCount
open ActualRefinementTriangleUniqueness ActualHubTriangleCensus ActualHubPathCounts
open ActualHubRingPaths ActualQ1CoreFans ActualQ1CoreCycle ActualQ1CoreTransitions
open ActualRingDirectionOrder ActualSelectedEarRemoval ActualQ0BoundaryFans

theorem common_ring_not_ear_middle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (E : EarData R) {k : Fin 11} (hk : k ∈ ringNeighbors R 9 ∩ ringNeighbors R 10) :
    k ≠ ringSite E.center := by
  intro he
  have h9 := ((mem_ringNeighbors R).mp (Finset.mem_inter.mp hk).1).1
  rw [he] at h9
  have hn := ActualHubNeighborCoverage.neighbor_symm h9
  exact (actual_ear_center_no_hub h hr R E.labels).1 hn

theorem CoreFans.exactly_two_core_transitions {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : CoreFans R) (P : RingPath R 9 10) :
    ∃ a b : Fin 8, a≠b ∧ ringSite (coreSite F.ear.center a)=P.first ∧
      ringSite (coreSite F.ear.center b)=P.last ∧
      ∀ i : Fin 8, F.colors (i-1) ≠ F.colors i ↔ i=a ∨ i=b := by
  obtain ⟨A,hA9,hA10,hAf⟩ := P.first_central
  obtain ⟨B,hB9,hB10,hBl⟩ := P.last_central
  have hfirst := P.ring_vertices _ P.walk.start_mem_support
  have hlast := P.ring_vertices _ P.walk.end_mem_support
  have hfcommon := central_ring_in_both_paths R hfirst hA9 hA10 hAf
  have hlcommon := central_ring_in_both_paths R hlast hB9 hB10 hBl
  let K : Fin 9 := ⟨P.first.val,hfirst⟩
  let L : Fin 9 := ⟨P.last.val,hlast⟩
  have hK : ringSite K=P.first := Fin.ext rfl
  have hL : ringSite L=P.last := Fin.ext rfl
  have hKe : K ≠ F.ear.center := by
    intro he
    apply common_ring_not_ear_middle h hr F.ear hfcommon
    rw [← hK,he]
  have hLe : L ≠ F.ear.center := by
    intro he
    apply common_ring_not_ear_middle h hr F.ear hlcommon
    rw [← hL,he]
  obtain ⟨a,ha⟩ := (core_sites_without_middle F.ear.center K).mpr hKe
  obtain ⟨b,hb⟩ := (core_sites_without_middle F.ear.center L).mpr hLe
  have haf : ringSite (coreSite F.ear.center a)=P.first := by rw [ha,hK]
  have hbl : ringSite (coreSite F.ear.center b)=P.last := by rw [hb,hL]
  have hab : a≠b := fun he => P.endpoints_ne (by rw [← haf,← hbl,he])
  have hinj : Function.Injective (fun i : Fin 8 => ringSite (coreSite F.ear.center i)) := by
    intro i j he
    apply coreSite_injective F.ear.center
    exact Fin.ext (congrArg (fun k : Fin 11 => k.val) he)
  refine ⟨a,b,hab,haf,hbl,?_⟩
  intro i
  rw [ActualQ1CoreTransitions.CoreFans.transition_iff_common_ring h hr F i,
    actual_common_neighbors_are_endpoints h hr R P,← haf,← hbl]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  exact ⟨fun hh => hh.imp (fun he => hinj he) (fun he => hinj he),
    fun hh => hh.imp (congrArg (fun i => ringSite (coreSite F.ear.center i)))
      (congrArg (fun i => ringSite (coreSite F.ear.center i)))⟩

structure OrderedCoreData {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) where
  fans : CoreFans R
  cut : Fin 8
  second : Fin 8
  endpoints_ne : cut ≠ second
  run_length : Fin 8
  positive : 0 < run_length.val
  length_exact : run_length=second-cut
  changes : ∀ i : Fin 8, fans.colors (i-1) ≠ fans.colors i ↔ i=cut ∨ i=second
  order : ∀ i : Fin 8, fans.colors (i+cut) =
    if i.val < run_length.val then fans.colors cut else !fans.colors cut
  central_first : ∃ A : R.Index,
    labelSet R A = {9,10,ringSite (coreSite fans.ear.center cut)}
  central_second : ∃ B : R.Index,
    labelSet R B = {9,10,ringSite (coreSite fans.ear.center second)}

theorem actual_q1_ordered_core_fans {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1) : Nonempty (OrderedCoreData R) := by
  obtain ⟨F⟩ := actual_q1_core_fans h hr R hq
  obtain ⟨P⟩ := (actual_two_ring_paths h hr R).1
  obtain ⟨a,b,hab,ha,hb,hchange⟩ := CoreFans.exactly_two_core_transitions h hr F P
  have H := ActualFiniteBinaryCycleRuns.two_changes_runs hab hchange
  obtain ⟨A,hA9,hA10,hAf⟩ := P.first_central
  obtain ⟨B,hB9,hB10,hBl⟩ := P.last_central
  have hA := ActualCentralRingEndpoints.three_labels_full R
    (P.ring_vertices _ P.walk.start_mem_support) hA9 hA10 hAf
  have hB := ActualCentralRingEndpoints.three_labels_full R
    (P.ring_vertices _ P.walk.end_mem_support) hB9 hB10 hBl
  exact ⟨⟨F,a,b,hab,b-a,Nat.pos_of_ne_zero H.1,rfl,hchange,H.2.2,
    ⟨A,by rwa [← ha] at hA⟩,⟨B,by rwa [← hb] at hB⟩⟩⟩

theorem OrderedCoreData.true_shifted_rows {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (O : OrderedCoreData R) :
    ∀ i : Fin 8, ‖R.witness (O.fans.faces (i+O.cut))‖ < 1 ∧
      ∀ j ∈ ({ringSite (coreSite O.fans.ear.center (i+O.cut)),
        ringSite (coreSite O.fans.ear.center (coreNext (i+O.cut))),
        if i.val < O.run_length.val then hubSite (O.fans.colors O.cut)
          else hubSite (!O.fans.colors O.cut)} : Finset (Fin 11)),
        R.witness (O.fans.faces (i+O.cut)) ∈ ActualVoronoiCells.Cell c j ∧
          dist (R.witness (O.fans.faces (i+O.cut))) (c j) ≤ r := by
  intro i
  have hlabels := O.fans.labels (i+O.cut)
  rw [O.order] at hlabels
  have hh : hubSite (if i.val < O.run_length.val then O.fans.colors O.cut
      else !O.fans.colors O.cut) =
      if i.val < O.run_length.val then hubSite (O.fans.colors O.cut)
        else hubSite (!O.fans.colors O.cut) := by split_ifs <;> rfl
  rw [hh] at hlabels
  refine ⟨(Refinement.real_triangle R _).1,?_⟩
  intro j hj
  rw [← hlabels] at hj
  obtain ⟨v,hv⟩ := mem_labelSet.mp hj
  rw [← hv]
  exact (Refinement.real_triangle R _).2.1 v

end N11Formalization.ActualQ1OrderedCoreFans
#check @N11Formalization.ActualQ1OrderedCoreFans.actual_q1_ordered_core_fans
#check @N11Formalization.ActualQ1OrderedCoreFans.OrderedCoreData.true_shifted_rows
#print axioms N11Formalization.ActualQ1OrderedCoreFans.actual_q1_ordered_core_fans
