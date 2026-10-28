import N11Formalization.ActualRefinementEulerCount
import N11Formalization.ActualSiteAngleChain

/-! Weighted finite incidence identities for all actual selected edges.
Flags are actual face/opposite-slot pairs, not a canonical face table.
The same reindexing pays both area aggregation and site angle rows. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualEdgeFlagSums

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementDoubleCounting
open ActualRefinementEulerCount ActualSelectedRingEdges ActualHubTriangleCensus
open ActualMetricAngleAtoms ActualSiteAngleChain ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualBoundaryCyclicOrder

local instance indexDecidableEq {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    DecidableEq R.Index := Classical.decEq _

def flagEdge {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (A : R.Index) (s : Fin 3) : Finset (Fin 11) :=
  (labelSet R A).erase (R.labels A s)

def edgeFlags {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (e : Finset (Fin 11)) : Finset (R.Index × Fin 3) := by
  classical
  exact Finset.univ.filter (fun p => flagEdge R p.1 p.2 = e)

def edgeSum {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (w : R.Index → Fin 3 → ℝ) (e : Finset (Fin 11)) : ℝ :=
  ∑ p ∈ edgeFlags R e, w p.1 p.2

theorem flag_edge_card {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : (flagEdge R A s).card = 2 := by
  have hm : R.labels A s ∈ labelSet R A := mem_labelSet.mpr ⟨s, rfl⟩
  have h := Finset.card_erase_add_one hm
  rw [labelSet_card] at h
  unfold flagEdge
  omega

theorem flag_edge_mem {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : flagEdge R A s ∈ edges R := by
  classical
  exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_univ _,
    Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, flag_edge_card R A s⟩⟩

theorem flag_edge_injective {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) : Function.Injective (flagEdge R A) := by
  intro s t he
  apply Refinement.labels_injective R A
  exact (Finset.erase_inj (labelSet R A) (mem_labelSet.mpr ⟨s, rfl⟩)).mp he

theorem flag_edge_eq_pair {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    flagEdge R A s = {R.labels A (s + 1), R.labels A (s + 2)} := by
  have hi := Refinement.labels_injective R A
  have h01 := hi.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := hi.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := hi.ne (by decide : (1 : Fin 3) ≠ 2)
  fin_cases s
  · change (labelSet R A).erase (R.labels A 0) = {R.labels A 1, R.labels A 2}
    simp [labelSet, h01, h02]
  · change (labelSet R A).erase (R.labels A 1) = {R.labels A 2, R.labels A 0}
    ext z
    simp only [labelSet, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    grind
  · change (labelSet R A).erase (R.labels A 2) = {R.labels A 0, R.labels A 1}
    ext z
    simp only [labelSet, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    grind

theorem exists_flag_of_subset {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {e : Finset (Fin 11)}
    (hsub : e ⊆ labelSet R A) (he : e.card = 2) :
    ∃ s : Fin 3, flagEdge R A s = e := by
  classical
  have hc : ((labelSet R A) \ e).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, labelSet_card, he]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have hm : p ∈ labelSet R A \ e := by rw [hp]; simp
  obtain ⟨s, hs⟩ := mem_labelSet.mp (Finset.mem_sdiff.mp hm).1
  refine ⟨s, ?_⟩
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_erase.mpr ⟨by
      intro heq
      subst x
      exact (Finset.mem_sdiff.mp hm).2 (hs ▸ hx), hsub hx⟩
  · rw [flag_edge_card, he]

theorem edge_flags_card {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {e : Finset (Fin 11)} (he : e.card = 2) :
    (edgeFlags R e).card = (edgeTriangles R e).card := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    have hh := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [← hh]
      exact Finset.erase_subset _ _⟩
  · intro p hp q hq heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext heq
    apply flag_edge_injective R p.1
    rw [hp', heq, hq']
  · intro A hA
    obtain ⟨s, hs⟩ := exists_flag_of_subset R (Finset.mem_filter.mp hA).2 he
    exact ⟨(A, s), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩

theorem sum_edge_sum {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (w : R.Index → Fin 3 → ℝ) :
    (∑ e ∈ edges R, edgeSum R w e) = ∑ A : R.Index, ∑ s : Fin 3, w A s := by
  classical
  have hh := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := edges R)
    (g := fun p : R.Index × Fin 3 => flagEdge R p.1 p.2)
    (fun p _ => flag_edge_mem R p.1 p.2) (fun p => w p.1 p.2)
  simpa only [edgeSum, edgeFlags, Fintype.sum_prod_type] using hh

theorem masked_edge_sum {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (w : R.Index → Fin 3 → ℝ) (i : Fin 11)
    (e : Finset (Fin 11)) :
    edgeSum R (fun A s => if i ∈ flagEdge R A s then w A s else 0) e =
      if i ∈ e then edgeSum R w e else 0 := by
  classical
  unfold edgeSum
  calc
    _ = ∑ p ∈ edgeFlags R e, if i ∈ e then w p.1 p.2 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      change (if i ∈ flagEdge R p.1 p.2 then w p.1 p.2 else 0) = _
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := by rw [Finset.sum_ite_irrel]; simp

theorem sum_incident_edge_sum {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (w : R.Index → Fin 3 → ℝ) (i : Fin 11) :
    (∑ e ∈ incidentEdges R i, edgeSum R w e) =
      ∑ A : R.Index, ∑ s : Fin 3, if i ∈ flagEdge R A s then w A s else 0 := by
  classical
  rw [← sum_edge_sum R (fun A s => if i ∈ flagEdge R A s then w A s else 0)]
  simp_rw [masked_edge_sum]
  exact Finset.sum_filter _ _

theorem face_site_flag_row {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (w : R.Index → Fin 3 → ℝ) (A : R.Index) (i : Fin 11) :
    (∑ s : Fin 3, if i ∈ flagEdge R A s then w A s else 0) =
      (if i ∈ labelSet R A then ∑ s : Fin 3, w A s else 0) -
        ∑ s : Fin 3, if R.labels A s = i then w A s else 0 := by
  classical
  have he (s : Fin 3) :
      (if i ∈ flagEdge R A s then w A s else 0) =
        (if i ∈ labelSet R A then w A s else 0) -
          (if R.labels A s = i then w A s else 0) := by
    by_cases hsi : R.labels A s = i
    · have hm : i ∈ labelSet R A := mem_labelSet.mpr ⟨s, hsi⟩
      simp [flagEdge, hm, hsi]
    · by_cases hm : i ∈ labelSet R A <;> simp [flagEdge, hm, hsi, Ne.symm hsi]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]

theorem face_site_label_count {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (i : Fin 11) :
    (∑ s : Fin 3, if R.labels A s = i then (1 : ℝ) else 0) =
      if i ∈ labelSet R A then 1 else 0 := by
  classical
  by_cases hi : i ∈ labelSet R A
  · obtain ⟨u, hu⟩ := mem_labelSet.mp hi
    have he (s : Fin 3) : R.labels A s = i ↔ s = u := by
      rw [← hu]
      exact (Refinement.labels_injective R A).eq_iff
    simp [he, hi]
  · have he (s : Fin 3) : R.labels A s ≠ i :=
      fun hs => hi (mem_labelSet.mpr ⟨s, hs⟩)
    simp [he, hi]

theorem sum_incident_face_angles {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (R : Refinement c r) (i : Fin 11) :
    (∑ e ∈ incidentEdges R i, edgeSum R (faceAngle R) e) =
      (siteTriangles R i).card * Real.pi - siteFaceSum R i := by
  classical
  rw [sum_incident_edge_sum]
  simp_rw [face_site_flag_row, actual_face_angle_sum h R]
  rw [Finset.sum_sub_distrib]
  have hcount : (∑ A : R.Index, if i ∈ labelSet R A then Real.pi else 0) =
      (siteTriangles R i).card * Real.pi := by
    rw [← Finset.sum_filter]
    simp only [siteTriangles, Finset.sum_const, nsmul_eq_mul]
  rw [hcount]
  rfl

def cycleEdge (k : Fin 9) : Finset (Fin 11) := {ringSite k, nextSite k}

theorem cycle_edge_injective : Function.Injective cycleEdge := by decide +kernel
theorem cycle_edge_card : ∀ k : Fin 9, (cycleEdge k).card = 2 := by decide +kernel
theorem cycle_edge_image : Finset.univ.image cycleEdge = boundaryEdges := rfl
theorem cycle_edge_owner_mem : ∀ i k : Fin 9,
    nextSite i ∈ cycleEdge k ↔ k = i ∨ k = nextRing i := by decide +kernel
theorem cycle_edge_hub_not_mem : ∀ (i : Fin 11), 9 ≤ i.val →
    ∀ k : Fin 9, i ∉ cycleEdge k := by decide +kernel
theorem boundary_incident_card : ∀ i : Fin 11,
    (boundaryEdges.filter (fun e => i ∈ e)).card = if i.val < 9 then 2 else 0 := by
  decide +kernel

def switchSum (f : Fin 9 → ℝ) (e : Finset (Fin 11)) : ℝ :=
  ∑ k : Fin 9, if cycleEdge k = e then f k else 0

theorem switch_sum_cycle (f : Fin 9 → ℝ) (i : Fin 9) :
    switchSum f (cycleEdge i) = f i := by
  classical
  simp [switchSum, cycle_edge_injective.eq_iff]

theorem switch_sum_nonboundary (f : Fin 9 → ℝ) {e : Finset (Fin 11)}
    (he : e ∉ boundaryEdges) : switchSum f e = 0 := by
  have hn (k : Fin 9) : cycleEdge k ≠ e := by
    intro hk
    apply he
    rw [← hk, ← cycle_edge_image]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  simp [switchSum, hn]

theorem sum_switch_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (f : Fin 9 → ℝ) : (∑ e ∈ edges R, switchSum f e) = ∑ k : Fin 9, f k := by
  classical
  unfold switchSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hm : cycleEdge k ∈ edges R := boundary_edges_subset h hr R
    (by rw [← cycle_edge_image]; exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  simp [hm, eq_comm]

theorem sum_incident_switch_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (f : Fin 9 → ℝ) (i : Fin 11) :
    (∑ e ∈ incidentEdges R i, switchSum f e) =
      ∑ k : Fin 9, if i ∈ cycleEdge k then f k else 0 := by
  classical
  unfold switchSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hm : cycleEdge k ∈ edges R := boundary_edges_subset h hr R
    (by rw [← cycle_edge_image]; exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  by_cases hi : i ∈ cycleEdge k <;> simp [incidentEdges, hm, hi, eq_comm]

theorem ring_switch_row (f : Fin 9 → ℝ) (i : Fin 9) :
    (∑ k : Fin 9, if nextSite i ∈ cycleEdge k then f k else 0) = f i + f (nextRing i) := by
  classical
  have hne : i ≠ nextRing i := ActualBoundaryCyclicOrder.next_ne i
  have he (k : Fin 9) :
      (if nextSite i ∈ cycleEdge k then f k else 0) =
        (if k = i then f k else 0) + (if k = nextRing i then f k else 0) := by
    simp only [cycle_edge_owner_mem]
    by_cases hk : k = i
    · subst k
      simp [hne]
    · by_cases hl : k = nextRing i <;> simp [hk, hl, hne.symm]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

theorem flag_mem_edge_triangles {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {s : Fin 3} {e : Finset (Fin 11)}
    (hs : flagEdge R A s = e) : A ∈ edgeTriangles R e := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [← hs]
    exact Finset.erase_subset _ _⟩

theorem edge_flags_eq_singleton {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {e : Finset (Fin 11)} {A : R.Index} {s : Fin 3}
    (hT : edgeTriangles R e = {A}) (hs : flagEdge R A s = e) :
    edgeFlags R e = {(A, s)} := by
  classical
  ext p
  simp only [edgeFlags, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hp
    have hA : p.1 = A := by
      have hh := flag_mem_edge_triangles R hp
      rwa [hT, Finset.mem_singleton] at hh
    apply Prod.ext hA
    apply flag_edge_injective R A
    simpa only [hA, hs] using hp
  · rintro rfl
    exact hs

theorem edge_flags_eq_pair {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {e : Finset (Fin 11)} {A B : R.Index} {s t : Fin 3}
    (hT : edgeTriangles R e = {A, B})
    (hs : flagEdge R A s = e) (ht : flagEdge R B t = e) :
    edgeFlags R e = {(A, s), (B, t)} := by
  classical
  ext p
  simp only [edgeFlags, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hp
    have hAB : p.1 = A ∨ p.1 = B := by
      have hh := flag_mem_edge_triangles R hp
      simpa only [hT, Finset.mem_insert, Finset.mem_singleton] using hh
    rcases hAB with hA | hB
    · left
      apply Prod.ext hA
      apply flag_edge_injective R A
      simpa only [hA, hs] using hp
    · right
      apply Prod.ext hB
      apply flag_edge_injective R B
      simpa only [hB, ht] using hp
  · rintro (rfl | rfl)
    · exact hs
    · exact ht

theorem face_site_flag_count {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (i : Fin 11) :
    (∑ s : Fin 3, if i ∈ flagEdge R A s then (1 : ℝ) else 0) =
      if i ∈ labelSet R A then 2 else 0 := by
  rw [face_site_flag_row R (fun _ _ => (1 : ℝ)) A i, face_site_label_count]
  by_cases hi : i ∈ labelSet R A <;> norm_num [hi]

/-- The degree offset is derived by counting actual flags at the site.
Ring sites have one more edge than face; hub sites have equal counts. -/
theorem actual_site_degree_offset {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (i : Fin 11) :
    ((incidentEdges R i).card : ℝ) - (siteTriangles R i).card =
      if i.val < 9 then 1 else 0 := by
  classical
  have hc := sum_incident_edge_sum R (fun _ _ => (1 : ℝ)) i
  have hflags (e : Finset (Fin 11)) : edgeSum R (fun _ _ => (1 : ℝ)) e =
      ((edgeFlags R e).card : ℝ) := by simp [edgeSum]
  simp only [hflags, face_site_flag_count] at hc
  have hright : (∑ A : R.Index, if i ∈ labelSet R A then (2 : ℝ) else 0) =
      2 * (siteTriangles R i).card := by
    rw [← Finset.sum_filter]
    simp [siteTriangles, mul_comm]
  rw [hright] at hc
  have hB := boundary_edges_subset h hr R
  have hfilter : (incidentEdges R i).filter (fun e => e ∈ boundaryEdges) =
      boundaryEdges.filter (fun e => i ∈ e) := by
    ext e
    simp only [incidentEdges, Finset.mem_filter]
    exact ⟨fun he => ⟨he.2, he.1.2⟩, fun he => ⟨⟨hB he.1, he.2⟩, he.1⟩⟩
  have hboole : (∑ e ∈ incidentEdges R i, if e ∈ boundaryEdges then (1 : ℝ) else 0) =
      ((boundaryEdges.filter (fun e => i ∈ e)).card : ℝ) := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hcard (e : Finset (Fin 11)) (he : e ∈ incidentEdges R i) :
      ((edgeFlags R e).card : ℝ) =
        2 - (if e ∈ boundaryEdges then 1 else 0) := by
    have heE := (Finset.mem_filter.mp he).1
    rw [edge_flags_card R (selected_edge_card_two R heE),
      actual_edge_triangle_card h hr R heE]
    by_cases hb : e ∈ boundaryEdges <;> norm_num [hb]
  rw [Finset.sum_congr rfl hcard, Finset.sum_sub_distrib, hboole,
    boundary_incident_card] at hc
  simp only [Finset.sum_const, nsmul_eq_mul] at hc
  by_cases hi : i.val < 9 <;> simp only [hi, if_true, if_false, Nat.cast_ofNat, Nat.cast_zero] at *
  all_goals linarith

end N11Formalization.ActualEdgeFlagSums

#check @N11Formalization.ActualEdgeFlagSums.sum_edge_sum
#check @N11Formalization.ActualEdgeFlagSums.sum_incident_face_angles
#print axioms N11Formalization.ActualEdgeFlagSums.sum_edge_sum
#print axioms N11Formalization.ActualEdgeFlagSums.sum_incident_face_angles
#print axioms N11Formalization.ActualEdgeFlagSums.actual_site_degree_offset
