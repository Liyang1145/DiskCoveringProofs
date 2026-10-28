import N11Formalization.ActualEdgeFlagSums
import N11Formalization.ActualBoundaryEdgeAreaAtoms
import N11Formalization.ActualSectorAreaEnvelope
import N11Formalization.ActualRingAngleClosure

/-! The real twenty-one-edge sine model produced from the actual refinement.
Every edge angle and area is defined by its true face flags and switch
fiber. Domains, station balances and both budgets are conclusions. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualEdgeMetricModel

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementDoubleCounting
open ActualRefinementEulerCount ActualEdgeFlagSums ActualSquaredSideMatching
open ActualMetricAngleAtoms ActualSharedFactorArea ActualEdgeAreaAtoms
open ActualBoundaryEdgeAreaAtoms ActualSectorAreaEnvelope ActualSiteAngleChain
open ActualHubOneTurn ActualRingAngleClosure ActualBoundaryNineTies
open ActualSwitchAtomAggregate ActualBoundarySwitchMetric ActualBoundarySwitchAngles
open ActualRingDirectionOrder ActualRingLinkBoundaryData
open ActualBoundaryCyclicOrder

local instance indexDecidableEq {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    DecidableEq R.Index := Classical.decEq _

def edgeAngle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (e : Finset (Fin 11)) : ℝ :=
  Real.pi - edgeSum R (faceAngle R) e -
    switchSum (fun k => SwitchData.angle (switchData h hr v k)) e

def pairedArea {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (e : Finset (Fin 11)) : ℝ :=
  edgeSum R (fun A s => faceSideSquared R A s * cotangent (faceAngle R A s)) e +
    switchSum (switchArea h hr v) e

theorem flag_edge_of_side_at {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {s : Fin 3} {i j : Fin 11}
    (hs : SideAt R A s i j) : flagEdge R A s = {i, j} := by
  rw [flag_edge_eq_pair]
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Finset.pair_comm]

/-- Both closed angular domains and the sine bound are produced for
every actual edge, including artificial flat diagonals. -/
theorem actual_edge_angle_area_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) {e : Finset (Fin 11)} (he : e ∈ edges R) :
    0 ≤ edgeAngle h hr R v e ∧ edgeAngle h hr R v e ≤ Real.pi ∧
      0 ≤ pairedArea h hr R v e ∧
      pairedArea h hr R v e ≤ (19 / 50 : ℝ) ^ 2 * Real.sin (edgeAngle h hr R v e) := by
  classical
  have hc := actual_edge_triangle_card h hr R he
  by_cases hb : e ∈ boundaryEdges
  · have hbimage : e ∈ Finset.univ.image cycleEdge := by rw [cycle_edge_image]; exact hb
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hbimage
    subst e
    obtain ⟨A, s, hs, _, hθ0, hθπ, _, _, ha0, hab⟩ :=
      actual_boundary_edge_area_producer h hr R v k
    have hf : flagEdge R A s = cycleEdge k := flag_edge_of_side_at R hs
    have hAm := flag_mem_edge_triangles R hf
    rw [if_pos hb] at hc
    obtain ⟨D, hD⟩ := Finset.card_eq_one.mp hc
    have hAD : A = D := by rwa [hD, Finset.mem_singleton] at hAm
    have hT : edgeTriangles R (cycleEdge k) = {A} := by simpa only [hAD] using hD
    have hflags := edge_flags_eq_singleton R hT hf
    have hsum (w : R.Index → Fin 3 → ℝ) :
        edgeSum R w (cycleEdge k) = w A s := by simp [edgeSum, hflags]
    have hangle : edgeAngle h hr R v (cycleEdge k) = boundaryEdgeAngle h hr R v k A s := by
      unfold edgeAngle boundaryEdgeAngle
      rw [hsum, switch_sum_cycle]
      ring
    have harea : pairedArea h hr R v (cycleEdge k) = boundaryEdgeAreaAtom h hr R v k A s := by
      unfold pairedArea
      rw [hsum, switch_sum_cycle, actual_switch_area_eq_half_side_cotangent]
      rfl
    rw [hangle, harea]
    exact ⟨hθ0, hθπ, ha0, hab⟩
  · rw [if_neg hb] at hc
    obtain ⟨A, B, hAB, hT⟩ := Finset.card_eq_two.mp hc
    have hecard := ActualSelectedRingEdges.selected_edge_card_two R he
    obtain ⟨i, j, hij, heq⟩ := Finset.card_eq_two.mp hecard
    have hAm : A ∈ edgeTriangles R e := by rw [hT]; simp
    have hBm : B ∈ edgeTriangles R e := by rw [hT]; simp
    have hAs := (Finset.mem_filter.mp hAm).2
    have hBs := (Finset.mem_filter.mp hBm).2
    have hAi := hAs (by rw [heq]; simp : i ∈ e)
    have hAj := hAs (by rw [heq]; simp : j ∈ e)
    have hBi := hBs (by rw [heq]; simp : i ∈ e)
    have hBj := hBs (by rw [heq]; simp : j ∈ e)
    obtain ⟨s, t, hs, ht, _, hθ0, hθπ, _, ha0, hab⟩ :=
      actual_shared_edge_area_producer h hr R hAB hij hAi hAj hBi hBj
    have hfA : flagEdge R A s = e := (flag_edge_of_side_at R hs).trans heq.symm
    have hfB : flagEdge R B t = e := (flag_edge_of_side_at R ht).trans heq.symm
    have hflags := edge_flags_eq_pair R hT hfA hfB
    have hne : (A, s) ≠ (B, t) := fun hp => hAB (congrArg Prod.fst hp)
    have hsum (w : R.Index → Fin 3 → ℝ) : edgeSum R w e = w A s + w B t := by
      simp [edgeSum, hflags, hne]
    have hangle : edgeAngle h hr R v e = sharedEdgeAngle R A B s t := by
      unfold edgeAngle sharedEdgeAngle
      rw [hsum, switch_sum_nonboundary _ hb]
      ring
    have harea : pairedArea h hr R v e = sharedEdgeAreaAtom R A B s t := by
      unfold pairedArea sharedEdgeAreaAtom
      rw [hsum, switch_sum_nonboundary _ hb, add_zero]
    rw [hangle, harea]
    exact ⟨hθ0, hθπ.le, ha0, hab⟩

/-- The twenty-one paired atoms contain each true face flag and each
of the nine switch triangles exactly once. -/
theorem actual_paired_area_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) :
    (∑ e ∈ edges R, pairedArea h hr R v e) =
      (∑ A : R.Index, faceArea R A) + ∑ k : Fin 9, switchArea h hr v k := by
  classical
  unfold pairedArea
  rw [Finset.sum_add_distrib, sum_edge_sum, sum_switch_sum h hr R]
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  exact (actual_face_area_eq_half_side_cotangent_sum h R A).symm

theorem actual_site_edge_angle_row {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 11) :
    (∑ e ∈ incidentEdges R i, edgeAngle h hr R v e) =
      siteFaceSum R i + (if i.val < 9 then Real.pi else 0) -
        ∑ k : Fin 9, if i ∈ cycleEdge k then
          SwitchData.angle (switchData h hr v k) else 0 := by
  classical
  unfold edgeAngle
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_incident_face_angles h R,
    sum_incident_switch_sum h hr R, Finset.sum_const, nsmul_eq_mul]
  calc
    _ = (((incidentEdges R i).card : ℝ) - (ActualHubTriangleCensus.siteTriangles R i).card) *
        Real.pi + siteFaceSum R i -
        ∑ k : Fin 9, if i ∈ cycleEdge k then SwitchData.angle (switchData h hr v k) else 0 := by ring
    _ = _ := by rw [actual_site_degree_offset h hr R]; split_ifs <;> ring

theorem actual_hub_edge_angle_balance {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 11) (hi : 9 ≤ i.val) :
    (∑ e ∈ incidentEdges R i, edgeAngle h hr R v e) = 2 * Real.pi := by
  rw [actual_site_edge_angle_row h hr R v, actual_hub_angle_sum h hr R i hi]
  have hn : ¬ i.val < 9 := by omega
  simp [hn, cycle_edge_hub_not_mem i hi]

theorem actual_ring_edge_angle_balance {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 9) :
    (∑ e ∈ incidentEdges R (nextSite i), edgeAngle h hr R v e) +
      sectorAngle v i = 2 * Real.pi := by
  have hcl := actual_ring_angle_closure h hr R v i
  rw [actual_site_edge_angle_row h hr R v, ring_switch_row]
  have hi : (nextSite i).val < 9 := by
    exact (nextRing i).isLt
  rw [if_pos hi]
  linarith

theorem owner_site_injective : Function.Injective nextSite := by decide +kernel

theorem site_owner_or_hub : ∀ i : Fin 11,
    (∃ k : Fin 9, nextSite k = i) ∨ 9 ≤ i.val := by decide +kernel

theorem owner_not_hub : ∀ (i : Fin 11), 9 ≤ i.val →
    ∀ k : Fin 9, nextSite k ≠ i := by decide +kernel

theorem actual_all_site_edge_angle_balance {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 11) :
    (∑ e ∈ incidentEdges R i, edgeAngle h hr R v e) +
      (∑ k : Fin 9, if nextSite k = i then sectorAngle v k else 0) = 2 * Real.pi := by
  classical
  rcases site_owner_or_hub i with ⟨k, rfl⟩ | hi
  · simpa only [owner_site_injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      using actual_ring_edge_angle_balance h hr R v k
  · simp only [owner_not_hub i hi, if_false, Finset.sum_const_zero, add_zero]
    exact actual_hub_edge_angle_balance h hr R v i hi

theorem weighted_incident_row {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (θ : Finset (Fin 11) → ℝ) (μ : Fin 11 → ℝ) :
    (∑ i : Fin 11, μ i * (∑ e ∈ incidentEdges R i, θ e)) =
      ∑ e ∈ edges R, (∑ i ∈ e, μ i) * θ e := by
  classical
  simp only [incidentEdges, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have he : (∑ i : Fin 11, if i ∈ e then μ i else 0) = ∑ i ∈ e, μ i := by
    simp [Finset.sum_ite_mem]
  calc
    _ = ∑ i : Fin 11, (if i ∈ e then μ i else 0) * θ e := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ e <;> simp [hi]
    _ = (∑ i : Fin 11, if i ∈ e then μ i else 0) * θ e := by rw [Finset.sum_mul]
    _ = _ := by rw [he]

/-- Exact cancellation for arbitrary real site multipliers. The owned
sector coefficient is at `nextSite k`, its actual ring owner. -/
theorem actual_weighted_angle_balance {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (μ : Fin 11 → ℝ) :
    (∑ e ∈ edges R, (∑ i ∈ e, μ i) * edgeAngle h hr R v e) +
      (∑ k : Fin 9, μ (nextSite k) * sectorAngle v k) =
        2 * Real.pi * (∑ i : Fin 11, μ i) := by
  classical
  have hs : (∑ i : Fin 11, μ i *
      ((∑ e ∈ incidentEdges R i, edgeAngle h hr R v e) +
        ∑ k : Fin 9, if nextSite k = i then sectorAngle v k else 0)) =
      ∑ i : Fin 11, μ i * (2 * Real.pi) := Finset.sum_congr rfl
    (fun i _ => congrArg (fun x : ℝ => μ i * x) (actual_all_site_edge_angle_balance h hr R v i))
  simp only [mul_add, Finset.sum_add_distrib] at hs
  rw [weighted_incident_row] at hs
  have hsector : (∑ i : Fin 11, μ i *
      (∑ k : Fin 9, if nextSite k = i then sectorAngle v k else 0)) =
      ∑ k : Fin 9, μ (nextSite k) * sectorAngle v k := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp [eq_comm]
  rw [hsector, ← Finset.sum_mul] at hs
  simpa only [mul_comm] using hs

/-- The exact disk area and all real paired-atom bounds give the area
budget without any metric-model premise. -/
theorem actual_edge_area_budget {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) :
    Real.pi ≤ (19 / 50 : ℝ) ^ 2 * (∑ e ∈ edges R, Real.sin (edgeAngle h hr R v e)) +
      ∑ i : Fin 9, areaEnvelope (sectorAngle v i) := by
  classical
  have ht := actual_shared_factor_area h hr R v
  rw [← actual_paired_area_sum h hr R v] at ht
  have he := Finset.sum_le_sum (s := edges R)
    (fun e he => (actual_edge_angle_area_domain h hr R v he).2.2.2)
  rw [← Finset.mul_sum] at he
  have hs := actual_total_sector_area_envelope h hr v
  linarith

theorem actual_edge_metric_model {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) :
    (edges R).card = 21 ∧
      (∀ e ∈ edges R, 0 ≤ edgeAngle h hr R v e ∧ edgeAngle h hr R v e ≤ Real.pi) ∧
      (∀ i : Fin 11, 9 ≤ i.val →
        (∑ e ∈ incidentEdges R i, edgeAngle h hr R v e) = 2 * Real.pi) ∧
      (∀ i : Fin 9, (∑ e ∈ incidentEdges R (nextSite i), edgeAngle h hr R v e) +
        sectorAngle v i = 2 * Real.pi) ∧
      Real.pi ≤ (19 / 50 : ℝ) ^ 2 * (∑ e ∈ edges R, Real.sin (edgeAngle h hr R v e)) +
        (∑ i : Fin 9, areaEnvelope (sectorAngle v i)) ∧
      2 * Real.pi ≤ ∑ i : Fin 9, widthEnvelope (sectorAngle v i) := by
  refine ⟨actual_edges_twenty_one h hr R, ?_, ?_, ?_,
    actual_edge_area_budget h hr R v, actual_total_width_envelope h hr v⟩
  · intro e he
    have hd := actual_edge_angle_area_domain h hr R v he
    exact ⟨hd.1, hd.2.1⟩
  · exact fun i hi => actual_hub_edge_angle_balance h hr R v i hi
  · exact fun i => actual_ring_edge_angle_balance h hr R v i

end N11Formalization.ActualEdgeMetricModel

#check @N11Formalization.ActualEdgeMetricModel.actual_paired_area_sum
#check @N11Formalization.ActualEdgeMetricModel.actual_edge_metric_model
#print axioms N11Formalization.ActualEdgeMetricModel.actual_paired_area_sum
#print axioms N11Formalization.ActualEdgeMetricModel.actual_hub_edge_angle_balance
#print axioms N11Formalization.ActualEdgeMetricModel.actual_ring_edge_angle_balance
#print axioms N11Formalization.ActualEdgeMetricModel.actual_edge_metric_model
#print axioms N11Formalization.ActualEdgeMetricModel.actual_weighted_angle_balance
