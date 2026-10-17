import N11Formalization.ActualAnglePhase
import N11Formalization.ActualCenterRingShoelace

/-! Actual site-angle phase cancellation from the accepted boundary chain.
This produces a modulo-2*pi relation. Its lift to the exact real site sum
requires a separate winding/upper-bound proof; it is NOT assumed here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSiteAngleChain
open ActualFiniteNearestRefinement ActualTriangleBoundaryChain
open ActualAnglePhase ActualMetricAngleAtoms ActualCoverStructuralReduction
open ActualBoundaryChainConservation ActualCenterRingShoelace
open ActualRefinementInteriorFacetCount ActualHubLinkCycles
open ActualFaceCircumradiusAtoms ActualRefinementTriangleUniqueness
open ActualHubTriangleCensus

theorem weighted_triangle_row (t : Fin 3 → Fin 11) (i : Fin 11)
    (w : Fin 11 → Real.Angle) :
    (∑ j : Fin 11, triangleBoundary t i j • w j) =
      (if i=t 0 then w (t 1)-w (t 2) else 0) +
      (if i=t 1 then w (t 2)-w (t 0) else 0) +
      (if i=t 2 then w (t 0)-w (t 1) else 0) := by
  simp only [triangleBoundary,add_zsmul,sub_zsmul,Finset.sum_add_distrib,
    ite_and,ite_smul,one_zsmul,zero_zsmul,
    Finset.sum_ite_irrel]
  simp only [Finset.sum_neg_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const_zero]
  split_ifs <;> abel

def siteFaceSum {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) : ℝ :=
  ∑ A : R.Index, ∑ s : Fin 3, if R.labels A s=i then faceAngle R A s else 0

theorem actual_one_face_site_phase {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (i : Fin 11) :
    ((∑ s : Fin 3, if R.labels A s=i then faceAngle R A s else 0) : Real.Angle) =
      -(∑ j : Fin 11, coefficient R A i j • sitePhase c i j) := by
  simp only [coefficient]
  rw [weighted_triangle_row,Fin.sum_univ_three]
  simp only [eq_comm (a := i) (b := R.labels A 0),
    eq_comm (a := i) (b := R.labels A 1),eq_comm (a := i) (b := R.labels A 2)]
  have hs (s : Fin 3) := actual_face_slot_phase R A s
  by_cases h0 : R.labels A 0=i
  · have h1 : R.labels A 1≠i :=
      fun he => ((Refinement.labels_injective R A).ne (by decide : (1:Fin 3)≠0)) (he.trans h0.symm)
    have h2 : R.labels A 2≠i :=
      fun he => ((Refinement.labels_injective R A).ne (by decide : (2:Fin 3)≠0)) (he.trans h0.symm)
    simp only [h0,h1,h2,if_true,if_false,eq_comm,Real.Angle.coe_zero,add_zero,zero_add]
    rw [hs 0]
    simp only [zero_add,h0]
    abel
  · by_cases h1 : R.labels A 1=i
    · have h2 : R.labels A 2≠i :=
        fun he => ((Refinement.labels_injective R A).ne (by decide : (2:Fin 3)≠1)) (he.trans h1.symm)
      simp only [h0,h1,h2,if_true,if_false,eq_comm,Real.Angle.coe_zero,add_zero,zero_add]
      rw [hs 1]
      change sitePhase c (R.labels A 1) (R.labels A 0) -
        sitePhase c (R.labels A 1) (R.labels A 2)=_
      rw [h1]
      abel
    · by_cases h2 : R.labels A 2=i
      · simp only [h0,h1,h2,if_true,if_false,eq_comm,Real.Angle.coe_zero,add_zero,zero_add]
        rw [hs 2]
        change sitePhase c (R.labels A 2) (R.labels A 1) -
          sitePhase c (R.labels A 2) (R.labels A 0)=_
        rw [h2]
        abel
      · simp [h0,h1,h2,eq_comm]

theorem actual_site_face_phase_chain {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) :
    (siteFaceSum R i : Real.Angle) =
      -(∑ j : Fin 11, total R i j • sitePhase c i j) := by
  have he : (siteFaceSum R i : Real.Angle) =
      ∑ A : R.Index, ((∑ s : Fin 3, if R.labels A s=i then faceAngle R A s else 0) : Real.Angle) :=
    by
      change Real.Angle.coeHom (∑ A : R.Index,
        ∑ s : Fin 3, if R.labels A s=i then faceAngle R A s else 0)=_
      simp only [map_sum,Real.Angle.coe_coeHom]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> rfl
  rw [he]
  simp_rw [actual_one_face_site_phase]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [total,Finset.sum_smul]

theorem actual_hub_face_sum_mod_two_pi {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) :
    (siteFaceSum R i : Real.Angle)=0 := by
  rw [actual_site_face_phase_chain]
  have ht (j : Fin 11) : total R i j=0 := by
    apply total_nonboundary_zero h hr R
    intro hb
    have hh := boundary_labels_ring i j hb
    omega
  simp only [ht,zero_zsmul,Finset.sum_const_zero,neg_zero]

theorem actual_hub_face_sum_integer_turns {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) :
    ∃ n : ℤ, siteFaceSum R i=(n:ℝ)*(2*Real.pi) := by
  obtain ⟨n,hn⟩ := Real.Angle.coe_eq_zero_iff.mp (actual_hub_face_sum_mod_two_pi h hr R i hi)
  exact ⟨n,by simpa only [zsmul_eq_mul] using hn.symm⟩

theorem actual_site_face_sum_nonneg {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) : 0 ≤ siteFaceSum R i := by
  apply Finset.sum_nonneg
  intro A hA
  apply Finset.sum_nonneg
  intro s hs
  split_ifs
  · exact (actual_face_angle_bounds R A s).1
  · exact le_rfl

theorem actual_site_face_sum_positive {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {i : Fin 11}
    (hi : i ∈ labelSet R A) : 0 < siteFaceSum R i := by
  obtain ⟨s,hs⟩ := mem_labelSet.mp hi
  have hpos : 0 < ∑ t : Fin 3, if R.labels A t=i then faceAngle R A t else 0 := by
    apply Finset.sum_pos'
    · intro t ht
      split_ifs
      · exact (actual_face_angle_bounds R A t).1
      · exact le_rfl
    · refine ⟨s,Finset.mem_univ _,?_⟩
      rw [if_pos hs]
      exact (actual_face_angle_strict R A s).1
  unfold siteFaceSum
  apply Finset.sum_pos'
  · intro B hB
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · exact (actual_face_angle_bounds R B t).1
    · exact le_rfl
  · exact ⟨A,Finset.mem_univ _,hpos⟩

theorem actual_hub_positive_integer_turns {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) :
    ∃ n : ℤ, 1 ≤ n ∧ siteFaceSum R i=(n:ℝ)*(2*Real.pi) := by
  obtain ⟨A,_,_,_,h9,h10,_,_⟩ :=
    ActualRefinementFacetRetention.Refinement.hub_edge_two_retained R h hr
  have hmem : i ∈ labelSet R A := by
    have hv := i.isLt
    have he : i=9 ∨ i=10 := by
      have hh : i.val=9 ∨ i.val=10 := by omega
      exact hh.imp (fun ht => Fin.ext ht) (fun ht => Fin.ext ht)
    rcases he with rfl | rfl
    · exact mem_labelSet.mpr h9
    · exact mem_labelSet.mpr h10
  have hp := actual_site_face_sum_positive R hmem
  obtain ⟨n,hn⟩ := actual_hub_face_sum_integer_turns h hr R i hi
  refine ⟨n,?_,hn⟩
  have hnR : 0 < (n:ℝ) := by
    by_contra hnot
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot)
      (by positivity : (0:ℝ) ≤ 2*Real.pi)
    rw [← hn] at hm
    linarith
  have hnI : 0 < n := by exact_mod_cast hnR
  omega

theorem actual_all_site_face_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ∑ i : Fin 11, siteFaceSum R i=11*Real.pi := by
  unfold siteFaceSum
  rw [Finset.sum_comm]
  have he (A : R.Index) :
      (∑ i : Fin 11, ∑ s : Fin 3, if R.labels A s=i then faceAngle R A s else 0)=Real.pi := by
    rw [Finset.sum_comm]
    simp only [eq_comm (a := R.labels A _) (b := _),Finset.sum_ite_eq',
      Finset.mem_univ,if_true]
    exact actual_face_angle_sum h R A
  rw [Finset.sum_congr rfl (fun A _ => he A)]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ActualRefinementEulerCount.actual_faces_eleven h hr R,Nat.cast_ofNat]

theorem actual_one_face_site_mass_lt_pi {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) {i : Fin 11}
    (hi : i ∈ labelSet R A) :
    (∑ s : Fin 3, if R.labels A s=i then faceAngle R A s else 0) < Real.pi := by
  classical
  obtain ⟨s,hs⟩ := mem_labelSet.mp hi
  have he : (fun t : Fin 3 => if R.labels A t=i then faceAngle R A t else 0) =
      (fun t : Fin 3 => if t=s then faceAngle R A s else 0) := by
    funext t
    by_cases ht : t=s
    · subst t
      rw [if_pos hs,if_pos rfl]
    · have hn : R.labels A t≠i :=
        fun hh => ht ((Refinement.labels_injective R A) (hh.trans hs.symm))
      rw [if_neg hn,if_neg ht]
  rw [he]
  simpa using (actual_face_angle_strict R A s).2

theorem actual_site_face_sum_lt_count_pi {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {i : Fin 11} (hne : (siteTriangles R i).Nonempty) :
    siteFaceSum R i < (siteTriangles R i).card*Real.pi := by
  classical
  have he : siteFaceSum R i =
      ∑ A ∈ siteTriangles R i, ∑ s : Fin 3, if R.labels A s=i then faceAngle R A s else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro A hA hnA
    have hi : i ∉ labelSet R A := fun hh => hnA ((mem_siteTriangles R).mpr hh)
    apply Finset.sum_eq_zero
    intro s hs
    rw [if_neg (fun hh => hi (mem_labelSet.mpr ⟨s,hh⟩))]
  rw [he]
  have hb := Finset.sum_lt_sum_of_nonempty hne
    (fun A hA => actual_one_face_site_mass_lt_pi R A ((mem_siteTriangles R).mp hA))
  simpa only [Finset.sum_const,nsmul_eq_mul] using hb

/-- The real one-turn hub sum is already paid for degree three/four.
Higher degrees still require the general angular star bound. -/
theorem actual_small_degree_hub_angle_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val) (hd : (neighbors R i).card ≤ 4) :
    siteFaceSum R i=2*Real.pi := by
  obtain ⟨n,hn,he⟩ := actual_hub_positive_integer_turns h hr R i hi
  have hpos : 0 < siteFaceSum R i := by
    rw [he]
    have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    exact mul_pos (by linarith) (by positivity)
  have hne : (siteTriangles R i).Nonempty := by
    by_contra hnot
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hzero : siteFaceSum R i=0 := by
      apply Finset.sum_eq_zero
      intro A hA
      apply Finset.sum_eq_zero
      intro s hs
      have hnot : R.labels A s ≠ i := by
        intro hh
        have hm := (mem_siteTriangles R).mpr (mem_labelSet.mpr ⟨s,hh⟩)
        rw [hempty] at hm
        exact Finset.notMem_empty A hm
      rw [if_neg hnot]
    linarith
  have hb := actual_site_face_sum_lt_count_pi R hne
  rw [actual_hub_face_neighbor_count h hr R hi,he] at hb
  have hdR : ((neighbors R i).card:ℝ) ≤ 4 := by exact_mod_cast hd
  have hn2 : n < 2 := by
    have hnR : (n:ℝ) < 2 := by nlinarith [Real.pi_pos]
    exact_mod_cast hnR
  have hn1 : n=1 := by omega
  simpa only [hn1,Int.cast_one,one_mul] using he

end N11Formalization.ActualSiteAngleChain
#check @N11Formalization.ActualSiteAngleChain.actual_hub_face_sum_integer_turns
#check @N11Formalization.ActualSiteAngleChain.actual_hub_positive_integer_turns
#check @N11Formalization.ActualSiteAngleChain.actual_all_site_face_sum
#check @N11Formalization.ActualSiteAngleChain.actual_small_degree_hub_angle_sum
#print axioms N11Formalization.ActualSiteAngleChain.actual_hub_face_sum_integer_turns
#print axioms N11Formalization.ActualSiteAngleChain.actual_hub_positive_integer_turns
#print axioms N11Formalization.ActualSiteAngleChain.actual_all_site_face_sum
#print axioms N11Formalization.ActualSiteAngleChain.actual_small_degree_hub_angle_sum
