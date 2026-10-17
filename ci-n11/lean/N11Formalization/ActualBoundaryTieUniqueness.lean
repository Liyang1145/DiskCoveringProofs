import N11Formalization.ActualCoverStructuralReduction
import N11Formalization.FlashCoverReductionBlockerGeometry

/-! A pair of distinct inward ring sites has at most ONE equal-distance
point in their actual closed circle-cap overlap.
Two bisector/circle intersections would be ≥2r apart; the parallelogram
identity then forces both sites to be the same chord midpoint.
No transversality, line/circle root-count or parity premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryTieUniqueness
open ActualCoverStructuralReduction ActualRingDirectionOrder

theorem bisector_equation {x a b : Point} (h : dist x a = dist x b) :
    2*inner ℝ x (b-a) = ‖b‖^2-‖a‖^2 := by
  have he := ActualHubEdgeGeometry.square_difference x a b
  rw [h,sub_self] at he
  linarith

theorem squared_norm_difference_bound {a b : Point} {A : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A) :
    |‖b‖^2-‖a‖^2| ≤ ‖b-a‖*(2*A) := by
  have he : |‖b‖^2-‖a‖^2| = |‖b‖-‖a‖| * (‖b‖+‖a‖) := by
    calc
      |‖b‖^2-‖a‖^2| = |(‖b‖-‖a‖)*(‖b‖+‖a‖)| := by congr 1; ring
      _ = |‖b‖-‖a‖| * |‖b‖+‖a‖| := abs_mul _ _
      _ = |‖b‖-‖a‖| * (‖b‖+‖a‖) := by
        rw [abs_of_nonneg (add_nonneg (norm_nonneg b) (norm_nonneg a))]
  rw [he]
  exact (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le b a)
    (add_nonneg (norm_nonneg b) (norm_nonneg a))).trans
      (mul_le_mul_of_nonneg_left (by linarith : ‖b‖+‖a‖ ≤ 2*A) (norm_nonneg (b-a)))

theorem chord_midpoint_bound {x y a b : Point} {A : ℝ}
    (hab : a ≠ b) (hxy : x ≠ y) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A)
    (hxt : dist x a = dist x b) (hyt : dist y a = dist y b) :
    ‖x+y‖ ≤ 2*A := by
  have hdne : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hdn : 0 < ‖b-a‖ := norm_pos_iff.mpr hdne
  have hxq := bisector_equation hxt
  have hyq := bisector_equation hyt
  have hdw : inner ℝ (b-a) (x-y) = 0 := by
    rw [real_inner_comm,inner_sub_left]
    linarith
  have hsumw : inner ℝ (x+y) (x-y) = 0 := by
    simp only [inner_add_left,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm]
    rw [hx,hy]
    ring
  obtain ⟨t,ht⟩ := parallel_of_orthogonal hdne (sub_ne_zero.mpr hxy) hdw hsumw
  have hscalar : t*‖b-a‖^2 = ‖b‖^2-‖a‖^2 := by
    have hh := congrArg (fun z : Point => inner ℝ z (b-a)) ht
    simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at hh
    linarith
  have hscalarAbs : |t| * ‖b-a‖^2 = |‖b‖^2-‖a‖^2| := by
    rw [← hscalar,abs_mul,abs_of_nonneg (sq_nonneg ‖b-a‖)]
  have hbound := squared_norm_difference_bound ha hb
  have hmul : (|t| * ‖b-a‖)*‖b-a‖ ≤ (2*A)*‖b-a‖ := by
    calc
      (|t| * ‖b-a‖)*‖b-a‖ = |t| * ‖b-a‖^2 := by ring
      _ = |‖b‖^2-‖a‖^2| := hscalarAbs
      _ ≤ ‖b-a‖*(2*A) := hbound
      _ = (2*A)*‖b-a‖ := by ring
  have htn := le_of_mul_le_mul_right hmul hdn
  rw [ht,norm_smul,Real.norm_eq_abs]
  exact htn

theorem midpoint_distance_identity (x y a : Point) :
    4*dist (((1:ℝ)/2) • (x+y)) a^2 + dist x y^2 =
      2*(dist x a^2+dist y a^2) := by
  simp only [dist_eq_norm,PinTangentGeometry.norm_sq_coords,
    PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

theorem unique_cap_tie {a b x y : Point} {r : ℝ}
    (hab : a ≠ b) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ‖a‖ ≤ Real.sqrt (1-r^2)) (hb : ‖b‖ ≤ Real.sqrt (1-r^2))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxt : dist x a = dist x b) (hyt : dist y a = dist y b)
    (hxr : dist x a ≤ r) (hyr : dist y a ≤ r) : x = y := by
  by_contra hxy
  have hsum := chord_midpoint_bound hab hxy hx hy ha hb hxt hyt
  have hsqrt : Real.sqrt (1-r^2)^2 = 1-r^2 := Real.sq_sqrt (by nlinarith)
  have hsumSq : ‖x+y‖^2 ≤ 4*(1-r^2) := by
    nlinarith [norm_nonneg (x+y),Real.sqrt_nonneg (1-r^2)]
  have hpara : ‖x-y‖^2+‖x+y‖^2 = 4 := by
    rw [norm_sub_sq_real,norm_add_sq_real,hx,hy]
    ring
  have hchord : 4*r^2 ≤ dist x y^2 := by
    rw [dist_eq_norm]
    linarith
  have hxa : dist x a^2 ≤ r^2 := by nlinarith [dist_nonneg (x := x) (y := a)]
  have hya : dist y a^2 ≤ r^2 := by nlinarith [dist_nonneg (x := y) (y := a)]
  have hxb : dist x b^2 ≤ r^2 := by rw [← hxt]; exact hxa
  have hyb : dist y b^2 ≤ r^2 := by rw [← hyt]; exact hya
  have hma := midpoint_distance_identity x y a
  have hmb := midpoint_distance_identity x y b
  have hda : dist (((1:ℝ)/2) • (x+y)) a = 0 := by
    nlinarith [dist_nonneg (x := ((1:ℝ)/2) • (x+y)) (y := a)]
  have hdb : dist (((1:ℝ)/2) • (x+y)) b = 0 := by
    nlinarith [dist_nonneg (x := ((1:ℝ)/2) • (x+y)) (y := b)]
  exact hab ((dist_eq_zero.mp hda).symm.trans (dist_eq_zero.mp hdb))

theorem Representative.unique_ring_cap_tie {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr1 : r < 1)
    {i j : Fin 9} (hij : i ≠ j) {x y : Point}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxt : dist x (c (ringSite i)) = dist x (c (ringSite j)))
    (hyt : dist y (c (ringSite i)) = dist y (c (ringSite j)))
    (hxr : dist x (c (ringSite i)) ≤ r) (hyr : dist y (c (ringSite i)) ≤ r) : x = y := by
  have hsites : ringSite i ≠ ringSite j := by
    intro he
    exact hij (Fin.ext (congrArg (fun k : Fin 11 => k.val) he))
  exact unique_cap_tie (fun he => hsites (h.injective he)) (Covers.nonneg h.cover) hr1
    (h.inward (ringSite i) i.isLt) (h.inward (ringSite j) j.isLt) hx hy hxt hyt hxr hyr

end N11Formalization.ActualBoundaryTieUniqueness
#check @N11Formalization.ActualBoundaryTieUniqueness.unique_cap_tie
#check @N11Formalization.ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie
#print axioms N11Formalization.ActualBoundaryTieUniqueness.unique_cap_tie
#print axioms N11Formalization.ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie
