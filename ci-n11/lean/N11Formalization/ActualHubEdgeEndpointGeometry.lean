import N11Formalization.ActualCoverStructuralReduction
import N11Formalization.FlashCoverReductionBlockerGeometry

/-! Pure Euclidean ingredients for genuine hub-edge endpoint witnesses.
Three distinct sites cannot be equidistant from two distinct points.
Thus a nontrivial common hub segment has a midpoint strictly separated
from every ring site, even with cocircular degeneracies elsewhere. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubEdgeEndpointGeometry
open ActualVoronoiCells ActualHubEdgeGeometry ActualCoverStructuralReduction
open ActualRingDirectionOrder

theorem translated_bisector {x a b : Point} (h : dist x a = dist x b) :
    ‖b-a‖^2 = 2*inner ℝ (x-a) (b-a) := by
  have he := square_difference x a b
  rw [h,sub_self] at he
  simp only [norm_sub_sq_real,inner_sub_left,inner_sub_right,
    real_inner_self_eq_norm_sq,real_inner_comm] at he ⊢
  linarith

theorem two_points_three_sites {x y a b k : Point}
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : dist x a = dist x b) (hya : dist y a = dist y b)
    (hxk : dist x k = dist x a) (hyk : dist y k = dist y a) :
    k = a ∨ k = b := by
  have hdne : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hdn : 0 < ‖b-a‖ := norm_pos_iff.mpr hdne
  have hdx := translated_bisector hxa
  have hdy := translated_bisector hya
  have hkx := translated_bisector hxk.symm
  have hky := translated_bisector hyk.symm
  have hdw : inner ℝ (b-a) (x-y) = 0 := by
    rw [real_inner_comm,inner_sub_left]
    simp only [inner_sub_left] at hdx hdy
    linarith
  have hkw : inner ℝ (k-a) (x-y) = 0 := by
    rw [real_inner_comm,inner_sub_left]
    simp only [inner_sub_left] at hkx hky
    linarith
  obtain ⟨t,ht⟩ := parallel_of_orthogonal hdne (sub_ne_zero.mpr hxy) hdw hkw
  have hkx' := translated_bisector hxk.symm
  rw [ht,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_right] at hkx'
  have hscaled : t*‖b-a‖^2 = 2*t*inner ℝ (x-a) (b-a) := by rw [hdx]; ring
  have hf : t*(t-1)*‖b-a‖^2 = 0 := by nlinarith
  have hn : ‖b-a‖^2 ≠ 0 := (sq_pos_of_pos hdn).ne'
  have htprod : t*(t-1) = 0 := (mul_eq_zero.mp hf).resolve_right hn
  rcases mul_eq_zero.mp htprod with ht0 | ht1
  · left
    rw [ht0,zero_smul] at ht
    exact sub_eq_zero.mp ht
  · right
    have htone : t = 1 := by linarith
    rw [htone,one_smul] at ht
    exact sub_left_inj.mp ht

theorem midpoint_gap_identity (x y a b : Point) :
    dist (((1:ℝ)/2) • (x+y)) b^2-dist (((1:ℝ)/2) • (x+y)) a^2 =
      ((dist x b^2-dist x a^2)+(dist y b^2-dist y a^2))/2 := by
  have hm := square_difference (((1:ℝ)/2) • (x+y)) b a
  have hx := square_difference x b a
  have hy := square_difference y b a
  rw [real_inner_smul_left,inner_add_left] at hm
  linarith

theorem strict_midpoint {c : Fin 11 → Point} {r : ℝ} (h : Representative c r)
    {x y : Point} (hx : x ∈ Cell c 9 ∩ Cell c 10)
    (hy : y ∈ Cell c 9 ∩ Cell c 10) (hxy : x ≠ y) :
    (((1:ℝ)/2) • (x+y)) ∈ Cell c 9 ∩ Cell c 10 ∧
      (((1:ℝ)/2) • (x+y)) ∈ StrictRing c := by
  let z := ((1:ℝ)/2) • (x+y)
  have hz : z ∈ Cell c 9 ∩ Cell c 10 := by
    have hc := ((cell_convex c 9).inter (cell_convex c 10)) hx hy
      (by norm_num : 0 ≤ ((1:ℝ)/2)) (by norm_num : 0 ≤ ((1:ℝ)/2))
      (by norm_num : ((1:ℝ)/2)+((1:ℝ)/2)=1)
    simpa only [z,smul_add] using hc
  refine ⟨hz,?_⟩
  intro i
  by_contra hnot
  have hztie : dist z (c (ringSite i)) = dist z (c 9) :=
    le_antisymm (le_of_not_gt hnot) (hz.1 (ringSite i))
  have hxnear := hx.1 (ringSite i)
  have hynear := hy.1 (ringSite i)
  have hxgap : 0 ≤ dist x (c (ringSite i))^2-dist x (c 9)^2 := by
    nlinarith [dist_nonneg (x := x) (y := c (ringSite i)),dist_nonneg (x := x) (y := c 9)]
  have hygap : 0 ≤ dist y (c (ringSite i))^2-dist y (c 9)^2 := by
    nlinarith [dist_nonneg (x := y) (y := c (ringSite i)),dist_nonneg (x := y) (y := c 9)]
  have hmid := midpoint_gap_identity x y (c 9) (c (ringSite i))
  change dist z (c (ringSite i))^2-dist z (c 9)^2 = _ at hmid
  rw [hztie,sub_self] at hmid
  have hxtie : dist x (c (ringSite i)) = dist x (c 9) := by
    nlinarith [dist_nonneg (x := x) (y := c (ringSite i)),dist_nonneg (x := x) (y := c 9)]
  have hytie : dist y (c (ringSite i)) = dist y (c 9) := by
    nlinarith [dist_nonneg (x := y) (y := c (ringSite i)),dist_nonneg (x := y) (y := c 9)]
  have hhub : c 9 ≠ c 10 := fun he => (by decide : (9 : Fin 11) ≠ 10) (h.injective he)
  have hxa : dist x (c 9) = dist x (c 10) := le_antisymm (hx.1 10) (hx.2 9)
  have hya : dist y (c 9) = dist y (c 10) := le_antisymm (hy.1 10) (hy.2 9)
  rcases two_points_three_sites hhub hxy hxa hya hxtie hytie with he | he
  · have hi := h.injective he
    have hv := congrArg (fun j : Fin 11 => j.val) hi
    have hl := i.isLt
    change i.val = 9 at hv
    omega
  · have hi := h.injective he
    have hv := congrArg (fun j : Fin 11 => j.val) hi
    have hl := i.isLt
    change i.val = 10 at hv
    omega

end N11Formalization.ActualHubEdgeEndpointGeometry
#check @N11Formalization.ActualHubEdgeEndpointGeometry.two_points_three_sites
#check @N11Formalization.ActualHubEdgeEndpointGeometry.strict_midpoint
#print axioms N11Formalization.ActualHubEdgeEndpointGeometry.two_points_three_sites
#print axioms N11Formalization.ActualHubEdgeEndpointGeometry.strict_midpoint
