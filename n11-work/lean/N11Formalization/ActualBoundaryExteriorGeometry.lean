import N11Formalization.ActualSelectedEdgeOrientation

/-! Exact exterior-side sign from genuine nearest equations.
For a boundary pair with both sites insideD, a unit-circle nearest point
is opposite every noncollinear third site at a true interior nearest
witness. No drawn hull, acute-face, genericity or disk premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryExteriorGeometry
open ActualHubEdgeGeometry ActualHubEdgeEndpointGeometry ActualIncidentFacetAdjacency
open FlashTiling

def midpoint (a b : Point) : Point := (1/2 : ℝ) • a+(1/2 : ℝ) • b

theorem midpoint_inside {a b : Point} (ha : ‖a‖<1) (hb : ‖b‖<1) :
    ‖midpoint a b‖<1 := by
  have hh := norm_add_le ((1/2 : ℝ) • a) ((1/2 : ℝ) • b)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at hh
  change ‖midpoint a b‖ ≤ (1/2 : ℝ)*‖a‖+(1/2 : ℝ)*‖b‖ at hh
  linarith

theorem outward_inner_positive {U p : Point} (hU : ‖U‖=1) (hp : ‖p‖<1) :
    0 < inner ℝ U (U-p) := by
  have hh := (abs_le.mp (abs_real_inner_le_norm U p)).2
  rw [hU,one_mul] at hh
  rw [inner_sub_right,real_inner_self_eq_norm_sq,hU]
  norm_num
  linarith

theorem midpoint_sub (a b : Point) : midpoint a b-a=(1/2 : ℝ) • (b-a) := by
  unfold midpoint
  module

theorem bisector_perp_coordinate {a b x : Point} (hab : a ≠ b)
    (he : dist x a=dist x b) :
    ∃ s : ℝ, x-midpoint a b=s • perp (b-a) := by
  have hw : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hbis := translated_bisector he
  have horth : inner ℝ (x-midpoint a b) (b-a)=0 := by
    have hv : x-midpoint a b=(x-a)-(midpoint a b-a) := by module
    rw [hv,inner_sub_left,midpoint_sub,real_inner_smul_left,real_inner_self_eq_norm_sq]
    linarith
  exact parallel_of_orthogonal (perp_ne hw) hw (perp_inner (b-a)) horth

theorem nearest_projection_nonpos {a k U z : Point}
    (hz : dist z a=dist z k) (hU : dist U a ≤ dist U k) :
    inner ℝ (U-z) (k-a) ≤ 0 := by
  have hu := square_difference U a k
  have hzz := square_difference z a k
  rw [hz,sub_self] at hzz
  have hsq : dist U a^2 ≤ dist U k^2 := by
    nlinarith [dist_nonneg (x := U) (y := a),dist_nonneg (x := U) (y := k)]
  rw [inner_sub_left]
  linarith

theorem boundary_point_opposite_third {a b k U z : Point}
    (hab : a ≠ b) (ha : ‖a‖<1) (hb : ‖b‖<1)
    (hU : ‖U‖=1) (hz : ‖z‖<1)
    (hUeq : dist U a=dist U b) (hzeq : dist z a=dist z b)
    (hzk : dist z a=dist z k) (hUk : dist U a ≤ dist U k)
    (hk : orient a b k ≠ 0) :
    orient a b U * orient a b k < 0 := by
  let p := perp (b-a)
  have hpne : p ≠ 0 := perp_ne (sub_ne_zero.mpr hab.symm)
  have hpq : 0 < ‖p‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hpne)
  obtain ⟨s,hs⟩ := bisector_perp_coordinate hab hUeq
  obtain ⟨v,hv⟩ := bisector_perp_coordinate hab hzeq
  have hdelta : U-z=(s-v) • p := by
    change U-midpoint a b=s • p at hs
    change z-midpoint a b=v • p at hv
    calc
      U-z=(U-midpoint a b)-(z-midpoint a b) := by module
      _=s • p-v • p := by rw [hs,hv]
      _=(s-v) • p := by module
  have hS := outward_inner_positive hU (midpoint_inside ha hb)
  have hT := outward_inner_positive hU hz
  rw [hs,real_inner_smul_right] at hS
  rw [hdelta,real_inner_smul_right] at hT
  change 0 < s*inner ℝ U p at hS
  have hK := nearest_projection_nonpos hzk hUk
  rw [hdelta,real_inner_smul_left] at hK
  change (s-v)*inner ℝ (perp (b-a)) (k-a) ≤ 0 at hK
  rw [perp_inner_orient] at hK
  have hOU : orient a b U=s*‖p‖^2 := by
    rw [← perp_inner_orient]
    have he : U-a=(U-midpoint a b)+(midpoint a b-a) := by module
    rw [he,hs,midpoint_sub,inner_add_right,real_inner_smul_right,
      real_inner_smul_right,perp_inner,mul_zero,add_zero,real_inner_self_eq_norm_sq]
  rw [hOU]
  rcases mul_pos_iff.mp hS with ⟨hspos,hnpos⟩ | ⟨hsneg,hnneg⟩
  · have hTpos : 0 < s-v := by
      by_contra hnot
      have hnon := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hnpos.le
      exact not_lt_of_ge hnon hT
    have hKneg : orient a b k < 0 := by
      rcases lt_or_gt_of_ne hk with he | he
      · exact he
      · exact (not_lt_of_ge hK (mul_pos hTpos he)).elim
    exact mul_neg_of_pos_of_neg (mul_pos hspos hpq) hKneg
  · have hTneg : s-v < 0 := by
      by_contra hnot
      have hnon := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hnot) hnneg.le
      exact not_lt_of_ge hnon hT
    have hKpos : 0 < orient a b k := by
      rcases lt_or_gt_of_ne hk with he | he
      · exact (not_lt_of_ge hK (mul_pos_of_neg_of_neg hTneg he)).elim
      · exact he
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hsneg hpq) hKpos

end N11Formalization.ActualBoundaryExteriorGeometry
#check @N11Formalization.ActualBoundaryExteriorGeometry.boundary_point_opposite_third
#print axioms N11Formalization.ActualBoundaryExteriorGeometry.boundary_point_opposite_third
