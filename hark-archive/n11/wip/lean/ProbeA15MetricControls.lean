import N11Formalization.ActualBoundaryExteriorGeometry

/-! Exact outside-center counterexample to dropping the inside-site
hypotheses of the exterior sign lemma. This is NOT an actual cover. -/
set_option autoImplicit false
namespace N11Formalization.ProbeA15MetricControls
open FlashTiling
def a : Point := !₂[2,-1]
def b : Point := !₂[2,1]
def k : Point := !₂[1,2]
def U : Point := !₂[1,0]

theorem exact_squared_rows :
    dist U a^2=2 ∧ dist U b^2=2 ∧ dist (0 : Point) a^2=5 ∧
      dist (0 : Point) b^2=5 ∧ dist (0 : Point) k^2=5 ∧ dist U k^2=4 := by
  norm_num [dist_eq_norm,PinTangentGeometry.norm_sq_coords,a,b,k,U,PiLp.sub_apply]

theorem outside_centers_same_side :
    ‖U‖=1 ∧ ‖(0 : Point)‖<1 ∧ dist U a=dist U b ∧
      dist (0 : Point) a=dist (0 : Point) b ∧
      dist (0 : Point) a=dist (0 : Point) k ∧ dist U a ≤ dist U k ∧
      0 < orient a b U*orient a b k := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := exact_squared_rows
  have hn : ‖U‖^2=1 := by norm_num [PinTangentGeometry.norm_sq_coords,U]
  refine ⟨?_,by simp,?_,?_,?_,?_,?_⟩
  · nlinarith [norm_nonneg U]
  · nlinarith [dist_nonneg (x := U) (y := a),dist_nonneg (x := U) (y := b)]
  · nlinarith [dist_nonneg (x := (0 : Point)) (y := a),dist_nonneg (x := (0 : Point)) (y := b)]
  · nlinarith [dist_nonneg (x := (0 : Point)) (y := a),dist_nonneg (x := (0 : Point)) (y := k)]
  · nlinarith [dist_nonneg (x := U) (y := a),dist_nonneg (x := U) (y := k)]
  · norm_num [orient,det2,a,b,k,U,PiLp.sub_apply]

theorem sites_really_outside : 1<‖a‖ ∧ 1<‖b‖ := by
  have ha : ‖a‖^2=5 := by norm_num [PinTangentGeometry.norm_sq_coords,a]
  have hb : ‖b‖^2=5 := by norm_num [PinTangentGeometry.norm_sq_coords,b]
  constructor <;> nlinarith [norm_nonneg a,norm_nonneg b]
end N11Formalization.ProbeA15MetricControls
#check @N11Formalization.ProbeA15MetricControls.outside_centers_same_side
#check @N11Formalization.ProbeA15MetricControls.sites_really_outside
#print axioms N11Formalization.ProbeA15MetricControls.exact_squared_rows
#print axioms N11Formalization.ProbeA15MetricControls.outside_centers_same_side
#print axioms N11Formalization.ProbeA15MetricControls.sites_really_outside
