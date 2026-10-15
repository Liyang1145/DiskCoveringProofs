import N11Formalization.C450QuadraticBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Actual grouped C450 harmonic identities and sign-safe scalar bounds.
No continuous packet/geometry/capacity certificate is supplied here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedAnalytic
open C450OuterGeometry

def arc (a p x : ℝ) : ℝ := a*x+p*Real.sin x

/-- A global version: an explicit spectral amplitude bound pays the slope.
Actual source packets must still certify this bound, not assume it. -/
theorem arc_mono {a p x y : ℝ} (hp : |p| ≤ a) (hxy : x ≤ y) :
    arc a p x ≤ arc a p y := by
  have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hs : |Real.sin y-Real.sin x| ≤ y-x := by
    simpa only [abs_of_nonneg hd] using Real.abs_sin_sub_sin_le y x
  have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg p)
  have ha := mul_le_mul_of_nonneg_right hp hd
  have hb : |p*(Real.sin y-Real.sin x)| ≤ a*(y-x) := by
    rw [abs_mul]
    exact hm.trans ha
  have hn := (neg_le_abs (p*(Real.sin y-Real.sin x))).trans hb
  unfold arc
  nlinarith only [hn]

/-- The lower-only version needs the actual small-angle domain. -/
theorem arc_unit_mono {a p x y : ℝ}
    (ha : 0 ≤ a) (hp : -a ≤ p) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    arc a p x ≤ arc a p y := by
  by_cases hp0 : 0 ≤ p
  · have hs : Real.sin x ≤ Real.sin y :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three]) hxy
    exact add_le_add (mul_le_mul_of_nonneg_left hxy ha)
      (mul_le_mul_of_nonneg_left hs hp0)
  · have hpn : p ≤ 0 := (lt_of_not_ge hp0).le
    have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
    have hs : Real.sin y-Real.sin x ≤ y-x := by
      calc
        _ ≤ |Real.sin y-Real.sin x| := le_abs_self _
        _ ≤ |y-x| := Real.abs_sin_sub_sin_le y x
        _ = y-x := abs_of_nonneg hd
    have hm := mul_le_mul_of_nonpos_left hs hpn
    have hc := mul_nonneg (by linarith : 0 ≤ a+p) hd
    unfold arc
    nlinarith only [hm,hc]

theorem sin_triple_factor (x : ℝ) :
    Real.sin (3*x) = Real.sin x*(4*(Real.cos x)^2-1) := by
  rw [Real.sin_three_mul]
  have hh := congrArg (fun z : ℝ => Real.sin x*z) (Real.sin_sq_add_cos_sq x)
  nlinarith only [hh]

def amplitude (W : TrigDensity) (z v : ℝ) : ℝ :=
  W.a1*v+W.a2*z*P2 v+W.a3*(4*z^2-1)*P3 v/3

theorem scalar_group (W : TrigDensity) (t v : ℝ) :
    W.a0*t+W.a1*Real.sin t*v+W.a2*Real.sin (2*t)*P2 v/2+
      W.a3*Real.sin (3*t)*P3 v/3 =
        arc W.a0 (amplitude W (Real.cos t) v) t := by
  rw [Real.sin_two_mul,sin_triple_factor]
  unfold arc amplitude
  ring

theorem actual_outer_group (W : TrigDensity) (c : Point) :
    c450Outer W c =
      arc W.a0 (amplitude W (Real.cos (outerT c)) (outerV c)) (outerT c) := by
  simpa only [c450Outer,outerT,outerV,zOf,P2,P3] using
    scalar_group W (outerT c) (outerV c)

theorem actual_inner_group (W : TrigDensity) (c : Point) (e : ℝ) :
    c450Inner W c e =
      arc W.a0 (amplitude W (Real.cos (c450B c e)) (c450Cq c e)) (c450B c e) := by
  simpa only [c450Inner,P2,P3] using scalar_group W (c450B c e) (c450Cq c e)

def innerCos (c : Point) (e : ℝ) : ℝ :=
  min 1 (‖c-hubPt e‖/(2*(19/50:ℝ)))

/-- Includes empty and tangent inner arcs. This is an actual definition
identity, not an assumed equation for a selected source configuration. -/
theorem actual_cos_beta (c : Point) (e : ℝ) :
    Real.cos (c450B c e) = innerCos c e := by
  unfold c450B innerCos hubPt
  split_ifs with hactive
  · have hp : (0:ℝ) < 2*(19/50) := by norm_num
    have hz0 : 0 ≤ ‖c-(!₂[e,0]:Point)‖/(2*(19/50:ℝ)) := by positivity
    have hz1 : ‖c-(!₂[e,0]:Point)‖/(2*(19/50:ℝ)) ≤ 1 :=
      (div_le_one hp).mpr hactive.le
    rw [Real.cos_arccos (by linarith : -1 ≤ ‖c-(!₂[e,0]:Point)‖/(2*(19/50:ℝ))) hz1,
      min_eq_right hz1]
  · have hz1 : (1:ℝ) ≤ ‖c-(!₂[e,0]:Point)‖/(2*(19/50:ℝ)) := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2*(19/50))]
      simpa only [one_mul] using (le_of_not_gt hactive)
    rw [Real.cos_zero,min_eq_left hz1]

/-- Actual physical pair consumer. All amplitude and width certificate
inputs remain EXPLICIT until the future real geometric packet pays them. -/
theorem actual_pair_bound (W0 W1 : TrigDensity) (c : Point) (e p0 p1 qt qb : ℝ)
    (hc0 : 1-19/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ 1+19/50)
    (ha0 : amplitude W0 (Real.cos (outerT c)) (outerV c) ≤ p0)
    (ha1 : amplitude W1 (Real.cos (c450B c e)) (c450Cq c e) ≤ p1)
    (hp0 : |p0| ≤ W0.a0) (hp1 : |p1| ≤ W1.a0)
    (ht : outerT c ≤ qt) (hb : c450B c e ≤ qb) :
    c450Outer W0 c+c450Inner W1 c e ≤ arc W0.a0 p0 qt+arc W1.a0 p1 qb := by
  have hwidth := outer_t_bounds hc0 hc1
  have hs0 : 0 ≤ Real.sin (outerT c) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨hwidth.1,by linarith [Real.pi_gt_three]⟩
  have hs1 : 0 ≤ Real.sin (c450B c e) := by
    apply Real.sin_nonneg_of_mem_Icc
    refine ⟨C450RadialMajorant.beta_nonneg c e,?_⟩
    unfold c450B
    split_ifs
    · exact Real.arccos_le_pi _
    · exact Real.pi_pos.le
  have h0 : arc W0.a0 (amplitude W0 (Real.cos (outerT c)) (outerV c)) (outerT c) ≤
      arc W0.a0 p0 (outerT c) := by
    unfold arc
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ha0 hs0)
  have h1 : arc W1.a0 (amplitude W1 (Real.cos (c450B c e)) (c450Cq c e)) (c450B c e) ≤
      arc W1.a0 p1 (c450B c e) := by
    unfold arc
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ha1 hs1)
  rw [actual_outer_group,actual_inner_group]
  exact add_le_add (h0.trans (arc_mono hp0 ht)) (h1.trans (arc_mono hp1 hb))

def sineProductUpper (p t : ℚ) : ℚ :=
  p*(if 0 ≤ p then sinHiNLag t else sinLoNLag t)

theorem sine_product_upper (p t : ℚ) :
    (p:ℝ)*Real.sin (t:ℝ) ≤ (sineProductUpper p t:ℝ) := by
  by_cases hp : 0 ≤ p
  · simp only [sineProductUpper,if_pos hp,Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left (sin_le_sinHiNLag t)
      ((Rat.cast_nonneg (K := ℝ)).mpr hp)
  · simp only [sineProductUpper,if_neg hp,Rat.cast_mul]
    have hn : (p:ℝ) ≤ 0 := by
      exact_mod_cast (lt_of_not_ge hp).le
    exact mul_le_mul_of_nonpos_left (sinLoNLag_le_sin t) hn

end N11Formalization.C450GroupedAnalytic
#check @N11Formalization.C450GroupedAnalytic.arc_mono
#check @N11Formalization.C450GroupedAnalytic.actual_outer_group
#check @N11Formalization.C450GroupedAnalytic.actual_inner_group
#check @N11Formalization.C450GroupedAnalytic.actual_cos_beta
#check @N11Formalization.C450GroupedAnalytic.actual_pair_bound
#print axioms N11Formalization.C450GroupedAnalytic.arc_mono
#print axioms N11Formalization.C450GroupedAnalytic.arc_unit_mono
#print axioms N11Formalization.C450GroupedAnalytic.actual_outer_group
#print axioms N11Formalization.C450GroupedAnalytic.actual_inner_group
#print axioms N11Formalization.C450GroupedAnalytic.actual_cos_beta
#print axioms N11Formalization.C450GroupedAnalytic.sine_product_upper
#print axioms N11Formalization.C450GroupedAnalytic.actual_pair_bound
