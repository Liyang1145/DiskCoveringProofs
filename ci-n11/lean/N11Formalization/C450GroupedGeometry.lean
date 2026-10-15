import N11Formalization.C450PolynomialRanges
import N11Formalization.Interval.Core

/-! Actual centre norm/direction geometry from real quadratic certificates.
Numeric packet data/validity stay EXPLICIT. No sampled optimizer is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450GroupedGeometry
open C450QuadraticBounds C450OuterGeometry C450AngularMajorant C450GroupedAnalytic

def ell (c : Point) (e : ℝ) : ℝ := ‖c-(!₂[e,0]:Point)‖

theorem ell_lower_global {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hr : (31:ℝ)/50 ≤ ‖c‖) :
    (12:ℝ)/25 ≤ ell c e := by
  have hh := (le_abs_self (‖c‖-‖(!₂[e,0]:Point)‖)).trans
    (abs_norm_sub_norm_le c (!₂[e,0]:Point))
  rw [norm_pair_zero he0] at hh
  unfold ell
  linarith

theorem coordinate_identity {c : Point} {e : ℝ} (hell : 0 < ell c e) :
    outerV c = (ell c e*c450Cq c e+e)/‖c‖ := by
  have hh : ell c e*c450Cq c e = c 0-e := by
    unfold ell c450Cq
    field_simp [show ‖c-(!₂[e,0]:Point)‖ ≠ 0 from hell.ne']
  rw [hh]
  unfold outerV
  congr 1
  ring

/-- The packet certifies the squared equation at real interval endpoints
and its clamped vertex. All implications refer to the ACTUAL centre. -/
theorem ell_bounds {c : Point} {e eLo E rLo rHi qLo qHi L U : ℝ}
    (hLo0 : 0 ≤ eLo) (heLo : eLo ≤ e) (heE : e ≤ E) (hE : E ≤ 7/50)
    (hrLo : (31:ℝ)/50 ≤ rLo) (hr0 : rLo ≤ ‖c‖) (hr1 : ‖c‖ ≤ rHi)
    (hq0 : qLo ≤ c450Cq c e) (hq1 : c450Cq c e ≤ qHi)
    (hL : E ≤ L) (hLU : L ≤ U)
    (hnumL0 : quad (L*qHi) (L^2) eLo ≤ rLo^2)
    (hnumL1 : quad (L*qHi) (L^2) E ≤ rLo^2)
    (hnumU : rHi^2 ≤ minimum eLo E (U*qLo) (U^2)) :
    ell c e ∈ Set.Icc L U := by
  have he0 : 0 ≤ e := hLo0.trans heLo
  have he7 : e ≤ 7/50 := heE.trans hE
  have hEn : 0 ≤ E := he0.trans heE
  have hLn : 0 ≤ L := hEn.trans hL
  have hUn : 0 ≤ U := hLn.trans hLU
  have hr : (31:ℝ)/50 ≤ ‖c‖ := hrLo.trans hr0
  have hd := ell_lower_global he0 he7 hr
  have hq := cq_bounds he0 he7 (by linarith : 1-19/50 ≤ ‖c‖)
  have hcouple := norm_coupling c e
  change ‖c‖^2 = (ell c e)^2+2*e*ell c e*c450Cq c e+e^2 at hcouple
  have hR0 : rLo^2 ≤ ‖c‖^2 := by nlinarith
  have hR1 : ‖c‖^2 ≤ rHi^2 := by nlinarith [norm_nonneg c]
  have hlowerNum := upper heLo heE hnumL0 hnumL1
  have hupperNum := lower heLo heE hnumU
  unfold quad at hlowerNum hupperNum
  have htermL := mul_le_mul_of_nonneg_left hq1
    (by positivity : 0 ≤ 2*e*L)
  have htermU := mul_le_mul_of_nonneg_left hq0
    (by positivity : 0 ≤ 2*e*U)
  have hFL : L^2+2*e*L*c450Cq c e+e^2 ≤ ‖c‖^2 := by
    nlinarith only [hlowerNum,htermL,hR0]
  have hFU : ‖c‖^2 ≤ U^2+2*e*U*c450Cq c e+e^2 := by
    nlinarith only [hupperNum,htermU,hR1]
  have hqprod := mul_le_mul_of_nonneg_left hq.1 (by positivity : 0 ≤ 2*e)
  have hfL : 0 < L+ell c e+2*e*c450Cq c e := by linarith
  have hfU : 0 < U+ell c e+2*e*c450Cq c e := by linarith
  constructor
  · by_contra hn
    have hh : ell c e < L := lt_of_not_ge hn
    have hp := mul_pos (sub_pos.mpr hh) hfL
    nlinarith only [hp,hFL,hcouple]
  · by_contra hn
    have hh : U < ell c e := lt_of_not_ge hn
    have hp := mul_pos (sub_pos.mpr hh) hfU
    nlinarith only [hp,hFU,hcouple]

theorem z_bounds {c : Point} {rLo rHi ZLo ZHi : ℝ}
    (hrLo : (31:ℝ)/50 ≤ rLo) (hr0 : rLo ≤ ‖c‖) (hr1 : ‖c‖ ≤ rHi)
    (hnumLo : 0 ≤ minimum rLo rHi (-ZLo) (1-(19/50:ℝ)^2))
    (hnumHi0 : quad (-ZHi) (1-(19/50:ℝ)^2) rLo ≤ 0)
    (hnumHi1 : quad (-ZHi) (1-(19/50:ℝ)^2) rHi ≤ 0) :
    zOf ‖c‖ ∈ Set.Icc ZLo ZHi := by
  have hp : 0 < 2*‖c‖ := by linarith
  have hlo := lower hr0 hr1 hnumLo
  have hhi := upper hr0 hr1 hnumHi0 hnumHi1
  unfold quad at hlo hhi
  unfold zOf
  constructor
  · rw [le_div_iff₀ hp]
    nlinarith only [hlo]
  · rw [div_le_iff₀ hp]
    nlinarith only [hhi]

theorem cosine_beta_bounds {c : Point} {e L U : ℝ}
    (hlo : L ≤ ell c e) (hhi : ell c e ≤ U) :
    Real.cos (c450B c e) ∈ Set.Icc
      (min 1 (L/(2*(19/50:ℝ)))) (min 1 (U/(2*(19/50:ℝ)))) := by
  rw [actual_cos_beta]
  unfold innerCos hubPt
  change min 1 (ell c e/(2*(19/50:ℝ))) ∈
    Set.Icc (min 1 (L/(2*(19/50:ℝ)))) (min 1 (U/(2*(19/50:ℝ))))
  constructor
  · exact min_le_min le_rfl
      (div_le_div_of_nonneg_right hlo (by norm_num : (0:ℝ) ≤ 2*(19/50)))
  · exact min_le_min le_rfl
      (div_le_div_of_nonneg_right hhi (by norm_num : (0:ℝ) ≤ 2*(19/50)))

def directionInterval (IL IQ IE IR : RatInterval)
    (hden : IR.hi < 0 ∨ 0 < IR.lo) : RatInterval :=
  ((IL.mul IQ).add IE).div IR hden

theorem direction_interval {c : Point} {e : ℝ} (IL IQ IE IR : RatInterval)
    (hden : IR.hi < 0 ∨ 0 < IR.lo) (hpos : 0 < ell c e)
    (hL : RatInterval.Mem IL (ell c e))
    (hQ : RatInterval.Mem IQ (c450Cq c e))
    (hE : RatInterval.Mem IE e) (hR : RatInterval.Mem IR ‖c‖) :
    RatInterval.Mem (directionInterval IL IQ IE IR hden) (outerV c) := by
  have hn := RatInterval.add_mem (RatInterval.mul_mem hL hQ) hE
  have hd := RatInterval.div_mem hn hR hden
  rw [← coordinate_identity hpos] at hd
  exact hd

def clipUnit (I : RatInterval) : RatInterval :=
  ⟨max (-1) I.lo,min 1 I.hi⟩

theorem clipped_direction {c : Point} (I : RatInterval)
    (hr : (31:ℝ)/50 ≤ ‖c‖) (hI : RatInterval.Mem I (outerV c)) :
    RatInterval.Mem (clipUnit I) (outerV c) := by
  have hg := outer_v_bounds (by linarith : 1-19/50 ≤ ‖c‖)
  change ((max (-1:ℚ) I.lo:ℚ):ℝ) ≤ outerV c ∧
    outerV c ≤ ((min (1:ℚ) I.hi:ℚ):ℝ)
  simp only [Rat.cast_max,Rat.cast_min,Rat.cast_neg,Rat.cast_one]
  exact ⟨max_le hg.1 (RatInterval.mem_lo_le hI),
    le_min hg.2 (RatInterval.mem_le_hi hI)⟩

theorem outer_width_le {c : Point} (qt : ℚ) {ZLo : ℝ}
    (hc0 : (31:ℝ)/50 ≤ ‖c‖) (hc1 : ‖c‖ ≤ (69:ℝ)/50)
    (hqt : 0 ≤ qt) (hz : ZLo ≤ zOf ‖c‖) (hcos : (cosHiNLag qt:ℝ) ≤ ZLo) :
    outerT c ≤ (qt:ℝ) := by
  have hd := C450FirstRadialKernel.z_mem hc0 hc1
  exact le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hqt)
    (Real.arccos_le_pi _) (Real.cos_arccos hd.1 hd.2) (hcos.trans hz)

theorem inner_width_le (c : Point) (e : ℝ) (qb : ℚ) {CBLo : ℝ}
    (hqb : 0 ≤ qb) (hc : CBLo ≤ Real.cos (c450B c e))
    (hcos : (cosHiNLag qb:ℝ) ≤ CBLo) :
    c450B c e ≤ (qb:ℝ) := by
  have hb : c450B c e ≤ Real.pi := by
    unfold c450B
    split_ifs
    · exact Real.arccos_le_pi _
    · exact Real.pi_pos.le
  exact le_of_cos_eq_bracket ((Rat.cast_nonneg (K := ℝ)).mpr hqb) hb rfl
    (hcos.trans hc)

end N11Formalization.C450GroupedGeometry
#check @N11Formalization.C450GroupedGeometry.ell_bounds
#check @N11Formalization.C450GroupedGeometry.z_bounds
#check @N11Formalization.C450GroupedGeometry.cosine_beta_bounds
#check @N11Formalization.C450GroupedGeometry.direction_interval
#check @N11Formalization.C450GroupedGeometry.outer_width_le
#check @N11Formalization.C450GroupedGeometry.inner_width_le
#print axioms N11Formalization.C450GroupedGeometry.ell_lower_global
#print axioms N11Formalization.C450GroupedGeometry.coordinate_identity
#print axioms N11Formalization.C450GroupedGeometry.ell_bounds
#print axioms N11Formalization.C450GroupedGeometry.z_bounds
#print axioms N11Formalization.C450GroupedGeometry.cosine_beta_bounds
#print axioms N11Formalization.C450GroupedGeometry.direction_interval
#print axioms N11Formalization.C450GroupedGeometry.clipped_direction
#print axioms N11Formalization.C450GroupedGeometry.outer_width_le
#print axioms N11Formalization.C450GroupedGeometry.inner_width_le
