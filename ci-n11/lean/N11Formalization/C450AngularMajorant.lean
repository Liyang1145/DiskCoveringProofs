import N11Formalization.C450RadialMajorant

/-! Direction-aware majorants for a nonpositive first inner harmonic.
The three continuous radial inequalities remain explicit until certified. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450AngularMajorant
open C450RadialMajorant C450NormalizedInterface

def tailSup (W : TrigDensity) : ℝ := W.a0+|W.a2|+|W.a3|
def angularModel (A M F r : ℝ) : ℝ :=
  A*Real.arccos (zOf r)+M*betaUpper r F
def AngularRadialBound (A B M F : ℝ) : Prop :=
  ∀ r : ℝ, 31/50 ≤ r → r ≤ 69/50 →
    angularModel A M F r < Real.pi*(A+B)/10

theorem cq_bounds {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖) :
    -1 ≤ c450Cq c e ∧ c450Cq c e ≤ 1 := by
  have hp := ell_pos_canonical he0 he7 hc0
  have hcoord := abs_coord_le_norm (c-(!₂[e,0]:Point))
  simp only [PiLp.sub_apply,Matrix.cons_val_zero] at hcoord
  unfold c450Cq
  constructor
  · rw [le_div_iff₀ hp]
    linarith [neg_le_abs (c 0-e)]
  · rw [div_le_one hp]
    exact (le_abs_self _).trans hcoord

theorem norm_coupling (c : Point) (e : ℝ) :
    ‖c‖^2 = ‖c-(!₂[e,0]:Point)‖^2+
      2*e*‖c-(!₂[e,0]:Point)‖*c450Cq c e+e^2 := by
  have hc := norm_sq_coord c
  have hd := norm_sq_coord (c-(!₂[e,0]:Point))
  simp only [PiLp.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one,sub_zero] at hd
  by_cases hz : ‖c-(!₂[e,0]:Point)‖ = 0
  · have hzero : c-(!₂[e,0]:Point) = 0 := norm_eq_zero.mp hz
    have hce : c = (!₂[e,0]:Point) := sub_eq_zero.mp hzero
    rw [hce]
    simp [c450Cq]
    simpa using norm_sq_coord (!₂[e,0]:Point)
  · unfold c450Cq
    field_simp
    nlinarith [hc,hd]

/-- Actual direction controls the inner distance. The small quadratic slack
is proved here; it is not an extra geometry assumption on ring centres. -/
theorem ell_lower {c : Point} {e E q : ℝ}
    (he0 : 0 ≤ e) (heE : e ≤ E) (hE : E ≤ 3/25)
    (hc0 : 1-19/50 ≤ ‖c‖) (hq0 : 0 ≤ q) (hcq : c450Cq c e ≤ q) :
    ‖c‖-(E*q+E^2) ≤ ‖c-(!₂[e,0]:Point)‖ := by
  have hEn : 0 ≤ E := he0.trans heE
  have hd : ‖c‖-e ≤ ‖c-(!₂[e,0]:Point)‖ := by
    have hh := (le_abs_self (‖c‖-‖(!₂[e,0]:Point)‖)).trans
      (abs_norm_sub_norm_le c (!₂[e,0]:Point))
    rwa [norm_pair_zero he0] at hh
  have hell : (1:ℝ)/2 ≤ ‖c-(!₂[e,0]:Point)‖ := by linarith
  have hprod : e*c450Cq c e ≤ E*q :=
    (mul_le_mul_of_nonneg_left hcq he0).trans
      (mul_le_mul_of_nonneg_right heE hq0)
  have hterm := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 2*‖c-(!₂[e,0]:Point)‖)
  have he2 : e^2 ≤ E^2 := by nlinarith
  have hsq : ‖c‖^2 ≤ ‖c-(!₂[e,0]:Point)‖^2+
      2*‖c-(!₂[e,0]:Point)‖*E*q+E^2 := by
    nlinarith [norm_coupling c e]
  have hslack := mul_le_mul_of_nonneg_right hell (sq_nonneg E)
  have hdelta : 0 ≤ E*q+E^2 := by positivity
  have hs : ‖c‖^2 ≤ (‖c-(!₂[e,0]:Point)‖+(E*q+E^2))^2 := by
    nlinarith [sq_nonneg (E*q+E^2)]
  nlinarith [norm_nonneg c,norm_nonneg (c-(!₂[e,0]:Point))]

theorem beta_le_angular {c : Point} {e E q : ℝ}
    (he0 : 0 ≤ e) (heE : e ≤ E) (hE : E ≤ 3/25)
    (hc0 : 1-19/50 ≤ ‖c‖) (hq0 : 0 ≤ q) (hcq : c450Cq c e ≤ q) :
    c450B c e ≤ betaUpper ‖c‖ (E*q+E^2) := by
  have hd := ell_lower he0 heE hE hc0 hq0 hcq
  unfold c450B betaUpper
  split_ifs
  · exact Real.arccos_le_arccos
      (div_le_div_of_nonneg_right hd (by norm_num))
  · exact Real.arccos_nonneg _

theorem beta_le_one {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (heE : e ≤ 3/25) (hc0 : 1-19/50 ≤ ‖c‖) :
    c450B c e ≤ 1 := by
  have hd : ‖c‖-e ≤ ‖c-(!₂[e,0]:Point)‖ := by
    have hh := (le_abs_self (‖c‖-‖(!₂[e,0]:Point)‖)).trans
      (abs_norm_sub_norm_le c (!₂[e,0]:Point))
    rwa [norm_pair_zero he0] at hh
  have hl : (1:ℝ)/2 ≤ ‖c-(!₂[e,0]:Point)‖ := by linarith
  unfold c450B
  split_ifs with hb
  · have hdom : ‖c-(!₂[e,0]:Point)‖/(2*(19/50:ℝ)) ∈ Set.Icc (-1) 1 := by
      constructor
      · have hh : 0 ≤ ‖c-(!₂[e,0]:Point)‖/(2*(19/50:ℝ)) := by positivity
        linarith
      · rw [div_le_one (by norm_num : (0:ℝ) < 2*(19/50))]
        exact hb.le
    have hcos := Real.cos_arccos hdom.1 hdom.2
    have hrat : cosHiNLag 1 ≤ (25/38:ℚ) := by decide +kernel
    have hreal : ((cosHiNLag 1:ℚ):ℝ) ≤ (25/38:ℝ) := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hrat
      norm_num at hh
      exact hh
    have hbound : ((cosHiNLag 1:ℚ):ℝ) ≤ ‖c-(!₂[e,0]:Point)‖/(2*(19/50:ℝ)) := by
      apply hreal.trans
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2*(19/50))]
      linarith
    simpa using le_of_cos_eq_bracket (q := 1) (by norm_num)
      (Real.arccos_le_pi _) hcos hbound
  · norm_num

theorem sin_lower {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (4/5:ℝ)*b ≤ Real.sin b := by
  have hb := Real.sin_bound (x := b) (by rwa [abs_of_nonneg hb0])
  rw [abs_of_nonneg hb0] at hb
  have h2 : b^2 ≤ 1 := by nlinarith
  have h3 : b^3 ≤ b := by nlinarith [mul_nonneg hb0 (by linarith : 0 ≤ 1-b^2)]
  have h4 : b^4 ≤ 1 := by nlinarith [sq_nonneg (b^2)]
  have h5 : b^5 ≤ b := by nlinarith [mul_nonneg hb0 (by linarith : 0 ≤ 1-b^4)]
  linarith [(abs_le.mp hb).1]

theorem inner_le_tail (W : TrigDensity) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖) :
    c450Inner W c e ≤ tailSup W*c450B c e+
      W.a1*Real.sin (c450B c e)*c450Cq c e := by
  have hp := ell_pos_canonical he0 he7 hc0
  obtain ⟨phi,hcos,_⟩ := exists_angle_of_point (c-(!₂[e,0]:Point)) (norm_pos_iff.mp hp)
  have hg : Real.cos phi = c450Cq c e := by
    rw [hcos,c450Cq]
    simp
  have hb := beta_nonneg c e
  have h2 := harmonic_le W.a2 2 (c450B c e) phi (by norm_num) hb
  have h3 := harmonic_le W.a3 3 (c450B c e) phi (by norm_num) hb
  have hc2 := cos_two_mul_of_cos hg
  have hc3 := cos_three_mul_of_cos hg
  unfold c450Inner tailSup
  rw [← hc2,← hc3]
  nlinarith [h2,h3]

theorem tail_nonneg (W : TrigDensity) : 0 ≤ tailSup W := by
  unfold tailSup
  linarith [W.hnonneg,abs_nonneg W.a1,abs_nonneg W.a2,abs_nonneg W.a3]

theorem neg_coefficient_nonneg (W : TrigDensity) : 0 ≤ tailSup W-W.a1 := by
  unfold tailSup
  linarith [W.hnonneg,le_abs_self W.a1,abs_nonneg W.a2,abs_nonneg W.a3]

theorem pos_coefficient_nonneg (W : TrigDensity) (ha : W.a1 ≤ 0) :
    0 ≤ tailSup W+(2/5)*W.a1 := by
  have habs : |W.a1| = -W.a1 := abs_of_nonpos ha
  have hh := W.hnonneg
  rw [habs] at hh
  unfold tailSup
  linarith [abs_nonneg W.a2,abs_nonneg W.a3]

theorem inner_neg (W : TrigDensity) (ha : W.a1 ≤ 0) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖) :
    c450Inner W c e ≤ (tailSup W-W.a1)*c450B c e := by
  have ht := inner_le_tail W he0 he7 hc0
  have hb := beta_nonneg c e
  have hq := cq_bounds he0 he7 hc0
  have hsin0 : 0 ≤ Real.sin (c450B c e) := by
    apply Real.sin_nonneg_of_mem_Icc
    refine ⟨hb,?_⟩
    unfold c450B
    split_ifs
    · exact Real.arccos_le_pi _
    · exact Real.pi_pos.le
  have hs : Real.sin (c450B c e) ≤ c450B c e := by
    have hh := Real.abs_sin_le_abs (x := c450B c e)
    rw [abs_of_nonneg hb] at hh
    exact (le_abs_self _).trans hh
  have hm := mul_le_mul_of_nonneg_left hq.1 hsin0
  have hm2 := mul_le_mul_of_nonpos_left hm ha
  nlinarith

theorem inner_mid (W : TrigDensity) (ha : W.a1 ≤ 0) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖)
    (hq0 : 0 ≤ c450Cq c e) :
    c450Inner W c e ≤ tailSup W*c450B c e := by
  have ht := inner_le_tail W he0 he7 hc0
  have hs : 0 ≤ Real.sin (c450B c e) := by
    apply Real.sin_nonneg_of_mem_Icc
    refine ⟨beta_nonneg c e,?_⟩
    unfold c450B
    split_ifs
    · exact Real.arccos_le_pi _
    · exact Real.pi_pos.le
  have hh := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ha hs) hq0
  linarith

theorem inner_pos (W : TrigDensity) (ha : W.a1 ≤ 0) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (heE : e ≤ 3/25) (hc0 : 1-19/50 ≤ ‖c‖)
    (hq : (1:ℝ)/2 ≤ c450Cq c e) :
    c450Inner W c e ≤ (tailSup W+(2/5)*W.a1)*c450B c e := by
  have he7 : e ≤ 7/50 := by linarith
  have ht := inner_le_tail W he0 he7 hc0
  have hb := beta_nonneg c e
  have hlow := sin_lower hb (beta_le_one he0 heE hc0)
  have hsin0 : 0 ≤ Real.sin (c450B c e) := by linarith
  have hm := mul_le_mul_of_nonneg_left hq hsin0
  have hm2 := mul_le_mul_of_nonpos_left hm ha
  have hm3 := mul_le_mul_of_nonpos_left hlow ha
  nlinarith

/-- Direction is eliminated by a complete three-way split. Only three genuine
one-dimensional closed radial inequalities remain; no angle premise survives. -/
theorem normalized_of_three (W0 W1 : TrigDensity)
    (h01 : W0.a1 = 0) (h02 : W0.a2 = 0) (h03 : W0.a3 = 0)
    (h11 : W1.a1 ≤ 0) (e0 E : ℝ) (hE : E ≤ 3/25)
    (hn : AngularRadialBound W0.a0 W1.a0 (tailSup W1-W1.a1) (E^2))
    (hm : AngularRadialBound W0.a0 W1.a0 (tailSup W1) (E/2+E^2))
    (hp : AngularRadialBound W0.a0 W1.a0 (tailSup W1+(2/5)*W1.a1) (E+E^2)) :
    PerDiskNormalized W0 W1 e0 E := by
  intro c e hc0 hc1 he0 _heLo heE
  have heSmall : e ≤ 3/25 := heE.trans hE
  have he7 : e ≤ 7/50 := by linarith
  have hr0 : (31:ℝ)/50 ≤ ‖c‖ := by linarith
  have hr1 : ‖c‖ ≤ (69:ℝ)/50 := by linarith
  have hb : c450Outer W0 c+c450Inner W1 c e <
      Real.pi*(W0.a0+W1.a0)/10 := by
    rw [outer_constant W0 h01 h02 h03]
    by_cases hq0 : c450Cq c e ≤ 0
    · have hi := inner_neg W1 h11 he0 he7 hc0
      have hbeta := beta_le_angular he0 heE hE hc0 (by norm_num : (0:ℝ) ≤ 0) hq0
      simp only [mul_zero,zero_add] at hbeta
      have hm' := mul_le_mul_of_nonneg_left hbeta (neg_coefficient_nonneg W1)
      exact (add_le_add le_rfl (hi.trans hm')).trans_lt (hn ‖c‖ hr0 hr1)
    · have hqpos : 0 ≤ c450Cq c e := (lt_of_not_ge hq0).le
      by_cases hqHalf : c450Cq c e ≤ 1/2
      · have hi := inner_mid W1 h11 he0 he7 hc0 hqpos
        have hbeta := beta_le_angular he0 heE hE hc0 (by norm_num : (0:ℝ) ≤ 1/2) hqHalf
        have hoff : E*(1/2) = E/2 := by ring
        rw [hoff] at hbeta
        have hm' := mul_le_mul_of_nonneg_left hbeta (tail_nonneg W1)
        exact (add_le_add le_rfl (hi.trans hm')).trans_lt (hm ‖c‖ hr0 hr1)
      · have hi := inner_pos W1 h11 he0 heSmall hc0 (lt_of_not_ge hqHalf).le
        have hq1 := (cq_bounds he0 he7 hc0).2
        have hbeta := beta_le_angular he0 heE hE hc0 (by norm_num : (0:ℝ) ≤ 1) hq1
        simp only [mul_one] at hbeta
        have hm' := mul_le_mul_of_nonneg_left hbeta (pos_coefficient_nonneg W1 h11)
        exact (add_le_add le_rfl (hi.trans hm')).trans_lt (hp ‖c‖ hr0 hr1)
  have hf : 2*c450Outer W0 c+2*c450Inner W1 c e <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
    nlinarith only [hb]
  exact (pair_canonical W0 W1 he0 he7 hc0 hc1).trans_lt hf
end N11Formalization.C450AngularMajorant
#check @N11Formalization.C450AngularMajorant.norm_coupling
#check @N11Formalization.C450AngularMajorant.normalized_of_three
#print axioms N11Formalization.C450AngularMajorant.ell_lower
#print axioms N11Formalization.C450AngularMajorant.normalized_of_three
