import N11Formalization.C450AngularMajorant

/-! Retain the actual lower hub offset on negative directions.
Four genuine radial continuum bounds remain explicit until concrete payment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SignedAngularMajorant
open C450AngularMajorant C450RadialMajorant C450NormalizedInterface

theorem ell_lower_signed {c : Point} {e eLo E q : ℝ}
    (hLo0 : 0 ≤ eLo) (heLo : eLo ≤ e) (heE : e ≤ E) (hE : E ≤ 3/25)
    (hc0 : 1-19/50 ≤ ‖c‖) (hqLo : -1 ≤ q) (hq0 : q ≤ 0)
    (hcq : c450Cq c e ≤ q) :
    ‖c‖-(eLo*q+E^2) ≤ ‖c-(!₂[e,0]:Point)‖ := by
  have he0 : 0 ≤ e := hLo0.trans heLo
  have hEn : 0 ≤ E := he0.trans heE
  have hLoE : eLo ≤ E := heLo.trans heE
  have hd : ‖c‖-e ≤ ‖c-(!₂[e,0]:Point)‖ := by
    have hh := (le_abs_self (‖c‖-‖(!₂[e,0]:Point)‖)).trans
      (abs_norm_sub_norm_le c (!₂[e,0]:Point))
    rwa [norm_pair_zero he0] at hh
  have hell : (1:ℝ)/2 ≤ ‖c-(!₂[e,0]:Point)‖ := by linarith
  have hprod : e*c450Cq c e ≤ eLo*q :=
    (mul_le_mul_of_nonneg_left hcq he0).trans
      (mul_le_mul_of_nonpos_right heLo hq0)
  have hterm := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 2*‖c-(!₂[e,0]:Point)‖)
  have he2 : e^2 ≤ E^2 := by nlinarith
  have hsq : ‖c‖^2 ≤ ‖c-(!₂[e,0]:Point)‖^2+
      2*‖c-(!₂[e,0]:Point)‖*eLo*q+E^2 := by
    nlinarith [norm_coupling c e]
  have hslack := mul_le_mul_of_nonneg_right hell (sq_nonneg E)
  have hqprod := mul_le_mul_of_nonneg_left hqLo hLo0
  have hsum : 0 ≤ ‖c-(!₂[e,0]:Point)‖+(eLo*q+E^2) := by
    nlinarith [sq_nonneg E]
  have hs : ‖c‖^2 ≤ (‖c-(!₂[e,0]:Point)‖+(eLo*q+E^2))^2 := by
    nlinarith [sq_nonneg (eLo*q+E^2)]
  nlinarith [norm_nonneg c]

theorem beta_le_signed {c : Point} {e eLo E q : ℝ}
    (hLo0 : 0 ≤ eLo) (heLo : eLo ≤ e) (heE : e ≤ E) (hE : E ≤ 3/25)
    (hc0 : 1-19/50 ≤ ‖c‖) (hqLo : -1 ≤ q) (hq0 : q ≤ 0)
    (hcq : c450Cq c e ≤ q) :
    c450B c e ≤ betaUpper ‖c‖ (eLo*q+E^2) := by
  have hd := ell_lower_signed hLo0 heLo heE hE hc0 hqLo hq0 hcq
  unfold c450B betaUpper
  split_ifs
  · exact Real.arccos_le_arccos
      (div_le_div_of_nonneg_right hd (by norm_num))
  · exact Real.arccos_nonneg _

theorem neg_cell_coefficient_nonneg (W : TrigDensity) (ha : W.a1 ≤ 0)
    {qLo : ℝ} (hq0 : qLo ≤ 0) :
    0 ≤ tailSup W+W.a1*qLo :=
  add_nonneg (tail_nonneg W) (mul_nonneg_of_nonpos_of_nonpos ha hq0)

theorem inner_neg_cell (W : TrigDensity) (ha : W.a1 ≤ 0) {c : Point} {e qLo : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖)
    (hqLo : qLo ≤ 0) (hcq : qLo ≤ c450Cq c e) :
    c450Inner W c e ≤ (tailSup W+W.a1*qLo)*c450B c e := by
  have ht := inner_le_tail W he0 he7 hc0
  have hb := beta_nonneg c e
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
  have hm := mul_le_mul_of_nonneg_left hcq hsin0
  have hm2 := mul_le_mul_of_nonpos_left hm ha
  have hcoeff : 0 ≤ W.a1*qLo := mul_nonneg_of_nonpos_of_nonpos ha hqLo
  have hm3 := mul_le_mul_of_nonneg_left hs hcoeff
  nlinarith

/-- The lower e endpoint is genuine segment data. No direction premise remains
on the normalized per-disk bound after the exhaustive four-way split. -/
theorem normalized_of_four (W0 W1 : TrigDensity)
    (h01 : W0.a1 = 0) (h02 : W0.a2 = 0) (h03 : W0.a3 = 0)
    (h11 : W1.a1 ≤ 0) (eLo E : ℝ) (hLo0 : 0 ≤ eLo) (hE : E ≤ 3/25)
    (hn1 : AngularRadialBound W0.a0 W1.a0 (tailSup W1-W1.a1) (-eLo/2+E^2))
    (hn2 : AngularRadialBound W0.a0 W1.a0 (tailSup W1-W1.a1/2) (E^2))
    (hm : AngularRadialBound W0.a0 W1.a0 (tailSup W1) (E/2+E^2))
    (hp : AngularRadialBound W0.a0 W1.a0 (tailSup W1+(2/5)*W1.a1) (E+E^2)) :
    PerDiskNormalized W0 W1 eLo E := by
  intro c e hc0 hc1 he0 heLo heE
  have heSmall : e ≤ 3/25 := heE.trans hE
  have he7 : e ≤ 7/50 := by linarith
  have hr0 : (31:ℝ)/50 ≤ ‖c‖ := by linarith
  have hr1 : ‖c‖ ≤ (69:ℝ)/50 := by linarith
  have hqBounds := cq_bounds he0 he7 hc0
  have hb : c450Outer W0 c+c450Inner W1 c e <
      Real.pi*(W0.a0+W1.a0)/10 := by
    rw [outer_constant W0 h01 h02 h03]
    by_cases hqNegHalf : c450Cq c e ≤ -1/2
    · have hi := inner_neg W1 h11 he0 he7 hc0
      have hbeta := beta_le_signed hLo0 heLo heE hE hc0
        (by norm_num : (-1:ℝ) ≤ -1/2) (by norm_num : (-1:ℝ)/2 ≤ 0) hqNegHalf
      have hoff : eLo*(-1/2)+E^2 = -eLo/2+E^2 := by ring
      rw [hoff] at hbeta
      have hm' := mul_le_mul_of_nonneg_left hbeta (neg_coefficient_nonneg W1)
      exact (add_le_add le_rfl (hi.trans hm')).trans_lt (hn1 ‖c‖ hr0 hr1)
    · have hqNegHalfLo : (-1:ℝ)/2 ≤ c450Cq c e := (lt_of_not_ge hqNegHalf).le
      by_cases hq0 : c450Cq c e ≤ 0
      · have hi := inner_neg_cell W1 h11 he0 he7 hc0
          (by norm_num : (-1:ℝ)/2 ≤ 0) hqNegHalfLo
        have hcoef : tailSup W1+W1.a1*(-1/2) = tailSup W1-W1.a1/2 := by ring
        rw [hcoef] at hi
        have hbeta := beta_le_angular he0 heE hE hc0 (by norm_num : (0:ℝ) ≤ 0) hq0
        simp only [mul_zero,zero_add] at hbeta
        have hc : 0 ≤ tailSup W1-W1.a1/2 := by
          have hh := neg_cell_coefficient_nonneg W1 h11 (by norm_num : (-1:ℝ)/2 ≤ 0)
          rwa [hcoef] at hh
        have hm' := mul_le_mul_of_nonneg_left hbeta hc
        exact (add_le_add le_rfl (hi.trans hm')).trans_lt (hn2 ‖c‖ hr0 hr1)
      · have hqpos : 0 ≤ c450Cq c e := (lt_of_not_ge hq0).le
        by_cases hqHalf : c450Cq c e ≤ 1/2
        · have hi := inner_mid W1 h11 he0 he7 hc0 hqpos
          have hbeta := beta_le_angular he0 heE hE hc0 (by norm_num : (0:ℝ) ≤ 1/2) hqHalf
          have hoff : E*(1/2) = E/2 := by ring
          rw [hoff] at hbeta
          have hm' := mul_le_mul_of_nonneg_left hbeta (tail_nonneg W1)
          exact (add_le_add le_rfl (hi.trans hm')).trans_lt (hm ‖c‖ hr0 hr1)
        · have hi := inner_pos W1 h11 he0 heSmall hc0 (lt_of_not_ge hqHalf).le
          have hbeta := beta_le_angular he0 heE hE hc0 (by norm_num : (0:ℝ) ≤ 1) hqBounds.2
          simp only [mul_one] at hbeta
          have hm' := mul_le_mul_of_nonneg_left hbeta (pos_coefficient_nonneg W1 h11)
          exact (add_le_add le_rfl (hi.trans hm')).trans_lt (hp ‖c‖ hr0 hr1)
  have hf : 2*c450Outer W0 c+2*c450Inner W1 c e <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
    nlinarith only [hb]
  exact (pair_canonical W0 W1 he0 he7 hc0 hc1).trans_lt hf
end N11Formalization.C450SignedAngularMajorant
#check @N11Formalization.C450SignedAngularMajorant.ell_lower_signed
#check @N11Formalization.C450SignedAngularMajorant.normalized_of_four
#print axioms N11Formalization.C450SignedAngularMajorant.ell_lower_signed
#print axioms N11Formalization.C450SignedAngularMajorant.inner_neg_cell
#print axioms N11Formalization.C450SignedAngularMajorant.normalized_of_four
