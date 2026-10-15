import N11Formalization.C450SourceQuantity
import N11Formalization.DSHTenBoundaryEval

/-! Genuine radial/density majorant for constant outer density.
No sampled maximum or optimizer result is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450RadialMajorant
open C450NormalizedInterface
open scoped Interval
open MeasureTheory

def densitySup (W : TrigDensity) : ℝ := W.a0+|W.a1|+|W.a2|+|W.a3|
def betaUpper (r E : ℝ) : ℝ := Real.arccos ((r-E)/(2*(19/50:ℝ)))
def majorant (W0 W1 : TrigDensity) (E r : ℝ) : ℝ :=
  W0.a0*Real.arccos (zOf r)+densitySup W1*betaUpper r E

theorem densitySup_nonneg (W : TrigDensity) : 0 ≤ densitySup W := by
  unfold densitySup
  linarith [W.hnonneg,abs_nonneg W.a1,abs_nonneg W.a2,abs_nonneg W.a3]

theorem harmonic_le (a k b phi : ℝ) (hk : 0 < k) (hb : 0 ≤ b) :
    a*Real.sin (k*b)*Real.cos (k*phi)/k ≤ |a| * b := by
  have hs := Real.abs_sin_le_abs (x := k*b)
  rw [abs_of_nonneg (mul_nonneg hk.le hb)] at hs
  have hm : a*Real.sin (k*b)*Real.cos (k*phi) ≤ |a| * (k*b) := by
    calc
      _ ≤ |a*Real.sin (k*b)*Real.cos (k*phi)| := le_abs_self _
      _ = |a| * |Real.sin (k*b)| * |Real.cos (k*phi)| := by rw [abs_mul,abs_mul]
      _ ≤ |a| * |Real.sin (k*b)| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (x := k*phi)) (by positivity)
      _ ≤ |a| * (k*b) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  rw [div_le_iff₀ hk]
  nlinarith only [hm]

theorem beta_nonneg (c : Point) (e : ℝ) : 0 ≤ c450B c e := by
  unfold c450B
  split_ifs
  · exact Real.arccos_nonneg _
  · norm_num

theorem inner_le_density (W : TrigDensity) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7/50) (hc0 : 1-19/50 ≤ ‖c‖) :
    c450Inner W c e ≤ densitySup W*c450B c e := by
  have hp := ell_pos_canonical he0 he7 hc0
  have hw : c-(!₂[e,0]:Point) ≠ 0 := norm_pos_iff.mp hp
  obtain ⟨phi,hcos,_⟩ := exists_angle_of_point (c-(!₂[e,0]:Point)) hw
  have hg : Real.cos phi = c450Cq c e := by
    rw [hcos,c450Cq]
    simp
  let b := c450B c e
  have hb : 0 ≤ b := beta_nonneg c e
  have h1 := harmonic_le W.a1 1 b phi (by norm_num) hb
  have h2 := harmonic_le W.a2 2 b phi (by norm_num) hb
  have h3 := harmonic_le W.a3 3 b phi (by norm_num) hb
  norm_num at h1
  have hc2 := cos_two_mul_of_cos hg
  have hc3 := cos_three_mul_of_cos hg
  change W.a0*b+W.a1*Real.sin b*c450Cq c e+
    W.a2*Real.sin (2*b)*(2*(c450Cq c e)^2-1)/2+
    W.a3*Real.sin (3*b)*(4*(c450Cq c e)^3-3*c450Cq c e)/3 ≤ densitySup W*b
  rw [← hc2,← hc3,← hg]
  unfold densitySup
  nlinarith [h1,h2,h3]

theorem beta_le_upper {c : Point} {e E : ℝ} (he0 : 0 ≤ e) (heE : e ≤ E) :
    c450B c e ≤ betaUpper ‖c‖ E := by
  have hd : ‖c‖-e ≤ ‖c-(!₂[e,0]:Point)‖ := by
    have ht := (le_abs_self (‖c‖-‖(!₂[e,0]:Point)‖)).trans
      (abs_norm_sub_norm_le c (!₂[e,0]:Point))
    rw [norm_pair_zero he0] at ht
    exact ht
  unfold c450B betaUpper
  split_ifs
  · apply Real.arccos_le_arccos
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith
  · exact Real.arccos_nonneg _

theorem outer_constant (W : TrigDensity) (h1 : W.a1 = 0)
    (h2 : W.a2 = 0) (h3 : W.a3 = 0) (c : Point) :
    c450Outer W c = W.a0*Real.arccos (zOf ‖c‖) := by
  simp [c450Outer,zOf,h1,h2,h3]

theorem pair_le_majorant (W0 W1 : TrigDensity)
    (h1 : W0.a1 = 0) (h2 : W0.a2 = 0) (h3 : W0.a3 = 0)
    {c : Point} {e E : ℝ} (he0 : 0 ≤ e) (he7 : e ≤ 7/50)
    (heE : e ≤ E) (hc0 : 1-19/50 ≤ ‖c‖) :
    c450Outer W0 c+c450Inner W1 c e ≤ majorant W0 W1 E ‖c‖ := by
  have hi := inner_le_density W1 he0 he7 hc0
  have hb := mul_le_mul_of_nonneg_left (beta_le_upper (c := c) he0 heE) (densitySup_nonneg W1)
  unfold majorant
  rw [outer_constant W0 h1 h2 h3]
  exact add_le_add le_rfl (hi.trans hb)

/-- The real closed radial continuum remains explicit until a finite exact
partition is certified. It is not supplied by host samples. -/
def RadialBound (W0 W1 : TrigDensity) (E : ℝ) : Prop :=
  ∀ r : ℝ, 1-19/50 ≤ r → r ≤ 1+19/50 →
    majorant W0 W1 E r < Real.pi*(W0.a0+W1.a0)/10

theorem normalized_of_radial (W0 W1 : TrigDensity)
    (h1 : W0.a1 = 0) (h2 : W0.a2 = 0) (h3 : W0.a3 = 0)
    (e0 E : ℝ) (hE : E ≤ 7/50) (hb : RadialBound W0 W1 E) :
    PerDiskNormalized W0 W1 e0 E := by
  intro c e hc0 hc1 he0 _heLo heE
  have hbound := (pair_le_majorant W0 W1 h1 h2 h3 he0 (heE.trans hE) heE hc0).trans_lt
    (hb ‖c‖ hc0 hc1)
  have hp := pair_canonical W0 W1 he0 (heE.trans hE) hc0 hc1
  have hh := mul_lt_mul_of_pos_left hbound (by norm_num : (0:ℝ) < 2)
  change 2*(c450Outer W0 c+c450Inner W1 c e) <
    2*(Real.pi*(W0.a0+W1.a0)/10) at hh
  have hfinal : 2*c450Outer W0 c+2*c450Inner W1 c e <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10 := by
    convert hh using 1 <;> ring
  exact hp.trans_lt hfinal
end N11Formalization.C450RadialMajorant
#check @N11Formalization.C450RadialMajorant.inner_le_density
#check @N11Formalization.C450RadialMajorant.normalized_of_radial
#print axioms N11Formalization.C450RadialMajorant.inner_le_density
#print axioms N11Formalization.C450RadialMajorant.normalized_of_radial
