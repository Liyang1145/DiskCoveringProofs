import Mathlib

namespace N11Formalization.ResumeRelativeScalar

/-- Directional stress loss is quartic after completing the square. This
is a conditional scalar implication, not a certificate for geometric constants. -/
theorem directional_completion (E q p μ C d K t : ℝ) (ht : 0 ≤ t)
    (h : μ / 2 * q^2 + t*p^2 - C*q^3 - (d/3)*q^4 - (2*t)*K*p*q^2 ≤ E) :
    (μ/2 - C*q - (d/3 + t*K^2)*q^2)*q^2 ≤ E := by
  have hs : 0 ≤ t * (p - K*q^2)^2 := mul_nonneg ht (sq_nonneg _)
  nlinarith

/-- C920 constants, exactly as rationals in RELATIVE-STRESS-BASIS.md.
These constants are hypotheses of the geometric bound, not inferred here. -/
noncomputable def coefficient (q : ℝ) : ℝ :=
  9/10000 - (179/5000)*q -
    ((2/25)/3 + 734*((99/200)*(2/25) + 429/50000)^2)*q^2

theorem coefficient_antitone_on_nonneg {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) :
    coefficient r ≤ coefficient q := by
  have hsq : q^2 ≤ r^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hqr) (show 0 ≤ r + q by linarith)]
  unfold coefficient
  norm_num
  nlinarith

theorem coefficient_at_radius : (1 : ℝ)/100000 < coefficient (729/50000) := by
  norm_num [coefficient]

theorem coefficient_gt {q : ℝ} (hq : 0 ≤ q) (hr : q ≤ 729/50000) :
    (1 : ℝ)/100000 < coefficient q :=
  lt_of_lt_of_le coefficient_at_radius (coefficient_antitone_on_nonneg hq hr)

/-- Consumer shape: if the actual C920 geometric derivation supplies its
scalar inequality, the whole CLOSED radius-.01458 ball has the target gain. -/
theorem local_gain {E q p : ℝ} (hq : 0 ≤ q) (hr : q ≤ 729/50000)
    (h : (9/10000 : ℝ)*q^2 + 734*p^2 - (179/5000)*q^3 - ((2/25)/3)*q^4
      - 1468*((99/200)*(2/25) + 429/50000)*p*q^2 ≤ E) :
    q^2/100000 ≤ E := by
  have hh := directional_completion E q p (9/5000) (179/5000) (2/25)
    ((99/200)*(2/25) + 429/50000) 734 (by norm_num) (by convert h using 1 <;> ring)
  have hc := coefficient_gt hq hr
  have hs := sq_nonneg q
  have hm : (1/100000 : ℝ)*q^2 ≤ coefficient q*q^2 :=
    mul_le_mul_of_nonneg_right hc.le hs
  have hcoef : (9/5000/2 : ℝ) = 9/10000 := by norm_num
  rw [hcoef] at hh
  change coefficient q*q^2 ≤ E at hh
  nlinarith

/-- Actual stress-positivity scalar gate on the closed source radius.
The bound p ≤ Gnorm*q still needs the bound for the actual source matrix. -/
theorem stress_gate {p q : ℝ} (hp : p ≤ (15363/1000000 : ℝ)*q)
    (hq : q ≤ 729/50000) : (1468 : ℝ)*(99/200)*p < 1 := by
  have h := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 15363/1000000 by norm_num)
  nlinarith

/-- Negative calibration: this particular scalar bound cannot support the
same gain after rounding the radius UP to .0146. Not a geometric disproof. -/
theorem rounded_radius_rejected : coefficient (73/5000) < (1 : ℝ)/100000 := by
  norm_num [coefficient]

#print axioms stress_gate
#print axioms rounded_radius_rejected
#print axioms directional_completion
#print axioms coefficient_at_radius
#print axioms local_gain
end N11Formalization.ResumeRelativeScalar
