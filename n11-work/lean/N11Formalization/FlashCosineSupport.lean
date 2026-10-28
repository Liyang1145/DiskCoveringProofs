/-
Analytic cosine minorants without critical-point enumeration.
Increasing-sine arc: rational approximate tangent + explicit slope error.
Decreasing-sine arc: both endpoint inequalities suffice.
These are continuum statements. Numerical proposed anchor points are not premises.
-/
import N11Formalization.FlashCosineCore
namespace N11Formalization.FlashCosineSupport
open Finset
set_option autoImplicit false

/-- Increasing derivative yields a supporting tangent on the entire interval. -/
theorem support_of_monotone_sin {a b t z : ℝ}
    (hm : MonotoneOn Real.sin (Set.Icc a b))
    (ht : t ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b) :
    Real.sin t * (z - t) ≤ Real.cos t - Real.cos z := by
  rcases le_total t z with htz | hzt
  · exact FlashCosine.le_cos_sub_cos_of_le_sin htz (by
      intro v hv
      exact hm ht ⟨le_trans ht.1 hv.1, le_trans hv.2 hz.2⟩ hv.1)
  · have h := FlashCosine.cos_sub_cos_le_of_sin_le hzt (by
      intro v hv
      exact hm ⟨le_trans hz.1 hv.1, le_trans hv.2 ht.2⟩ ht hv.2)
    linarith

/-- Approximate tangent: all rounding loss is retained explicitly in `e * (b-a)`. -/
theorem minorant_of_approx_support {a b t s c e H : ℝ}
    (hm : MonotoneOn Real.sin (Set.Icc a b))
    (ht : t ∈ Set.Icc a b) (he : 0 ≤ e)
    (hs : |Real.sin t - s| ≤ e) (hcos : Real.cos t ≤ H)
    (hc : c ≤ 1 - H - s * t - e * (b - a)) :
    ∀ z ∈ Set.Icc a b, s * z + c ≤ 1 - Real.cos z := by
  intro z hz
  have hd : |z - t| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2, ht.1, ht.2]
  have herr : |(Real.sin t - s) * (z - t)| ≤ e * (b - a) := by
    rw [abs_mul]
    exact mul_le_mul hs hd (abs_nonneg _) he
  have h := support_of_monotone_sin hm ht hz
  have hlow := (abs_le.mp herr).1
  nlinarith

/-- Decreasing derivative: a minimum is attained at an endpoint, even when the
function crosses a stationary maximum. No branch / inverse-sine assumptions. -/
theorem minorant_of_antitone_sin {a b s c : ℝ}
    (hm : AntitoneOn Real.sin (Set.Icc a b))
    (ha : c ≤ 1 - Real.cos a - s * a)
    (hb : c ≤ 1 - Real.cos b - s * b) :
    ∀ z ∈ Set.Icc a b, s * z + c ≤ 1 - Real.cos z := by
  intro z hz
  rcases le_total s (Real.sin z) with hs | hs
  · have h := FlashCosine.le_cos_sub_cos_of_le_sin hz.1 (by
      intro v hv
      exact le_trans hs (hm ⟨hv.1, le_trans hv.2 hz.2⟩ hz hv.2))
    linarith
  · have h := FlashCosine.cos_sub_cos_le_of_sin_le hz.2 (by
      intro v hv
      exact le_trans (hm hz ⟨le_trans hz.1 hv.1, hv.2⟩ hv.1) hs)
    linarith

/-- Integer shifts are part of the exact arc premises, not floating branch labels. -/
theorem monotone_sin_arc {a b : ℝ} {m : ℤ}
    (ha : -(Real.pi / 2) ≤ a - (m : ℝ) * (2 * Real.pi))
    (hb : b - (m : ℝ) * (2 * Real.pi) ≤ Real.pi / 2) :
    MonotoneOn Real.sin (Set.Icc a b) := by
  intro x hx z hz hxz
  exact FlashCosine.arc_inc_le_sin (m := m) (a := x) (b := b)
    (by linarith [hx.1]) hb ⟨hxz, hz.2⟩

theorem antitone_sin_arc {a b : ℝ} {m : ℤ}
    (ha : Real.pi / 2 ≤ a - (m : ℝ) * (2 * Real.pi))
    (hb : b - (m : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2) :
    AntitoneOn Real.sin (Set.Icc a b) := by
  intro x hx z hz hxz
  exact FlashCosine.sin_le_sin_of_mem_arc_dec (m := m) (a := x) (b := b)
    (by linarith [hx.1]) hb ⟨hxz, hz.2⟩

/-- Calibration: the tangent at zero on [-1,1] really proves nonnegative energy. -/
theorem known_zero_support : ∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ 1 - Real.cos z := by
  have hm := monotone_sin_arc (a := (-1 : ℝ)) (b := (1 : ℝ)) (m := 0)
    (by norm_num; linarith [Real.pi_gt_three])
    (by norm_num; linarith [Real.pi_gt_three])
  simpa using minorant_of_approx_support (t := 0) (s := 0) (c := 0) (e := 0) (H := 1)
    hm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end N11Formalization.FlashCosineSupport
#print N11Formalization.FlashCosineSupport.minorant_of_approx_support
#print N11Formalization.FlashCosineSupport.minorant_of_antitone_sin
#print axioms N11Formalization.FlashCosineSupport.minorant_of_approx_support
#print axioms N11Formalization.FlashCosineSupport.minorant_of_antitone_sin
#print axioms N11Formalization.FlashCosineSupport.known_zero_support
