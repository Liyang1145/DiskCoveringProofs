import N11Formalization.ActualSectorAreaEnvelope

/-! Global real Lipschitz bounds for the correct skew-sector envelopes.
The max kink and angles just beyond pi are retained. These bounds justify
grid error margins; no sampled value is asserted to be a global maximum. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricAreaEnvelopeRegularity

open ActualSectorAreaEnvelope ActualCircleSegmentAlgebra

theorem arcsin_box_difference {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (19/50)) (hy : y ∈ Set.Icc (0 : ℝ) (19/50)) :
    |Real.arcsin x-Real.arcsin y| ≤ 2*|x-y| := by
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) (19/50),
      HasDerivWithinAt Real.arcsin (1/Real.sqrt (1-t^2)) (Set.Icc (0 : ℝ) (19/50)) t := by
    intro t ht
    exact (Real.hasDerivAt_arcsin (by linarith [ht.1] : t ≠ -1)
      (by linarith [ht.2] : t ≠ 1)).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) (19/50), ‖(1 : ℝ)/Real.sqrt (1-t^2)‖ ≤ 2 := by
    intro t ht
    have hrad : 0 ≤ 1-t^2 := by nlinarith [ht.1,ht.2]
    have hs : (1/2 : ℝ) ≤ Real.sqrt (1-t^2) :=
      (Real.le_sqrt (by norm_num) hrad).mpr (by nlinarith [ht.1,ht.2])
    have hs0 : 0 < Real.sqrt (1-t^2) := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by norm_num) hs0.le)]
    exact (div_le_iff₀ hs0).mpr (by linarith)
  have hm := (convex_Icc (0 : ℝ) (19/50)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hf hb hy hx
  simpa only [Real.norm_eq_abs] using hm

theorem widthEnvelope_difference (a b : ℝ) :
    |widthEnvelope a-widthEnvelope b| ≤ (19/25 : ℝ)*|a-b| := by
  let A := max (1/2 : ℝ) (Real.sin (a/2))
  let B := max (1/2 : ℝ) (Real.sin (b/2))
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1/2) (le_max_left _ _)
  have hB0 : 0 ≤ B := le_trans (by norm_num : (0 : ℝ) ≤ 1/2) (le_max_left _ _)
  have hA1 : A ≤ 1 := max_le (by norm_num) (Real.sin_le_one _)
  have hB1 : B ≤ 1 := max_le (by norm_num) (Real.sin_le_one _)
  have hx : (19/50 : ℝ)*A ∈ Set.Icc (0 : ℝ) (19/50) := by constructor <;> nlinarith
  have hy : (19/50 : ℝ)*B ∈ Set.Icc (0 : ℝ) (19/50) := by constructor <;> nlinarith
  have hi := arcsin_box_difference hx hy
  have hm : |A-B| ≤ |Real.sin (a/2)-Real.sin (b/2)| := by
    simpa only [A,B,max_comm] using
      abs_max_sub_max_le_abs (Real.sin (a/2)) (Real.sin (b/2)) (1/2 : ℝ)
  have hs := Real.abs_sin_sub_sin_le (a/2) (b/2)
  have hhalf : |a/2-b/2| = |a-b|/2 := by
    rw [← sub_div,abs_div]
    norm_num
  have harg : |(19/50 : ℝ)*A-(19/50 : ℝ)*B| = (19/50 : ℝ)*|A-B| := by
    rw [← mul_sub,abs_mul]
    norm_num
  have hwidth : |widthEnvelope a-widthEnvelope b| =
      2*|Real.arcsin ((19/50 : ℝ)*A)-Real.arcsin ((19/50 : ℝ)*B)| := by
    unfold widthEnvelope
    change |2*Real.arcsin ((19/50 : ℝ)*A)-2*Real.arcsin ((19/50 : ℝ)*B)| = _
    rw [← mul_sub,abs_mul]
    norm_num
  rw [harg] at hi
  rw [hhalf] at hs
  rw [hwidth]
  nlinarith only [hi,hm,hs]

theorem segmentTerm_difference (a b : ℝ) :
    |segmentTerm a-segmentTerm b| ≤ |a-b| := by
  have he : segmentTerm a-segmentTerm b = ((a-b)-(Real.sin a-Real.sin b))/2 := by
    unfold segmentTerm
    ring
  have ht : |(a-b)-(Real.sin a-Real.sin b)| ≤ |a-b|+|Real.sin a-Real.sin b| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le (a-b) 0 (Real.sin a-Real.sin b)
  have hs := Real.abs_sin_sub_sin_le a b
  rw [he,abs_div]
  norm_num
  linarith

theorem areaEnvelope_difference (a b : ℝ) :
    |areaEnvelope a-areaEnvelope b| ≤ |a-b| := by
  have he : areaEnvelope a-areaEnvelope b =
      ((19/50 : ℝ)^2/2)*(Real.sin a-Real.sin b) +
        (segmentTerm (widthEnvelope a)-segmentTerm (widthEnvelope b)) := by
    unfold areaEnvelope
    ring
  have ht := abs_add_le (((19/50 : ℝ)^2/2)*(Real.sin a-Real.sin b))
    (segmentTerm (widthEnvelope a)-segmentTerm (widthEnvelope b))
  have hm := segmentTerm_difference (widthEnvelope a) (widthEnvelope b)
  have hw := widthEnvelope_difference a b
  have hs := Real.abs_sin_sub_sin_le a b
  have hc : |((19/50 : ℝ)^2/2)*(Real.sin a-Real.sin b)| =
      ((19/50 : ℝ)^2/2)*|Real.sin a-Real.sin b| := by
    rw [abs_mul]
    norm_num
  rw [hc] at ht
  rw [he]
  nlinarith only [ht,hm,hw,hs,abs_nonneg (a-b)]

theorem widthEnvelope_one_lipschitz (a b : ℝ) :
    |widthEnvelope a-widthEnvelope b| ≤ |a-b| := by
  have h := widthEnvelope_difference a b
  nlinarith only [h,abs_nonneg (a-b)]

end N11Formalization.MetricAreaEnvelopeRegularity
#check @N11Formalization.MetricAreaEnvelopeRegularity.widthEnvelope_one_lipschitz
#check @N11Formalization.MetricAreaEnvelopeRegularity.areaEnvelope_difference
#print axioms N11Formalization.MetricAreaEnvelopeRegularity.arcsin_box_difference
#print axioms N11Formalization.MetricAreaEnvelopeRegularity.widthEnvelope_one_lipschitz
#print axioms N11Formalization.MetricAreaEnvelopeRegularity.areaEnvelope_difference
