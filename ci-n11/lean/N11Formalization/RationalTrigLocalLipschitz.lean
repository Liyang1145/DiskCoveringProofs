import N11Formalization.RationalTrigCellBounds

/-! Local mean-value bounds on complete rational closed intervals. The
derivative enclosure can keep signed cancellation before taking its absolute
bound. Endpoints and degenerate intervals require no extra hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.RationalTrigLocalLipschitz
open RationalTrigCellBounds

def absBoundQ (I : RatInterval) : ℚ := max |I.lo| |I.hi|

theorem absBoundQ_nonneg (I : RatInterval) : 0 ≤ absBoundQ I :=
  (abs_nonneg I.lo).trans (le_max_left _ _)

theorem abs_of_mem {I : RatInterval} {x : ℝ} (hx : I.Mem x) :
    |x| ≤ (absBoundQ I : ℝ) := by
  unfold absBoundQ
  push_cast
  apply abs_le.mpr
  constructor
  · have hl := (neg_abs_le (I.lo : ℝ)).trans hx.1
    have hm := neg_le_neg (le_max_left |(I.lo : ℝ)| |(I.hi : ℝ)|)
    exact hm.trans hl
  · exact hx.2.trans ((le_abs_self _).trans (le_max_right _ _))

/-- A whole-interval derivative certificate gives a difference bound even
when the derivative changes sign or vanishes inside the interval. -/
theorem image_sub_le_of_derivative_mem {I J : RatInterval} {f f' : ℝ → ℝ}
    (hf : ∀ t, I.Mem t → HasDerivAt f (f' t) t)
    (hbound : ∀ t, I.Mem t → J.Mem (f' t))
    {x y : ℝ} (hx : I.Mem x) (hy : I.Mem y) :
    |f y-f x| ≤ (absBoundQ J : ℝ)*|y-x| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := Set.Icc (I.lo : ℝ) (I.hi : ℝ))
    (C := (absBoundQ J : ℝ))
    (fun t ht => (hf t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using abs_of_mem (hbound t ht))
    (convex_Icc _ _) hx hy
  simpa only [Real.norm_eq_abs] using hh

theorem sin_sub_le_local {I : RatInterval} {x y : ℝ}
    (hx : I.Mem x) (hy : I.Mem y) :
    |Real.sin y-Real.sin x| ≤ (absBoundQ (cosCell I) : ℝ)*|y-x| := by
  exact image_sub_le_of_derivative_mem
    (fun t _ => Real.hasDerivAt_sin t) (fun _ ht => cosCell_mem ht) hx hy

theorem cos_sub_le_local {I : RatInterval} {x y : ℝ}
    (hx : I.Mem x) (hy : I.Mem y) :
    |Real.cos y-Real.cos x| ≤ (absBoundQ (sinCell I) : ℝ)*|y-x| := by
  have hh := image_sub_le_of_derivative_mem
    (J := (sinCell I).neg) (fun t _ => Real.hasDerivAt_cos t)
    (fun _ ht => RatInterval.neg_mem (sinCell_mem ht)) hx hy
  have he : absBoundQ (sinCell I).neg=absBoundQ (sinCell I) := by
    unfold absBoundQ RatInterval.neg
    simp only [abs_neg]
    exact max_comm _ _
  simpa only [he] using hh

theorem sin_mul_cos_mem {I : RatInterval} {x : ℝ} (hx : I.Mem x) :
    ((sinCell I).mul (cosCell I)).Mem (Real.sin x*Real.cos x) :=
  RatInterval.mul_mem (sinCell_mem hx) (cosCell_mem hx)

theorem sine_square_sub_le_local {I : RatInterval} {x y : ℝ}
    (hx : I.Mem x) (hy : I.Mem y) :
    |Real.sin y^2-Real.sin x^2| ≤
      (absBoundQ ((RatInterval.ofRat 2).mul ((sinCell I).mul (cosCell I))) : ℝ)*|y-x| := by
  apply image_sub_le_of_derivative_mem
    (I := I) (J := (RatInterval.ofRat 2).mul ((sinCell I).mul (cosCell I)))
    (f := fun t => Real.sin t^2) (f' := fun t => 2*Real.sin t*Real.cos t)
  · intro t _
    simpa using (Real.hasDerivAt_sin t).fun_pow 2
  · intro t ht
    convert RatInterval.mul_mem (RatInterval.ofRat_mem 2) (sin_mul_cos_mem ht) using 1
      <;> norm_num <;> ring
  · exact hx
  · exact hy

end N11Formalization.RationalTrigLocalLipschitz
#print axioms N11Formalization.RationalTrigLocalLipschitz.absBoundQ_nonneg
#print axioms N11Formalization.RationalTrigLocalLipschitz.abs_of_mem
#print axioms N11Formalization.RationalTrigLocalLipschitz.image_sub_le_of_derivative_mem
#print axioms N11Formalization.RationalTrigLocalLipschitz.sin_sub_le_local
#print axioms N11Formalization.RationalTrigLocalLipschitz.cos_sub_le_local
#print axioms N11Formalization.RationalTrigLocalLipschitz.sin_mul_cos_mem
#print axioms N11Formalization.RationalTrigLocalLipschitz.sine_square_sub_le_local
