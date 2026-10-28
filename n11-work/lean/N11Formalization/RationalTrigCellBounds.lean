import N11Formalization.RationalBoxSubdivision
import N11Formalization.SharedMomentFactorRationalNodes

/-! Pure rational enclosures for trigonometric functions on complete closed
cells. Midpoint Taylor bounds and the global Lipschitz bound cover every real
point, including closed boundaries; clipping retains the natural range. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.RationalTrigCellBounds

def midpoint (I : RatInterval) : ℚ := (I.lo+I.hi)/2
def halfWidth (I : RatInterval) : ℚ := (I.hi-I.lo)/2

def sinCell (I : RatInterval) : RatInterval :=
  ⟨max (-1) (sinLoNLag (midpoint I)-halfWidth I),
   min 1 (sinHiNLag (midpoint I)+halfWidth I)⟩
def cosCell (I : RatInterval) : RatInterval :=
  ⟨max (-1) (cosLoNLag (midpoint I)-halfWidth I),
   min 1 (cosHiNLag (midpoint I)+halfWidth I)⟩

theorem distance_le_halfWidth {I : RatInterval} {x : ℝ} (hx : I.Mem x) :
    |x-(midpoint I : ℝ)| ≤ (halfWidth I : ℝ) := by
  unfold midpoint halfWidth
  push_cast
  exact abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩

theorem sinCell_mem {I : RatInterval} {x : ℝ} (hx : I.Mem x) :
    (sinCell I).Mem (Real.sin x) := by
  have hd := (Real.abs_sin_sub_sin_le x (midpoint I)).trans (distance_le_halfWidth hx)
  have hlo := sinLoNLag_le_sin (midpoint I)
  have hhi := sin_le_sinHiNLag (midpoint I)
  have hh := abs_le.mp hd
  change ((max (-1) (sinLoNLag (midpoint I)-halfWidth I) : ℚ) : ℝ) ≤ Real.sin x ∧
    Real.sin x ≤ ((min 1 (sinHiNLag (midpoint I)+halfWidth I) : ℚ) : ℝ)
  push_cast
  exact ⟨max_le (Real.neg_one_le_sin x) (by linarith only [hlo,hh.1]),
    le_min (Real.sin_le_one x) (by linarith only [hhi,hh.2])⟩

theorem cosCell_mem {I : RatInterval} {x : ℝ} (hx : I.Mem x) :
    (cosCell I).Mem (Real.cos x) := by
  have hd := (Real.abs_cos_sub_cos_le x (midpoint I)).trans (distance_le_halfWidth hx)
  have hlo := cosLoNLag_le_cos (midpoint I)
  have hhi := cos_le_cosHiNLag (midpoint I)
  have hh := abs_le.mp hd
  change ((max (-1) (cosLoNLag (midpoint I)-halfWidth I) : ℚ) : ℝ) ≤ Real.cos x ∧
    Real.cos x ≤ ((min 1 (cosHiNLag (midpoint I)+halfWidth I) : ℚ) : ℝ)
  push_cast
  exact ⟨max_le (Real.neg_one_le_cos x) (by linarith only [hlo,hh.1]),
    le_min (Real.cos_le_one x) (by linarith only [hhi,hh.2])⟩

/-- Squaring preserves dependency of the two factors. In a cell crossing zero,
the lower endpoint is exactly zero, rather than a negative cross product. -/
def squareCell (I : RatInterval) : RatInterval :=
  if 0 ≤ I.lo then ⟨I.lo^2,I.hi^2⟩
  else if I.hi ≤ 0 then ⟨I.hi^2,I.lo^2⟩
  else ⟨0,max (I.lo^2) (I.hi^2)⟩

theorem squareCell_mem {I : RatInterval} {x : ℝ} (hx : I.Mem x) :
    (squareCell I).Mem (x^2) := by
  by_cases hlo : 0 ≤ I.lo
  · simp only [squareCell,if_pos hlo]
    change ((I.lo^2 : ℚ) : ℝ) ≤ x^2 ∧ x^2 ≤ ((I.hi^2 : ℚ) : ℝ)
    push_cast
    have hl : (0 : ℝ) ≤ I.lo := by exact_mod_cast hlo
    have hxx : 0 ≤ x := hl.trans hx.1
    have hr : (0 : ℝ) ≤ I.hi := hxx.trans hx.2
    exact ⟨(sq_le_sq₀ hl hxx).mpr hx.1,(sq_le_sq₀ hxx hr).mpr hx.2⟩
  · by_cases hhi : I.hi ≤ 0
    · simp only [squareCell,if_neg hlo,if_pos hhi]
      change ((I.hi^2 : ℚ) : ℝ) ≤ x^2 ∧ x^2 ≤ ((I.lo^2 : ℚ) : ℝ)
      push_cast
      have hr : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
      have hxx : x ≤ 0 := hx.2.trans hr
      have hl : (I.lo : ℝ) ≤ 0 := hx.1.trans hxx
      have ha := (sq_le_sq₀ (neg_nonneg.mpr hr) (neg_nonneg.mpr hxx)).mpr (neg_le_neg hx.2)
      have hb := (sq_le_sq₀ (neg_nonneg.mpr hxx) (neg_nonneg.mpr hl)).mpr (neg_le_neg hx.1)
      simpa only [neg_sq] using And.intro ha hb
    · simp only [squareCell,if_neg hlo,if_neg hhi]
      change ((0 : ℚ) : ℝ) ≤ x^2 ∧ x^2 ≤ ((max (I.lo^2) (I.hi^2) : ℚ) : ℝ)
      push_cast
      refine ⟨sq_nonneg x,?_⟩
      by_cases hxx : 0 ≤ x
      · exact ((sq_le_sq₀ hxx (hxx.trans hx.2)).mpr hx.2).trans (le_max_right _ _)
      · have hneg : x ≤ 0 := (lt_of_not_ge hxx).le
        have hh := (sq_le_sq₀ (neg_nonneg.mpr hneg)
          (neg_nonneg.mpr (hx.1.trans hneg))).mpr (neg_le_neg hx.1)
        have hl : x^2 ≤ (I.lo : ℝ)^2 := by simpa only [neg_sq] using hh
        exact hl.trans (le_max_left _ _)

theorem sinCell_valid {I : RatInterval} (hI : I.Valid) : (sinCell I).Valid := by
  have hm : I.Mem (midpoint I) := by
    change (I.lo : ℝ) ≤ ((I.lo+I.hi)/2 : ℚ) ∧ ((I.lo+I.hi)/2 : ℚ) ≤ (I.hi : ℝ)
    push_cast
    constructor <;> linarith only [hI.lo_le_hi]
  exact RatInterval.valid_of_mem (sinCell_mem hm)

theorem cosCell_valid {I : RatInterval} (hI : I.Valid) : (cosCell I).Valid := by
  have hm : I.Mem (midpoint I) := by
    change (I.lo : ℝ) ≤ ((I.lo+I.hi)/2 : ℚ) ∧ ((I.lo+I.hi)/2 : ℚ) ≤ (I.hi : ℝ)
    push_cast
    constructor <;> linarith only [hI.lo_le_hi]
  exact RatInterval.valid_of_mem (cosCell_mem hm)

theorem squareCell_valid {I : RatInterval} (hI : I.Valid) : (squareCell I).Valid :=
  RatInterval.valid_of_mem (squareCell_mem
    (show I.Mem (I.lo : ℝ) from ⟨le_rfl,hI.lo_le_hi⟩))

#print axioms distance_le_halfWidth
#print axioms sinCell_mem
#print axioms cosCell_mem
#print axioms squareCell_mem
#print axioms sinCell_valid
#print axioms cosCell_valid
#print axioms squareCell_valid
end N11Formalization.RationalTrigCellBounds
