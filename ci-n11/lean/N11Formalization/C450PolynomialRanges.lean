import N11Formalization.C450GroupedAnalytic

/-! Real closed Chebyshev ranges. Critical points are included as actual
real interval facts, not inferred from samples or endpoint-only scans. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450PolynomialRanges
open C450OuterGeometry C450QuadraticBounds

def lower2 (lo hi : ℝ) : ℝ := P2 (vertex lo hi 0)
def upper2 (lo hi : ℝ) : ℝ := max (P2 lo) (P2 hi)

theorem range2 {lo hi x : ℝ} (hx0 : lo ≤ x) (hx1 : x ≤ hi) :
    P2 x ∈ Set.Icc (lower2 lo hi) (upper2 lo hi) := by
  have hlow := minimum_le (B := (0:ℝ)) (C := (0:ℝ)) hx0 hx1
  have hlo : quad 0 0 lo ≤ (upper2 lo hi+1)/2 := by
    have hh := le_max_left (P2 lo) (P2 hi)
    unfold P2 at hh
    unfold upper2 quad P2
    nlinarith only [hh]
  have hhi : quad 0 0 hi ≤ (upper2 lo hi+1)/2 := by
    have hh := le_max_right (P2 lo) (P2 hi)
    unfold P2 at hh
    unfold upper2 quad P2
    nlinarith only [hh]
  have hu := upper hx0 hx1 hlo hhi
  constructor
  · unfold minimum quad at hlow
    unfold lower2 P2
    nlinarith only [hlow]
  · unfold quad at hu
    unfold P2
    nlinarith only [hu]

theorem global3 {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    P3 x ∈ Set.Icc (-1:ℝ) 1 := by
  have hl := mul_nonneg (by linarith : 0 ≤ x+1) (sq_nonneg (2*x-1))
  have hu := mul_nonneg (by linarith : 0 ≤ 1-x) (sq_nonneg (2*x+1))
  constructor <;> unfold P3 <;> nlinarith only [hl,hu]

theorem odd3 (x : ℝ) : P3 (-x) = -P3 x := by
  unfold P3
  ring

theorem negative_mono3 {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ -1/2) :
    P3 x ≤ P3 y := by
  have hh := P3_le (q := -y) (v := -x) (by linarith) (by linarith)
  rw [odd3,odd3] at hh
  linarith only [hh]

theorem middle_anti3 {x y : ℝ}
    (hx : (-1:ℝ)/2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    P3 y ≤ P3 x := by
  have hx2 : x^2 ≤ (1:ℝ)/4 := by nlinarith
  have hy2 : y^2 ≤ (1:ℝ)/4 := by nlinarith
  have hprod : x*y ≤ (1:ℝ)/4 := by nlinarith [sq_nonneg (x-y)]
  have hf : 0 ≤ 3-4*(y^2+y*x+x^2) := by nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hxy) hf
  unfold P3
  nlinarith only [hh]

/-- Every endpoint AND every contained turning point is certified. -/
theorem range3_of_checks {lo hi x L U : ℝ}
    (hlo : -1 ≤ lo) (hhi : hi ≤ 1) (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (hLlo : L ≤ P3 lo) (hLhi : L ≤ P3 hi)
    (hUlo : P3 lo ≤ U) (hUhi : P3 hi ≤ U)
    (hcritL : lo ≤ 1/2 → 1/2 ≤ hi → L ≤ -1)
    (hcritU : lo ≤ -1/2 → -1/2 ≤ hi → 1 ≤ U) :
    P3 x ∈ Set.Icc L U := by
  have hg := global3 (hlo.trans hx0) (hx1.trans hhi)
  constructor
  · by_cases hxneg : x ≤ -1/2
    · exact hLlo.trans (negative_mono3 hx0 hxneg)
    · have hxmid : (-1:ℝ)/2 ≤ x := (lt_of_not_ge hxneg).le
      by_cases hxpos : (1:ℝ)/2 ≤ x
      · by_cases hlpos : (1:ℝ)/2 ≤ lo
        · exact hLlo.trans (P3_le hlpos hx0)
        · exact (hcritL (by linarith) (by linarith)).trans hg.1
      · have hxhalf : x ≤ (1:ℝ)/2 := (lt_of_not_ge hxpos).le
        by_cases hhmid : hi ≤ (1:ℝ)/2
        · exact hLhi.trans (middle_anti3 hxmid hx1 hhmid)
        · exact (hcritL (by linarith) (by linarith)).trans hg.1
  · by_cases hxpos : (1:ℝ)/2 ≤ x
    · exact (P3_le hxpos hx1).trans hUhi
    · have hxmid : x ≤ (1:ℝ)/2 := (lt_of_not_ge hxpos).le
      by_cases hxneg : x ≤ (-1:ℝ)/2
      · by_cases hhneg : hi ≤ (-1:ℝ)/2
        · exact (negative_mono3 hx1 hhneg).trans hUhi
        · exact hg.2.trans (hcritU (by linarith) (by linarith))
      · have hxhalf : (-1:ℝ)/2 ≤ x := (lt_of_not_ge hxneg).le
        by_cases hlmid : (-1:ℝ)/2 ≤ lo
        · exact (middle_anti3 hlmid hx0 hxmid).trans hUlo
        · exact hg.2.trans (hcritU (by linarith) (by linarith))

def lower3 (lo hi : ℝ) : ℝ :=
  if lo ≤ 1/2 ∧ 1/2 ≤ hi then -1 else min (P3 lo) (P3 hi)
def upper3 (lo hi : ℝ) : ℝ :=
  if lo ≤ -1/2 ∧ -1/2 ≤ hi then 1 else max (P3 lo) (P3 hi)

theorem range3 {lo hi x : ℝ} (hlo : -1 ≤ lo) (hhi : hi ≤ 1)
    (hx0 : lo ≤ x) (hx1 : x ≤ hi) :
    P3 x ∈ Set.Icc (lower3 lo hi) (upper3 lo hi) := by
  have hord := hx0.trans hx1
  have hgl := global3 hlo (hord.trans hhi)
  have hgh := global3 (hlo.trans hord) hhi
  apply range3_of_checks hlo hhi hx0 hx1
  · unfold lower3
    split_ifs
    · exact hgl.1
    · exact min_le_left _ _
  · unfold lower3
    split_ifs
    · exact hgh.1
    · exact min_le_right _ _
  · unfold upper3
    split_ifs
    · exact hgl.2
    · exact le_max_left _ _
  · unfold upper3
    split_ifs
    · exact hgh.2
    · exact le_max_right _ _
  · intro h0 h1
    simp only [lower3,if_pos (And.intro h0 h1),le_refl]
  · intro h0 h1
    simp only [upper3,if_pos (And.intro h0 h1),le_refl]

end N11Formalization.C450PolynomialRanges
#check @N11Formalization.C450PolynomialRanges.range2
#check @N11Formalization.C450PolynomialRanges.range3
#print axioms N11Formalization.C450PolynomialRanges.range2
#print axioms N11Formalization.C450PolynomialRanges.global3
#print axioms N11Formalization.C450PolynomialRanges.middle_anti3
#print axioms N11Formalization.C450PolynomialRanges.range3_of_checks
#print axioms N11Formalization.C450PolynomialRanges.range3
