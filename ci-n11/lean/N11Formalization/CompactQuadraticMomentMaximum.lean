import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact elimination of the shared normalized radius in a signed first/second
moment factor. The whole closed interval, including every coefficient boundary,
has a proved upper bound and an explicitly attained maximum. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CompactQuadraticMomentMaximum

def quad (A B y : ℝ) : ℝ := A*y^2+B*y

def maximum (A B : ℝ) : ℝ :=
  if A < 0 ∧ 0 < B ∧ B < -2*A then -B^2/(4*A) else max 0 (A+B)

/-- The interior vertex is used exactly when it lies strictly inside the interval. -/
theorem maximum_of_vertex {A B : ℝ} (h : A < 0 ∧ 0 < B ∧ B < -2*A) :
    maximum A B = -B^2/(4*A) := by
  simp only [maximum, if_pos h]

/-- All other cases, including the three coefficient boundaries, use an endpoint. -/
theorem maximum_of_endpoint {A B : ℝ} (h : ¬ (A < 0 ∧ 0 < B ∧ B < -2*A)) :
    maximum A B = max 0 (A+B) := by
  simp only [maximum, if_neg h]

theorem maximum_zero_first (B : ℝ) : maximum 0 B = max 0 B := by
  simp [maximum]

theorem maximum_zero_second (A : ℝ) : maximum A 0 = max 0 A := by
  simp [maximum]

theorem maximum_vertex_boundary (A : ℝ) : maximum A (-2*A) = max 0 (-A) := by
  simp only [maximum,lt_self_iff_false,and_false,if_false]
  congr 1
  ring

theorem quad_le_maximum {A B y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    quad A B y ≤ maximum A B := by
  unfold maximum
  split_ifs with h
  · unfold quad
    apply (le_div_iff_of_neg (by linarith [h.1] : 4*A < 0)).mpr
    nlinarith only [sq_nonneg (2*A*y+B)]
  · by_cases hA : 0 ≤ A
    · have hy2 : y^2 ≤ y := by nlinarith [hy.1,hy.2]
      have hquad : quad A B y ≤ (A+B)*y := by
        unfold quad
        nlinarith only [mul_le_mul_of_nonneg_left hy2 hA]
      have hsum : (A+B)*y ≤ max 0 (A+B)*y :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hy.1
      have hmax : max 0 (A+B)*y ≤ max 0 (A+B) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hy.2 (le_max_left (0 : ℝ) (A+B))
      exact hquad.trans (hsum.trans hmax)
    · have hAn : A < 0 := lt_of_not_ge hA
      by_cases hB : B ≤ 0
      · have hp : A*y^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAn.le (sq_nonneg y)
        have hq : B*y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hB hy.1
        exact (show quad A B y ≤ 0 by unfold quad; linarith only [hp,hq]).trans
          (le_max_left _ _)
      · have hBp : 0 < B := lt_of_not_ge hB
        have hAB : -2*A ≤ B := by
          by_contra hn
          exact h ⟨hAn,hBp,lt_of_not_ge hn⟩
        have hAy : A ≤ A*y := by
          simpa only [mul_one] using mul_le_mul_of_nonpos_left hy.2 hAn.le
        have hf : 0 ≤ A*(1+y)+B := by nlinarith only [hAy,hAB]
        have hp := mul_nonneg (sub_nonneg.mpr hy.2) hf
        have hend : quad A B y ≤ A+B := by
          unfold quad
          nlinarith only [hp]
        exact hend.trans (le_max_right _ _)

/-- A genuine closed-domain maximizer is constructed from the coefficients. -/
theorem maximum_attained (A B : ℝ) :
    ∃ y ∈ Set.Icc (0 : ℝ) 1, quad A B y = maximum A B := by
  unfold maximum
  split_ifs with h
  · have hA : A ≠ 0 := ne_of_lt h.1
    have hden : 2*A < 0 := by linarith [h.1]
    refine ⟨-B/(2*A), ⟨?_,?_⟩,?_⟩
    · exact div_nonneg_of_nonpos (by linarith [h.2.1]) hden.le
    · apply (div_le_iff_of_neg hden).mpr
      linarith [h.2.2]
    · unfold quad
      field_simp [hA]
      ring
  · by_cases hs : 0 ≤ A+B
    · refine ⟨1,⟨by norm_num,by norm_num⟩,?_⟩
      simp [quad,max_eq_right hs]
    · refine ⟨0,⟨by norm_num,by norm_num⟩,?_⟩
      simp [quad,max_eq_left (le_of_not_ge hs)]

theorem maximum_nonneg (A B : ℝ) : 0 ≤ maximum A B := by
  simpa only [quad,pow_two,mul_zero,add_zero] using
    (quad_le_maximum (A := A) (B := B) (y := 0) ⟨le_rfl,by norm_num⟩)

theorem endpoint_le_maximum (A B : ℝ) : A+B ≤ maximum A B := by
  simpa only [quad,one_pow,mul_one] using
    (quad_le_maximum (A := A) (B := B) (y := 1) ⟨by norm_num,le_rfl⟩)

theorem maximum_le_iff (A B M : ℝ) :
    maximum A B ≤ M ↔ ∀ y ∈ Set.Icc (0 : ℝ) 1, quad A B y ≤ M := by
  constructor
  · intro h y hy
    exact (quad_le_maximum hy).trans h
  · intro h
    obtain ⟨y,hy,heq⟩ := maximum_attained A B
    rw [← heq]
    exact h y hy

/-- Increasing either signed coefficient increases the exact maximum. -/
theorem maximum_mono {A B A' B' : ℝ} (hA : A ≤ A') (hB : B ≤ B') :
    maximum A B ≤ maximum A' B' := by
  obtain ⟨y,hy,heq⟩ := maximum_attained A B
  rw [← heq]
  calc
    quad A B y ≤ quad A' B' y :=
      add_le_add (mul_le_mul_of_nonneg_right hA (sq_nonneg y))
        (mul_le_mul_of_nonneg_right hB hy.1)
    _ ≤ maximum A' B' := quad_le_maximum hy

theorem maximum_monotone_first (B : ℝ) : Monotone (fun A => maximum A B) :=
  fun _ _ h => maximum_mono h le_rfl

theorem maximum_monotone_second (A : ℝ) : Monotone (maximum A) :=
  fun _ _ h => maximum_mono le_rfl h

/-- Perturbing signed coefficients has a uniform error on the whole radius domain. -/
theorem maximum_sub_le (A B C D : ℝ) :
    maximum A B-maximum C D ≤ |A-C|+|B-D| := by
  obtain ⟨y,hy,heq⟩ := maximum_attained A B
  have hy2 : y^2 ≤ 1 := by nlinarith [hy.1,hy.2]
  have hA : (A-C)*y^2 ≤ |A-C| := by
    calc
      (A-C)*y^2 ≤ |A-C| * y^2 :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg y)
      _ ≤ |A-C| := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hy2 (abs_nonneg (A-C))
  have hB : (B-D)*y ≤ |B-D| := by
    calc
      (B-D)*y ≤ |B-D| * y :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hy.1
      _ ≤ |B-D| := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 (abs_nonneg (B-D))
  have hupper := quad_le_maximum (A := C) (B := D) hy
  unfold quad at heq hupper
  nlinarith only [heq,hupper,hA,hB]

theorem maximum_lipschitz (A B C D : ℝ) :
    |maximum A B-maximum C D| ≤ |A-C|+|B-D| := by
  apply abs_le.mpr
  constructor
  · have h := maximum_sub_le C D A B
    rw [abs_sub_comm C A,abs_sub_comm D B] at h
    linarith only [h]
  · exact maximum_sub_le A B C D

def maximumQ (A B : ℚ) : ℚ :=
  if A < 0 ∧ 0 < B ∧ B < -2*A then -B^2/(4*A) else max 0 (A+B)

theorem maximum_cast (A B : ℚ) :
    (maximumQ A B : ℝ) = maximum (A : ℝ) (B : ℝ) := by
  unfold maximumQ maximum
  by_cases h : A < 0 ∧ 0 < B ∧ B < -2*A
  · have hr : (A : ℝ) < 0 ∧ 0 < (B : ℝ) ∧ (B : ℝ) < -2*(A : ℝ) := by
      exact_mod_cast h
    rw [if_pos h,if_pos hr]
    norm_cast
  · have hr : ¬ ((A : ℝ) < 0 ∧ 0 < (B : ℝ) ∧ (B : ℝ) < -2*(A : ℝ)) := by
      intro hh
      apply h
      exact_mod_cast hh
    rw [if_neg h,if_neg hr]
    simp only [Rat.cast_max,Rat.cast_zero,Rat.cast_add]

theorem maximum_rational_enclosure {A B : ℝ} {aLo aHi bLo bHi : ℚ}
    (haLo : (aLo : ℝ) ≤ A) (haHi : A ≤ (aHi : ℝ))
    (hbLo : (bLo : ℝ) ≤ B) (hbHi : B ≤ (bHi : ℝ)) :
    (maximumQ aLo bLo : ℝ) ≤ maximum A B ∧
      maximum A B ≤ (maximumQ aHi bHi : ℝ) := by
  rw [maximum_cast,maximum_cast]
  exact ⟨maximum_mono haLo hbLo,maximum_mono haHi hbHi⟩

theorem maximumQ_mono {A B C D : ℚ} (hA : A ≤ C) (hB : B ≤ D) :
    maximumQ A B ≤ maximumQ C D := by
  have hAr : (A : ℝ) ≤ (C : ℝ) := by exact_mod_cast hA
  have hBr : (B : ℝ) ≤ (D : ℝ) := by exact_mod_cast hB
  have h := maximum_mono hAr hBr
  rw [← maximum_cast,← maximum_cast] at h
  exact_mod_cast h

theorem maximum_le_rational_bound {A B : ℝ} {aHi bHi bound : ℚ}
    (haHi : A ≤ (aHi : ℝ)) (hbHi : B ≤ (bHi : ℝ))
    (hbound : maximumQ aHi bHi ≤ bound) : maximum A B ≤ (bound : ℝ) := by
  have h : maximum (aHi : ℝ) (bHi : ℝ) ≤ (bound : ℝ) := by
    rw [← maximum_cast]
    exact_mod_cast hbound
  exact (maximum_mono haHi hbHi).trans h

theorem quad_le_rational_maximum {A B y : ℝ} {aHi bHi : ℚ}
    (haHi : A ≤ (aHi : ℝ)) (hbHi : B ≤ (bHi : ℝ))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    quad A B y ≤ (maximumQ aHi bHi : ℝ) := by
  rw [maximum_cast]
  exact (quad_le_maximum hy).trans (maximum_mono haHi hbHi)

theorem quad_le_rational_bound {A B y : ℝ} {aHi bHi bound : ℚ}
    (haHi : A ≤ (aHi : ℝ)) (hbHi : B ≤ (bHi : ℝ))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hbound : maximumQ aHi bHi ≤ bound) :
    quad A B y ≤ (bound : ℝ) :=
  (quad_le_maximum hy).trans (maximum_le_rational_bound haHi hbHi hbound)

end N11Formalization.CompactQuadraticMomentMaximum

#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_of_vertex
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_of_endpoint
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_zero_first
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_zero_second
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_vertex_boundary
#print axioms N11Formalization.CompactQuadraticMomentMaximum.quad_le_maximum
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_attained
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_nonneg
#print axioms N11Formalization.CompactQuadraticMomentMaximum.endpoint_le_maximum
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_le_iff
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_mono
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_monotone_first
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_monotone_second
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_sub_le
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_lipschitz
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_cast
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_rational_enclosure
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximumQ_mono
#print axioms N11Formalization.CompactQuadraticMomentMaximum.maximum_le_rational_bound
#print axioms N11Formalization.CompactQuadraticMomentMaximum.quad_le_rational_maximum
#print axioms N11Formalization.CompactQuadraticMomentMaximum.quad_le_rational_bound
