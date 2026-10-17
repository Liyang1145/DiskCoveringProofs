import N11Formalization.CompactQuadraticMomentMaximum

/-! Extremal closed-interval maximizers of a signed radius quadratic.  The
endpoint tie is retained as an interval, which makes coefficient enclosures
valid without selecting an arbitrary tied maximizer. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CompactQuadraticArgmaxRange

open CompactQuadraticMomentMaximum

def lowerArg (A B : ℝ) : ℝ :=
  if A < 0 ∧ 0 < B ∧ B < -2*A then -B/(2*A) else if 0 < A+B then 1 else 0

def upperArg (A B : ℝ) : ℝ :=
  if A < 0 ∧ 0 < B ∧ B < -2*A then -B/(2*A) else if A+B < 0 then 0 else 1

private theorem vertex_mem {A B : ℝ} (h : A < 0 ∧ 0 < B ∧ B < -2*A) :
    -B/(2*A) ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : 2*A < 0 := by linarith [h.1]
  constructor
  · exact div_nonneg_of_nonpos (by linarith [h.2.1]) hd.le
  · apply (div_le_iff_of_neg hd).mpr
    linarith [h.2.2]

theorem lowerArg_mem (A B : ℝ) : lowerArg A B ∈ Set.Icc (0 : ℝ) 1 := by
  unfold lowerArg
  split_ifs with h hs
  · exact vertex_mem h
  · norm_num
  · norm_num

theorem upperArg_mem (A B : ℝ) : upperArg A B ∈ Set.Icc (0 : ℝ) 1 := by
  unfold upperArg
  split_ifs with h hs
  · exact vertex_mem h
  · norm_num
  · norm_num

private theorem vertex_attained {A B : ℝ} (h : A < 0 ∧ 0 < B ∧ B < -2*A) :
    quad A B (-B/(2*A)) = maximum A B := by
  rw [maximum_of_vertex h]
  unfold quad
  field_simp [ne_of_lt h.1]
  ring

theorem lowerArg_attained (A B : ℝ) :
    quad A B (lowerArg A B) = maximum A B := by
  unfold lowerArg
  split_ifs with h hs
  · exact vertex_attained h
  · rw [maximum_of_endpoint h, max_eq_right hs.le]
    simp [quad]
  · rw [maximum_of_endpoint h, max_eq_left (le_of_not_gt hs)]
    simp [quad]

theorem upperArg_attained (A B : ℝ) :
    quad A B (upperArg A B) = maximum A B := by
  unfold upperArg
  split_ifs with h hs
  · exact vertex_attained h
  · rw [maximum_of_endpoint h, max_eq_left hs.le]
    simp [quad]
  · rw [maximum_of_endpoint h, max_eq_right (le_of_not_gt hs)]
    simp [quad]

private theorem vertex_unique {A B y : ℝ}
    (h : A < 0 ∧ 0 < B ∧ B < -2*A)
    (heq : quad A B y = maximum A B) : y = -B/(2*A) := by
  rw [maximum_of_vertex h] at heq
  have hA : A ≠ 0 := ne_of_lt h.1
  have h4 : 4*A ≠ 0 := mul_ne_zero (by norm_num) hA
  have hh := (eq_div_iff h4).mp heq
  unfold quad at hh
  have hz : (2*A*y+B)^2 = 0 := by nlinarith only [hh]
  have hz' := sq_eq_zero_iff.mp hz
  apply (eq_div_iff (mul_ne_zero (by norm_num) hA)).mpr
  linarith only [hz']

private theorem endpoint_zero_unique {A B y : ℝ}
    (h : ¬ (A < 0 ∧ 0 < B ∧ B < -2*A)) (hs : A+B < 0)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (heq : quad A B y = maximum A B) : y = 0 := by
  rw [maximum_of_endpoint h, max_eq_left hs.le] at heq
  by_cases hA : 0 ≤ A
  · have hy2 : y^2 ≤ y := by nlinarith [hy.1,hy.2]
    have hm := mul_le_mul_of_nonneg_left hy2 hA
    unfold quad at heq
    nlinarith only [heq,hm,hs,hy.1]
  · have hAn : A < 0 := lt_of_not_ge hA
    by_cases hB : B ≤ 0
    · have hm := mul_nonpos_of_nonpos_of_nonneg hB hy.1
      unfold quad at heq
      have ha := mul_nonpos_of_nonpos_of_nonneg hAn.le (sq_nonneg y)
      have hz : A*y^2 = 0 := by linarith only [heq,hm,ha]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact False.elim (ne_of_lt hAn hz)
      · exact sq_eq_zero_iff.mp hz
    · have hBp : 0 < B := lt_of_not_ge hB
      have hd : -2*A ≤ B := by
        by_contra hn
        exact h ⟨hAn,hBp,lt_of_not_ge hn⟩
      linarith only [hAn,hs,hd]

private theorem endpoint_one_unique {A B y : ℝ}
    (h : ¬ (A < 0 ∧ 0 < B ∧ B < -2*A)) (hs : 0 < A+B)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (heq : quad A B y = maximum A B) : y = 1 := by
  rw [maximum_of_endpoint h, max_eq_right hs.le] at heq
  by_cases hA : 0 ≤ A
  · have hy2 : y^2 ≤ y := by nlinarith [hy.1,hy.2]
    have hm := mul_le_mul_of_nonneg_left hy2 hA
    unfold quad at heq
    nlinarith only [heq,hm,hs,hy.2]
  · have hAn : A < 0 := lt_of_not_ge hA
    have hBp : 0 < B := by linarith only [hAn,hs]
    have hd : -2*A ≤ B := by
      by_contra hn
      exact h ⟨hAn,hBp,lt_of_not_ge hn⟩
    have hAy : A ≤ A*y := by
      simpa only [mul_one] using mul_le_mul_of_nonpos_left hy.2 hAn.le
    have hz : (1-y)*(A*(1+y)+B) = 0 := by
      unfold quad at heq
      nlinarith only [heq]
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith only [hz]
    · have hAy' : A*y = A := by nlinarith only [hz,hd,hAy]
      have hh : A*(y-1) = 0 := by nlinarith only [hAy']
      rcases mul_eq_zero.mp hh with hh | hh
      · exact False.elim (ne_of_lt hAn hh)
      · linarith only [hh]

/-- The two definitions are the least and greatest maximizers, including ties. -/
theorem maximizer_bounds {A B y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (heq : quad A B y = maximum A B) :
    lowerArg A B ≤ y ∧ y ≤ upperArg A B := by
  by_cases h : A < 0 ∧ 0 < B ∧ B < -2*A
  · have hh := vertex_unique h heq
    simp only [lowerArg,upperArg,if_pos h]
    exact ⟨hh.ge,hh.le⟩
  · simp only [lowerArg,upperArg,if_neg h]
    by_cases hp : 0 < A+B
    · have hh := endpoint_one_unique h hp hy heq
      rw [if_pos hp,if_neg (by linarith only [hp] : ¬ A+B < 0),hh]
      exact ⟨le_rfl,le_rfl⟩
    · by_cases hn : A+B < 0
      · have hh := endpoint_zero_unique h hn hy heq
        rw [if_neg hp,if_pos hn,hh]
        exact ⟨le_rfl,le_rfl⟩
      · rw [if_neg hp,if_neg hn]
        exact hy

private theorem increasing_differences {A B C D x y : ℝ}
    (hA : A ≤ C) (hB : B ≤ D) (hx : 0 ≤ x) (hxy : x ≤ y) :
    quad A B y-quad A B x ≤ quad C D y-quad C D x := by
  have hy : 0 ≤ y := hx.trans hxy
  have hs : 0 ≤ y^2-x^2 := by nlinarith only [hx,hy,hxy]
  have hmA := mul_nonneg (sub_nonneg.mpr hA) hs
  have hmB := mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hxy)
  unfold quad
  nlinarith only [hmA,hmB]

/-- Coordinatewise coefficient bounds enclose every maximizer; tied endpoints
are deliberately enclosed by their least and greatest choices. -/
theorem maximizer_corner_enclosure {A B aLo aHi bLo bHi y : ℝ}
    (haLo : aLo ≤ A) (haHi : A ≤ aHi)
    (hbLo : bLo ≤ B) (hbHi : B ≤ bHi)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (heq : quad A B y = maximum A B) :
    lowerArg aLo bLo ≤ y ∧ y ≤ upperArg aHi bHi := by
  constructor
  · by_contra hn
    have hxy : y ≤ lowerArg aLo bLo := (lt_of_not_ge hn).le
    have hd := increasing_differences haLo hbLo hy.1 hxy
    have hl := quad_le_maximum (A := aLo) (B := bLo) hy
    have hu := quad_le_maximum (A := A) (B := B) (lowerArg_mem aLo bLo)
    rw [lowerArg_attained] at hd
    have heql : quad aLo bLo y = maximum aLo bLo := by
      linarith only [hd,hl,hu,heq]
    exact hn (maximizer_bounds hy heql).1
  · by_contra hn
    have hxy : upperArg aHi bHi ≤ y := (lt_of_not_ge hn).le
    have hd := increasing_differences haHi hbHi (upperArg_mem aHi bHi).1 hxy
    have hl := quad_le_maximum (A := A) (B := B) (upperArg_mem aHi bHi)
    have hu := quad_le_maximum (A := aHi) (B := bHi) hy
    rw [upperArg_attained] at hd
    have hequ : quad aHi bHi y = maximum aHi bHi := by
      linarith only [hd,hl,hu,heq]
    exact hn (maximizer_bounds hy hequ).2

def lowerArgQ (A B : ℚ) : ℚ :=
  if A < 0 ∧ 0 < B ∧ B < -2*A then -B/(2*A) else if 0 < A+B then 1 else 0

def upperArgQ (A B : ℚ) : ℚ :=
  if A < 0 ∧ 0 < B ∧ B < -2*A then -B/(2*A) else if A+B < 0 then 0 else 1

theorem lowerArg_cast (A B : ℚ) :
    (lowerArgQ A B : ℝ) = lowerArg (A : ℝ) (B : ℝ) := by
  unfold lowerArgQ lowerArg
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
    by_cases hs : 0 < A+B
    · have hsr : 0 < (A : ℝ)+(B : ℝ) := by exact_mod_cast hs
      rw [if_pos hs,if_pos hsr]
      norm_num
    · have hsr : ¬ 0 < (A : ℝ)+(B : ℝ) := by exact_mod_cast hs
      rw [if_neg hs,if_neg hsr]
      norm_num

theorem upperArg_cast (A B : ℚ) :
    (upperArgQ A B : ℝ) = upperArg (A : ℝ) (B : ℝ) := by
  unfold upperArgQ upperArg
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
    by_cases hs : A+B < 0
    · have hsr : (A : ℝ)+(B : ℝ) < 0 := by exact_mod_cast hs
      rw [if_pos hs,if_pos hsr]
      norm_num
    · have hsr : ¬ (A : ℝ)+(B : ℝ) < 0 := by exact_mod_cast hs
      rw [if_neg hs,if_neg hsr]
      norm_num

theorem lowerArgQ_nonneg (A B : ℚ) : 0 ≤ lowerArgQ A B := by
  have hh := (lowerArg_mem (A : ℝ) (B : ℝ)).1
  rw [← lowerArg_cast] at hh
  exact_mod_cast hh

theorem lowerArgQ_le_one (A B : ℚ) : lowerArgQ A B ≤ 1 := by
  have hh := (lowerArg_mem (A : ℝ) (B : ℝ)).2
  rw [← lowerArg_cast] at hh
  exact_mod_cast hh

theorem upperArgQ_nonneg (A B : ℚ) : 0 ≤ upperArgQ A B := by
  have hh := (upperArg_mem (A : ℝ) (B : ℝ)).1
  rw [← upperArg_cast] at hh
  exact_mod_cast hh

theorem upperArgQ_le_one (A B : ℚ) : upperArgQ A B ≤ 1 := by
  have hh := (upperArg_mem (A : ℝ) (B : ℝ)).2
  rw [← upperArg_cast] at hh
  exact_mod_cast hh

theorem maximizer_rational_enclosure {A B y : ℝ} {aLo aHi bLo bHi : ℚ}
    (haLo : (aLo : ℝ) ≤ A) (haHi : A ≤ (aHi : ℝ))
    (hbLo : (bLo : ℝ) ≤ B) (hbHi : B ≤ (bHi : ℝ))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (heq : quad A B y = maximum A B) :
    (lowerArgQ aLo bLo : ℝ) ≤ y ∧ y ≤ (upperArgQ aHi bHi : ℝ) := by
  rw [lowerArg_cast,upperArg_cast]
  exact maximizer_corner_enclosure haLo haHi hbLo hbHi hy heq

theorem maximum_attained_with_rational_enclosure (A B : ℝ)
    (aLo aHi bLo bHi : ℚ)
    (haLo : (aLo : ℝ) ≤ A) (haHi : A ≤ (aHi : ℝ))
    (hbLo : (bLo : ℝ) ≤ B) (hbHi : B ≤ (bHi : ℝ)) :
    ∃ y, y ∈ Set.Icc (0 : ℝ) 1 ∧ quad A B y = maximum A B ∧
      (lowerArgQ aLo bLo : ℝ) ≤ y ∧ y ≤ (upperArgQ aHi bHi : ℝ) := by
  obtain ⟨y,hy,heq⟩ := maximum_attained A B
  exact ⟨y,hy,heq,maximizer_rational_enclosure haLo haHi hbLo hbHi hy heq⟩

theorem maximum_attained_with_rational_upper (A B : ℝ)
    (aLo aHi bLo bHi : ℚ)
    (haLo : (aLo : ℝ) ≤ A) (haHi : A ≤ (aHi : ℝ))
    (hbLo : (bLo : ℝ) ≤ B) (hbHi : B ≤ (bHi : ℝ)) :
    ∃ y, y ∈ Set.Icc (0 : ℝ) 1 ∧ quad A B y = maximum A B ∧
      y ≤ (upperArgQ aHi bHi : ℝ) := by
  obtain ⟨y,hy,heq,hl,hu⟩ :=
    maximum_attained_with_rational_enclosure A B aLo aHi bLo bHi haLo haHi hbLo hbHi
  exact ⟨y,hy,heq,hu⟩

theorem lowerArg_endpoint_tie {A B : ℝ} (hA : 0 ≤ A) (hs : A+B = 0) :
    lowerArg A B = 0 := by
  have hv : ¬ (A < 0 ∧ 0 < B ∧ B < -2*A) := by
    intro hh
    linarith only [hA,hh.1]
  rw [lowerArg,if_neg hv]
  simp only [hs,lt_self_iff_false,if_false]

theorem upperArg_endpoint_tie {A B : ℝ} (hA : 0 ≤ A) (hs : A+B = 0) :
    upperArg A B = 1 := by
  have hv : ¬ (A < 0 ∧ 0 < B ∧ B < -2*A) := by
    intro hh
    linarith only [hA,hh.1]
  rw [upperArg,if_neg hv]
  simp only [hs,lt_self_iff_false,if_false]

theorem zero_coefficients_all_maximizers (y : ℝ) :
    quad 0 0 y = maximum 0 0 := by simp [quad,maximum]

end N11Formalization.CompactQuadraticArgmaxRange

#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_mem
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_mem
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_attained
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_attained
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximizer_bounds
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximizer_corner_enclosure
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_cast
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_cast
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArgQ_nonneg
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArgQ_le_one
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArgQ_nonneg
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArgQ_le_one
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximizer_rational_enclosure
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximum_attained_with_rational_enclosure
#print axioms N11Formalization.CompactQuadraticArgmaxRange.maximum_attained_with_rational_upper
#print axioms N11Formalization.CompactQuadraticArgmaxRange.lowerArg_endpoint_tie
#print axioms N11Formalization.CompactQuadraticArgmaxRange.upperArg_endpoint_tie
#print axioms N11Formalization.CompactQuadraticArgmaxRange.zero_coefficients_all_maximizers
