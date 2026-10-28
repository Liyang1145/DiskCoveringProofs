import N11Formalization.ResumeHarmonic
import N11Formalization.Geometry.ArcCovering

noncomputable section
namespace N11Formalization.ResumeSchurEnergy
open ResumeNetwork ResumeDirichlet ResumeHarmonic

def gram (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (i j : Fin 9) : ℝ :=
  ∑ e, α e * coeff H e i * coeff H e j

/-- No Schur inverse is assumed: this is the exact Gram form of the harmonic
edge extension, valid for arbitrary boundary vectors. -/
theorem energy_eq_gram (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (U : Fin 9 → Point) :
    (∑ e, α e * ‖∑ j, coeff H e j • U j‖ ^ 2) =
      ∑ i, ∑ j, gram α H i j * inner ℝ (U i) (U j) := by
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [gram, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Certified matrix energy is a lower bound for the actual network oracle. -/
theorem gram_le_oracle (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hα : ∀ e, 0 ≤ α e) (hs : ∑ e, α e = 1)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (U : Fin 9 → Point) (hU : ∀ j, ‖U j‖ ≤ 1) :
    (∑ i, ∑ j, gram α H i j * inner ℝ (U i) (U j)) ≤ V2 U := by
  rw [← energy_eq_gram]
  exact harmonic_energy_le_oracle α H hα hs hbal U hU

/-- An affine harmonic extension has zero edge row sums, including boundary edges. -/
theorem coeff_sum_zero (H : Free → Fin 9 → ℝ)
    (hH : ∀ v, ∑ j, H v j = 1) (e : Edge) : ∑ j, coeff H e j = 0 := by
  rcases e with ⟨i, side⟩ | ⟨f, k⟩
  · simp [coeff, Finset.sum_sub_distrib, hH]
  · simp [coeff, Finset.sum_sub_distrib, hH]

theorem gram_row_zero (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hH : ∀ v, ∑ j, H v j = 1) (i : Fin 9) : ∑ j, gram α H i j = 0 := by
  simp only [gram]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, coeff_sum_zero H hH, mul_zero]
  simp

theorem gram_symmetric (α : Edge → ℝ) (H : Free → Fin 9 → ℝ) (i j : Fin 9) :
    gram α H i j = gram α H j i := by
  unfold gram
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Zero row sums supply the constant term in the cosine-energy formula.
The double sum is ordered; its off-diagonal terms occur twice. -/
theorem gram_energy_eq_one_sub_inner (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hH : ∀ v, ∑ j, H v j = 1) (U : Fin 9 → Point) :
    (∑ i, ∑ j, gram α H i j * inner ℝ (U i) (U j)) =
      ∑ i, ∑ j, -(gram α H i j) * (1 - inner ℝ (U i) (U j)) := by
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (∑ j, gram α H i j * inner ℝ (U i) (U j)) - ∑ j, gram α H i j := by
      rw [gram_row_zero α H hH]; ring
    _ = ∑ j, -(gram α H i j) * (1 - inner ℝ (U i) (U j)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The factor two in the 36 unordered-pair representation is explicit. -/
theorem sum_symmetric_pairs (f : Fin 9 → Fin 9 → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
  have he (i j : Fin 9) : f i j = (if i < j then f i j else 0) +
      (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simp [hd]
    · simp [h, not_lt_of_ge h.le, hs i j]
  calc
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f j i else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => he i j)
    _ = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
      rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
      ring

/-- This is exactly the 36-pair cosine energy used by the source library:
weights are minus the off-diagonal Gram entries, with the required factor two. -/
theorem cosine_energy_eq (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hH : ∀ v, ∑ j, H v j = 1) (θ : Fin 9 → ℝ) :
    (∑ e, α e * ‖∑ j, coeff H e j • circleMap (θ j)‖ ^ 2) =
      2 * ∑ i, ∑ j, if i < j then
        -(gram α H i j) * (1 - Real.cos (θ i - θ j)) else 0 := by
  rw [energy_eq_gram, gram_energy_eq_one_sub_inner α H hH]
  simp_rw [inner_circleMap]
  apply sum_symmetric_pairs
  · intro i j
    rw [gram_symmetric α H i j]
    have hc : Real.cos (θ i - θ j) = Real.cos (θ j - θ i) := by
      rw [← Real.cos_neg (θ j - θ i)]
      congr 1
      ring
    rw [hc]
  · intro i
    simp

theorem cosine_energy_le_oracle (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hα : ∀ e, 0 ≤ α e) (hs : ∑ e, α e = 1)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (hH : ∀ v, ∑ j, H v j = 1) (θ : Fin 9 → ℝ) :
    (2 * ∑ i, ∑ j, if i < j then
      -(gram α H i j) * (1 - Real.cos (θ i - θ j)) else 0) ≤
      V2 (fun j => circleMap (θ j)) := by
  rw [← cosine_energy_eq α H hH]
  exact harmonic_energy_le_oracle α H hα hs hbal _ (fun j => (circleMap_norm (θ j)).le)

#check @cosine_energy_le_oracle
#print axioms cosine_energy_le_oracle
#print axioms sum_symmetric_pairs
#print axioms gram_energy_eq_one_sub_inner
#print axioms gram_row_zero
#print axioms energy_eq_gram
#print axioms gram_le_oracle
end N11Formalization.ResumeSchurEnergy
