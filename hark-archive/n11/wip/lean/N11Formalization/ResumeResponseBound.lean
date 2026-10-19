import N11Formalization.ResumeResponseProperties
import N11Formalization.FlashLocalMixedPinned
import Mathlib.Algebra.QuadraticDiscriminant
import N11Formalization.ResumeStressComparison

noncomputable section
namespace N11Formalization.ResumeResponseBound
open ResumeNetwork ResumeDirichlet ResumeResponseGram FlashLocal

/-- PSD on all mixed directions yields Cauchy--Schwarz for the response form. -/
theorem form_cauchy (Λ : Fin 9 → Fin 9 → ℝ)
    (hs : ∀ i j, Λ i j = Λ j i)
    (hp : ∀ U : Fin 9 → Point, 0 ≤ Eform Λ U U) (U W : Fin 9 → Point) :
    (Eform Λ U W)^2 ≤ Eform Λ U U * Eform Λ W W := by
  have hpoly : ∀ t : ℝ, 0 ≤ Eform Λ U U * (t*t) +
      (2*Eform Λ U W)*t + Eform Λ W W := by
    intro t
    have h := hp (fun i => t • U i + W i)
    rw [Eform_decomp Λ hs] at h
    have h1 : Eform Λ (fun i => t • U i) (fun i => t • U i) = t*t*Eform Λ U U := by
      simp only [Eform, real_inner_smul_left, real_inner_smul_right]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h2 : Eform Λ (fun i => t • U i) W = t * Eform Λ U W := by
      simp only [Eform, real_inner_smul_left, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, h2] at h
    nlinarith
  have h := discrim_le_zero hpoly
  unfold discrim at h
  nlinarith

/-- A diagonal bound suffices for the full bilinear bound. No separate mixed
operator norm certificate is required once actual response PSD is known. -/
theorem form_bound (Λ : Fin 9 → Fin 9 → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hs : ∀ i j, Λ i j = Λ j i)
    (hp : ∀ U : Fin 9 → Point, 0 ≤ Eform Λ U U)
    (hb : ∀ U : Fin 9 → Point, Eform Λ U U ≤ d * (frob U)^2)
    (U W : Fin 9 → Point) : |Eform Λ U W| ≤ d * frob U * frob W := by
  have hfU : 0 ≤ frob U := Real.sqrt_nonneg _
  have hfW : 0 ≤ frob W := Real.sqrt_nonneg _
  have hc := form_cauchy Λ hs hp U W
  have hm := mul_le_mul (hb U) (hb W) (hp W) (by positivity : 0 ≤ d * (frob U)^2)
  have ht : 0 ≤ d * frob U * frob W := by positivity
  have hsq : |Eform Λ U W|^2 ≤ (d * frob U * frob W)^2 := by
    rw [sq_abs]
    nlinarith [hm]
  nlinarith [abs_nonneg (Eform Λ U W)]

/-- The actual network diagonal trial bound now pays the full mixed-direction
hypothesis used by the cubic/quartic remainder consumer. -/
theorem network_response_bound (α : Edge → ℝ) (Λ : Fin 9 → Fin 9 → ℝ)
    (d : ℝ) (hd : 0 ≤ d) (hα : ∀ e, 0 ≤ α e)
    (hs : ∀ i j, Λ i j = Λ j i)
    (hp : ∀ U : Fin 9 → Point, 0 ≤ Eform Λ U U)
    (hr : ∀ U : Fin 9 → Point, Eform Λ U U = dirichletEnergy α U)
    (ha : ∀ j, ResumeStressComparison.anchorWeight α j ≤ d)
    (U W : Fin 9 → Point) : |Eform Λ U W| ≤ d * frob U * frob W := by
  apply form_bound Λ d hd hs hp ?_ U W
  intro V
  rw [hr, frob, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖V i‖))]
  exact ResumeStressComparison.dirichlet_le_diagonal hα ha V

#print axioms network_response_bound
#print axioms form_cauchy
#print axioms form_bound
end N11Formalization.ResumeResponseBound
