import N11Formalization.ResumeResponseGram

noncomputable section
namespace N11Formalization.ResumeResponseColumns
open ResumeNetwork ResumeDirichlet ResumeResponseGram FlashLocal

/-- 22 x 9 scalar column equations imply node balance for every vector-valued
anchor displacement; no pointwise differentiation or numerical rank claim. -/
theorem balance_of_columns (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ)
    (C Z : (Fin 9 → Point) → Fin 11 → Point)
    (hK : ∀ W e, edgeVector W (C W) (Z W) e = ∑ i, K e i • W i)
    (hc : ∀ v i, ∑ e, α e * incidence e v * K e i = 0)
    (W : Fin 9 → Point) (v : Free) :
    ∑ e, (α e * incidence e v) • edgeVector W (C W) (Z W) e = 0 := by
  simp_rw [hK, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hc, zero_smul]
  simp

/-- Response identity with finite scalar equilibrium premises. -/
theorem response_eq_of_columns (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ)
    (C Z : (Fin 9 → Point) → Fin 11 → Point) (hα : ∀ e, 0 ≤ α e)
    (hK : ∀ W e, edgeVector W (C W) (Z W) e = ∑ i, K e i • W i)
    (hc : ∀ v i, ∑ e, α e * incidence e v * K e i = 0) (W : Fin 9 → Point) :
    Eform (response α K) W W = dirichletEnergy α W :=
  response_eq_dirichlet α K C Z hα hK (balance_of_columns α K C Z hK hc) W

#print axioms response_eq_of_columns
end N11Formalization.ResumeResponseColumns
