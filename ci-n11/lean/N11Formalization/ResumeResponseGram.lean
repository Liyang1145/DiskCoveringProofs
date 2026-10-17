import N11Formalization.ResumeAnchorFlux
import N11Formalization.FlashLocalH0

noncomputable section
namespace N11Formalization.ResumeResponseGram
open ResumeNetwork ResumeDirichlet FlashLocal

def response (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ) (i j : Fin 9) : ℝ :=
  ∑ e, α e * K e i * K e j

/-- A scalar harmonic-extension edge matrix gives the full mixed response,
including all i,j terms, with no nonsingularity assumption. -/
theorem gram_energy (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ) (W : Fin 9 → Point) :
    Eform (response α K) W W = ∑ e, α e * ‖∑ i, K e i • W i‖^2 := by
  simp only [Eform, response, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A supplied scalar extension K is certified against actual network edges
and actual node balance; these finite identities replace an abstract response
identity. Constructing/certifying K for the original stress remains separate. -/
theorem response_eq_dirichlet (α : Edge → ℝ) (K : Edge → Fin 9 → ℝ)
    (C Z : (Fin 9 → Point) → Fin 11 → Point) (hα : ∀ e, 0 ≤ α e)
    (hK : ∀ W e, edgeVector W (C W) (Z W) e = ∑ i, K e i • W i)
    (hbal : ∀ W v, ∑ e, (α e * incidence e v) • edgeVector W (C W) (Z W) e = 0)
    (W : Fin 9 → Point) : Eform (response α K) W W = dirichletEnergy α W := by
  rw [dirichlet_eq_of_node_balance (C W) (Z W) hα (hbal W), gram_energy]
  simp only [energy, edgeLength_eq_norm, hK]

#print axioms gram_energy
#print axioms response_eq_dirichlet
end N11Formalization.ResumeResponseGram
