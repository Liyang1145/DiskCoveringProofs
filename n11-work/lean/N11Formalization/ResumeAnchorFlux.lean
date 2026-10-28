import N11Formalization.ResumeDirichletShift
import N11Formalization.FlashLocalAdaptive

noncomputable section
namespace N11Formalization.ResumeAnchorFlux
open ResumeNetwork ResumeDirichlet ResumeDirichletShift

/-- Site-minus-anchor convention: boundary incidence is negative. -/
def anchorIncidence : Edge → Fin 9 → ℝ
  | .inl (i,s), j => if anchorIndex i s = j then -1 else 0
  | .inr _, _ => 0

theorem anchorIncidence_apply (V : Fin 9 → Point) (e : Edge) :
    (∑ j, anchorIncidence e j • V j) = edgeVector V 0 0 e := by
  rcases e with ⟨i,s⟩ | ⟨f,k⟩ <;> simp [anchorIncidence, edgeVector]

/-- Actual anchor force for any signed stress, with no factor of two. -/
def flux (α : Edge → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point) (j : Fin 9) : Point :=
  ∑ e, (anchorIncidence e j * α e) • edgeVector U C Z e

theorem baseCross_eq_flux (α : Edge → ℝ) (U V : Fin 9 → Point) (C Z : Fin 11 → Point) :
    baseCross α U C Z V = ∑ j, inner ℝ (flux α U C Z j) (V j) := by
  unfold baseCross
  simp_rw [← anchorIncidence_apply, inner_sum, real_inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [flux, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The generic adaptive finite-sum theorem now acts on the actual 51-edge
baseCross used by the minimized-energy expansion. Source N identities and its
norm bounds are deliberately not asserted here. -/
theorem adaptive_baseCross (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    (tang : Fin 9 → Point) (N : Edge → Fin 4 → ℝ) (τ : ℝ) (x : Fin 9 → ℝ) :
    2 * baseCross (FlashLocal.Qx anchorIncidence (edgeVector U C Z) tang N τ x)
      U C Z (fun j => x j • tang j) =
      τ * ∑ a, (FlashLocal.GtX anchorIncidence (edgeVector U C Z) tang N x a)^2 := by
  rw [baseCross_eq_flux]
  exact FlashLocal.adaptive_cross_identity anchorIncidence (edgeVector U C Z) tang N τ x

#check @adaptive_baseCross
#print axioms adaptive_baseCross
end N11Formalization.ResumeAnchorFlux
