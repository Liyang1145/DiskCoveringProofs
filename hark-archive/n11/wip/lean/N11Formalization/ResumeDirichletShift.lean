import N11Formalization.ResumeDirichlet

noncomputable section
namespace N11Formalization.ResumeDirichletShift
open ResumeNetwork ResumeDirichlet

/-- Base flux applied to anchor displacement; the sign is inherited from
actual site-minus-anchor edge vectors, not assumed from a matrix convention. -/
def baseCross (α : Edge → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point)
    (dU : Fin 9 → Point) : ℝ :=
  ∑ e, α e * inner ℝ (edgeVector U C Z e) (edgeVector dU 0 0 e)

theorem edge_add (U V : Fin 9 → Point) (C Z D W : Fin 11 → Point) (e : Edge) :
    edgeVector (U+V) (C+D) (Z+W) e = edgeVector U C Z e + edgeVector V D W e := by
  rcases e with ⟨i,s⟩ | ⟨f,j⟩ <;> simp only [edgeVector, Pi.add_apply] <;> abel

theorem cross_eq {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (hbal : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (V : Fin 9 → Point) (D W : Fin 11 → Point) :
    (∑ e, α e * inner ℝ (edgeVector U C Z e) (edgeVector V D W e)) =
      baseCross α U C Z V := by
  have hz := cross_term_zero_of_balance α incidence (edgeVector U C Z) hbal (Sum.elim D W)
  simp only [incidence_apply] at hz
  have he : ∀ e, edgeVector V D W e = edgeVector V 0 0 e + edgeVector 0 D W e := by
    intro e
    simpa using edge_add V 0 0 0 D W e
  simp_rw [he, inner_add_right, mul_add, Finset.sum_add_distrib]
  have hz' : (∑ e, α e * inner ℝ (edgeVector U C Z e) (edgeVector 0 D W e)) = 0 := by
    simpa only [Pi.zero_def] using hz
  rw [hz', add_zero]
  rfl

/-- Exact trial energy expansion, with arbitrary free-node variation. -/
theorem energy_shift {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (hbal : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (V : Fin 9 → Point) (D W : Fin 11 → Point) :
    energy α (U+V) (C+D) (Z+W) = energy α U C Z +
      2 * baseCross α U C Z V + energy α V D W := by
  simp only [energy, edgeLength_eq_norm, edge_add, norm_add_sq_real,
    mul_add, Finset.sum_add_distrib]
  rw [show (∑ e, α e * (2 * inner ℝ (edgeVector U C Z e) (edgeVector V D W e))) =
    2 * ∑ e, α e * inner ℝ (edgeVector U C Z e) (edgeVector V D W e) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring]
  rw [cross_eq hbal]

/-- Exact minimized-energy expansion at a balanced base. No inverse, strict
positivity, uniqueness, or existence of a minimizer at displaced anchors is used. -/
theorem dirichlet_shift {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (hα : ∀ e, 0 ≤ α e)
    (hbal : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (V : Fin 9 → Point) :
    dirichletEnergy α (U+V) = energy α U C Z +
      2 * baseCross α U C Z V + dirichletEnergy α V := by
  apply le_antisymm
  · have hb : dirichletEnergy α (U+V) - (energy α U C Z + 2*baseCross α U C Z V)
        ≤ dirichletEnergy α V := by
      apply le_csInf
      · exact ⟨energy α V 0 0, (0,0), rfl⟩
      · rintro a ⟨⟨D,W⟩, rfl⟩
        have h := dirichlet_le_energy hα (U+V) (C+D) (Z+W)
        rw [energy_shift hbal] at h
        linarith
    linarith
  · apply le_csInf
    · exact ⟨energy α (U+V) C Z, (C,Z), rfl⟩
    · rintro a ⟨⟨D,W⟩, rfl⟩
      have hs := energy_shift hbal V (D-C) (W-Z)
      have hl := dirichlet_le_energy hα V (D-C) (W-Z)
      have hD : C + (D-C) = D := by abel
      have hW : Z + (W-Z) = W := by abel
      rw [hD, hW] at hs
      linarith

#print axioms dirichlet_shift
end N11Formalization.ResumeDirichletShift
