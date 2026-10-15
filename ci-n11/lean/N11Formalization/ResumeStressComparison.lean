import N11Formalization.ResumeNetwork

/-! Order comparison of minimized energies, without any inverse differentiation.
Allows zero-weight edges; in particular the six slack edges of the local network.
This pays the variational interface only, not the source-specific stress bounds. -/
namespace N11Formalization.ResumeStressComparison
open ResumeNetwork

 theorem energy_scaled_le {α β : Edge → ℝ} (s : ℝ)
    (h : ∀ e, s * α e ≤ β e) (U : Fin 9 → Point) (C Z : Fin 11 → Point) :
    s * energy α U C Z ≤ energy β U C Z := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h e) (sq_nonneg (edgeLength U C Z e))

 theorem dirichlet_scaled_le {α β : Edge → ℝ} {s : ℝ}
    (hα : ∀ e, 0 ≤ α e) (hs : 0 ≤ s) (h : ∀ e, s * α e ≤ β e)
    (U : Fin 9 → Point) : s * dirichletEnergy α U ≤ dirichletEnergy β U := by
  apply le_csInf
  · exact Set.range_nonempty _
  · rintro y ⟨⟨C, Z⟩, rfl⟩
    exact (mul_le_mul_of_nonneg_left (dirichlet_le_energy hα U C Z) hs).trans
      (energy_scaled_le s h U C Z)

 theorem dirichlet_le_scaled {α β : Edge → ℝ} {s : ℝ}
    (hβ : ∀ e, 0 ≤ β e) (hs : 0 < s) (h : ∀ e, β e ≤ s * α e)
    (U : Fin 9 → Point) : dirichletEnergy β U ≤ s * dirichletEnergy α U := by
  have hi : ∀ e, s⁻¹ * β e ≤ α e := by
    intro e
    have := mul_le_mul_of_nonneg_left (h e) (inv_nonneg.mpr hs.le)
    simpa [← mul_assoc, inv_mul_cancel₀ hs.ne'] using this
  have hd := dirichlet_scaled_le hβ (inv_nonneg.mpr hs.le) hi U
  have := mul_le_mul_of_nonneg_left hd hs.le
  simpa [← mul_assoc, mul_inv_cancel₀ hs.ne'] using this

/-- The source's (1-bq)Λ₀ ≤ Λα ≤ (1+bq)Λ₀ interpreted on actual vector anchors.
No claim that the minimizer or Schur complement is linear in the varying stress. -/
 theorem dirichlet_relative_comparison {α β : Edge → ℝ} {ε : ℝ}
    (hα : ∀ e, 0 ≤ α e) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hl : ∀ e, (1 - ε) * α e ≤ β e)
    (hu : ∀ e, β e ≤ (1 + ε) * α e) (U : Fin 9 → Point) :
    (1 - ε) * dirichletEnergy α U ≤ dirichletEnergy β U ∧
    dirichletEnergy β U ≤ (1 + ε) * dirichletEnergy α U := by
  have hβ : ∀ e, 0 ≤ β e := fun e =>
    (mul_nonneg (by linarith) (hα e)).trans (hl e)
  exact ⟨dirichlet_scaled_le hα (by linarith) hl U,
    dirichlet_le_scaled hβ (by linarith) hu U⟩

/-- Direct perturbation interface: a single relative absolute edge bound supplies
both sides. The stress change need not be linear in any parameter. -/
theorem dirichlet_of_abs_perturbation {α δ : Edge → ℝ} {ε : ℝ}
    (hα : ∀ e, 0 ≤ α e) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hδ : ∀ e, |δ e| ≤ ε * α e) (U : Fin 9 → Point) :
    (1 - ε) * dirichletEnergy α U ≤ dirichletEnergy (fun e => α e + δ e) U ∧
    dirichletEnergy (fun e => α e + δ e) U ≤ (1 + ε) * dirichletEnergy α U := by
  apply dirichlet_relative_comparison hα hε hε1
  · intro e
    have := (abs_le.mp (hδ e)).1
    nlinarith
  · intro e
    have := (abs_le.mp (hδ e)).2
    nlinarith

/-- Zero free-node trial bounds the minimized form by its boundary diagonal.
This is an upper bound, never a lower bound from a fixed trial assignment. -/
theorem dirichlet_le_boundary_trial {α : Edge → ℝ}
    (hα : ∀ e, 0 ≤ α e) (U : Fin 9 → Point) :
    dirichletEnergy α U ≤
      ∑ i : Fin 9, ∑ side : Fin 2,
        α (.inl (i, side)) * ‖U (anchorIndex i side)‖ ^ 2 := by
  have h := dirichlet_le_energy hα U (fun _ => 0) (fun _ => 0)
  simpa [energy, Fintype.sum_sum_type, Fintype.sum_prod_type, edgeLength,
    dist_zero_left] using h

/-- Total stress incident at anchor j (free-free edges contribute nothing). -/
def anchorWeight (α : Edge → ℝ) (j : Fin 9) : ℝ :=
  ∑ i : Fin 9, ∑ side : Fin 2, if anchorIndex i side = j then α (.inl (i, side)) else 0

 theorem boundary_trial_eq (α : Edge → ℝ) (U : Fin 9 → Point) :
    (∑ i : Fin 9, ∑ side : Fin 2,
      α (.inl (i, side)) * ‖U (anchorIndex i side)‖ ^ 2) =
    ∑ j, anchorWeight α j * ‖U j‖ ^ 2 := by
  symm
  simp only [anchorWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro side _
  simp

/-- Concrete version of Λ ≤ d I. Only incident weight upper bounds remain;
there is no positive-definite inverse premise and the vector norm is Euclidean. -/
theorem dirichlet_le_diagonal {α : Edge → ℝ} {d : ℝ}
    (hα : ∀ e, 0 ≤ α e) (hd : ∀ j, anchorWeight α j ≤ d)
    (U : Fin 9 → Point) : dirichletEnergy α U ≤ d * ∑ j, ‖U j‖ ^ 2 := by
  calc
    dirichletEnergy α U ≤ ∑ j, anchorWeight α j * ‖U j‖ ^ 2 := by
      rw [← boundary_trial_eq]
      exact dirichlet_le_boundary_trial hα U
    _ ≤ ∑ j, d * ‖U j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hd j) (sq_nonneg _)
    _ = d * ∑ j, ‖U j‖ ^ 2 := (Finset.mul_sum ..).symm

#check @dirichlet_relative_comparison
#print axioms dirichlet_relative_comparison
end N11Formalization.ResumeStressComparison
