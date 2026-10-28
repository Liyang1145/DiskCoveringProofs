import N11Formalization.ResumeDirichlet

noncomputable section
namespace N11Formalization.ResumeAdaptiveRoot
open ResumeNetwork ResumeDirichlet

/-- A signed equilibrium perturbation preserves the very same free-node minimizer
at the base anchors. This is not a claim of linearity away from those anchors. -/
theorem balance_add {α δ : Edge → ℝ} {U : Fin 9 → Point}
    {C Z : Fin 11 → Point}
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hd : ∀ v : Free, ∑ e, (δ e * incidence e v) • edgeVector U C Z e = 0) :
    ∀ v : Free, ∑ e, ((α e + δ e) * incidence e v) • edgeVector U C Z e = 0 := by
  intro v
  simp_rw [add_mul, add_smul, Finset.sum_add_distrib, ha v, hd v]
  simp

/-- Only carrying edges need have the common length. Zero-weight slack edges
are allowed and no stationarity premise is hidden in this energy identity. -/
theorem energy_eq_radius_sq {α : Edge → ℝ} {U : Fin 9 → Point}
    {C Z : Fin 11 → Point} {R : ℝ}
    (hs : ∑ e, α e = 1)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = R ^ 2) :
    energy α U C Z = R ^ 2 := by
  unfold energy
  calc
    _ = ∑ e, α e * R ^ 2 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : α e = 0
      · simp [he]
      · rw [hl e he]
    _ = R ^ 2 := by rw [← Finset.sum_mul, hs, one_mul]

/-- Exact base-root identity for adaptive stress: signed perturbations with
zero sum and zero free force preserve the root energy, provided they introduce
no new carrying edge. No inverse or uniqueness hypothesis is used. -/
theorem adaptive_root_value {α δ : Edge → ℝ} {U : Fin 9 → Point}
    {C Z : Fin 11 → Point} {R : ℝ}
    (hpos : ∀ e, 0 ≤ α e + δ e)
    (hs : ∑ e, α e = 1) (hds : ∑ e, δ e = 0)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hd : ∀ v : Free, ∑ e, (δ e * incidence e v) • edgeVector U C Z e = 0)
    (hsupport : ∀ e, α e = 0 → δ e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = R ^ 2) :
    dirichletEnergy (fun e => α e + δ e) U = R ^ 2 := by
  rw [dirichlet_eq_of_node_balance C Z hpos (balance_add ha hd)]
  apply energy_eq_radius_sq
  · simp [Finset.sum_add_distrib, hs, hds]
  · intro e he
    apply hl e
    intro haz
    exact he (by simp [haz, hsupport e haz])

#print axioms adaptive_root_value
end N11Formalization.ResumeAdaptiveRoot
