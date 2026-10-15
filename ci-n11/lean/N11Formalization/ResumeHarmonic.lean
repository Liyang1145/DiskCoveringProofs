import N11Formalization.ResumeDirichlet

/-! A finite rational harmonic-extension certificate controls every boundary
configuration, not just the sampled coordinates at which a stress was found. -/
noncomputable section
namespace N11Formalization.ResumeHarmonic
open ResumeNetwork ResumeDirichlet

/-- Lift nine boundary vectors by a scalar matrix with 22 free-node rows. -/
def lift (H : Free → Fin 9 → ℝ) (U : Fin 9 → Point) (v : Free) : Point :=
  ∑ j, H v j • U j

def coeff (H : Free → Fin 9 → ℝ) : Edge → Fin 9 → ℝ
  | .inl (i, side), j => H (.inl ⟨i.val, by omega⟩) j -
      (if j = anchorIndex i side then 1 else 0)
  | .inr (f, k), j => H (.inl (face f k)) j - H (.inr f) j

/-- The exported coefficients represent the actual graph edges, including
boundary incidence signs; no independently supplied edge-vector premise. -/
theorem edge_lift (H : Free → Fin 9 → ℝ) (U : Fin 9 → Point) (e : Edge) :
    edgeVector U (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f)) e =
      ∑ j, coeff H e j • U j := by
  rcases e with ⟨i, side⟩ | ⟨f, k⟩
  · simp [edgeVector, lift, coeff, sub_smul, Finset.sum_sub_distrib]
  · simp [edgeVector, lift, coeff, sub_smul, Finset.sum_sub_distrib]

/-- Scalar balance in each boundary column implies vector balance for every U. -/
theorem balance_of_columns (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (U : Fin 9 → Point) (v : Free) :
    ∑ e, (α e * incidence e v) •
      edgeVector U (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f)) e = 0 := by
  simp_rw [edge_lift, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hbal, zero_smul]
  simp

/-- Actual oracle consumer: a finite scalar balance certificate gives a valid
lower bound for every unit-bounded boundary configuration. -/
theorem harmonic_energy_le_oracle (α : Edge → ℝ) (H : Free → Fin 9 → ℝ)
    (hα : ∀ e, 0 ≤ α e) (hs : ∑ e, α e = 1)
    (hbal : ∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0)
    (U : Fin 9 → Point) (hU : ∀ j, ‖U j‖ ≤ 1) :
    (∑ e, α e * ‖∑ j, coeff H e j • U j‖ ^ 2) ≤ V2 U := by
  have h := balanced_energy_le_oracle (fun i => lift H U (.inl i))
    (fun f => lift H U (.inr f)) hU hα hs (balance_of_columns α H hbal U)
  simpa only [energy, edgeLength_eq_norm, edge_lift] using h

#check @harmonic_energy_le_oracle
#print axioms harmonic_energy_le_oracle
end N11Formalization.ResumeHarmonic
