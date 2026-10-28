import N11Formalization.C923Gate

/-! Exact diagnostics of old consumer interfaces; no claim that the main theorem is false.
The old strict-global lower bound cannot coexist with attainment and its own relaxation.
The old Fin8 sum=1 domain also excludes the uniform reduced nine-deficit vector. -/
namespace N11Formalization.ResumeInterfaceAudit
open N11Formalization.C921Sem

/-- Applies in particular to the old n11_main_of_C923 assumptions. -/
theorem strict_global_incompatible_with_attainment
    {R T : ℝ} {V2 : (Fin 8 → ℝ) → ℝ}
    (hattain : ∃ c : Fin 11 → Point, Covers c R)
    (hc923 : C923Gate.HC923Slot V2)
    (hRT : R ≤ T)
    (hglob : ∀ y, InSimplex y → T ^ 2 < V2 y) : False := by
  obtain ⟨c, hc⟩ := hattain
  have hR0 : 0 ≤ R := hc.nonneg
  obtain ⟨y, hy, hv⟩ := hc923 R c hR0 hc
  have hg := hglob y hy
  nlinarith

/-- A concrete legal reduced-coordinate simplex interior point. -/
theorem uniform_reduced_deficits :
    (∀ i : Fin 8, 0 ≤ (fun _ : Fin 8 => (1 / 9 : ℝ)) i) ∧
    (∑ i : Fin 8, (fun _ : Fin 8 => (1 / 9 : ℝ)) i) ≤ 1 := by
  constructor
  · intro i; norm_num
  · norm_num

/-- Exact counterexample to identifying the current `InSimplex` with the reduced
nine-width deficit simplex. The source identification itself is audited separately. -/
theorem uniform_reduced_not_old_simplex :
    ¬ InSimplex (fun _ : Fin 8 => (1 / 9 : ℝ)) := by
  intro h
  have hs := h.2
  norm_num at hs

#print strict_global_incompatible_with_attainment
#print axioms strict_global_incompatible_with_attainment
#print axioms uniform_reduced_not_old_simplex
end N11Formalization.ResumeInterfaceAudit
