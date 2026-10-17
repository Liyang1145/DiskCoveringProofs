import N11Formalization.C921Sem

/-!
# ResumeGlobal: corrected global consumer (energy + local leaves, target V2 ≥ R²)

Replaces the over-strong `hglob : ∀ y, V2 y > T²` (false at the optimum: local leaves
only give V2 ≥ R*² + q²/1e5, equality at the extremal point) by a MIXED cover:
energy leaves (V2 > T², with R ≤ T) and local leaves (V2 ≥ R² + q ≥ R²).
Generic in the leaf index types; no symmetry, no data.
-/

namespace N11Formalization.ResumeGlobal
open N11Formalization N11Formalization.C921Sem

/-- Mixed-cover global bound: V2 ≥ R² on the whole closed simplex. -/
theorem global_ge_sq_of_mixed {V2 : (Fin 8 → ℝ) → ℝ} {R T : ℝ}
    {ιE ιL : Type} (domE : ιE → (Fin 8 → ℝ) → Prop) (domL : ιL → (Fin 8 → ℝ) → Prop)
    (qL : ιL → ℝ)
    (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hE : ∀ ℓ y, domE ℓ y → InSimplex y → V2 y > T ^ 2)
    (hL : ∀ ℓ y, domL ℓ y → InSimplex y → V2 y ≥ R ^ 2 + qL ℓ ^ 2 / 100000)
    (hcover : ∀ y, InSimplex y → (∃ ℓ, domE ℓ y) ∨ (∃ ℓ, domL ℓ y)) :
    ∀ y, InSimplex y → R ^ 2 ≤ V2 y := by
  intro y hy
  rcases hcover y hy with ⟨ℓ, h⟩ | ⟨ℓ, h⟩
  · have := hE ℓ y h hy
    nlinarith
  · have := hL ℓ y h hy
    have : 0 ≤ qL ℓ ^ 2 / 100000 := by positivity
    linarith

/-- Corrected `hbound`: C923 slot + global `V2 ≥ R²` ⇒ every cover radius ≥ R. -/
theorem hbound_of_ge_sq {V2 : (Fin 8 → ℝ) → ℝ} {R : ℝ} (hR0 : 0 ≤ R)
    (hc923 : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      ∃ y : Fin 8 → ℝ, InSimplex y ∧ V2 y ≤ r ^ 2)
    (hglob : ∀ y, InSimplex y → R ^ 2 ≤ V2 y)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hcov : Covers c r) : R ≤ r := by
  obtain ⟨y, hy, hV⟩ := hc923 r c hr hcov
  have h := (hglob y hy).trans hV
  nlinarith

/-- Corrected terminal node at the exact root `Rstar S` (not sInf). -/
theorem n11_main_of_mixed (S : C891RootSpec) {V2 : (Fin 8 → ℝ) → ℝ}
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S))
    (hR0 : 0 ≤ Rstar S)
    (hc923 : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      ∃ y : Fin 8 → ℝ, InSimplex y ∧ V2 y ≤ r ^ 2)
    (hglob : ∀ y, InSimplex y → (Rstar S) ^ 2 ≤ V2 y) :
    N11MainStatement (Rstar S) :=
  n11_main_conditional S hattain
    (fun r c hr hc => hbound_of_ge_sq hR0 hc923 hglob r c hr hc)

end N11Formalization.ResumeGlobal

#print axioms N11Formalization.ResumeGlobal.global_ge_sq_of_mixed
#print axioms N11Formalization.ResumeGlobal.n11_main_of_mixed
