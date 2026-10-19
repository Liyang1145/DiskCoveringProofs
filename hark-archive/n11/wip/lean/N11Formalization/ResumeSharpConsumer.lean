import N11Formalization.Conditional.RootSpec

/-! Source-neutral sharp consumer. Domain is abstract so it cannot silently hard-code
an erroneous simplex chart. Relaxation is needed only for hypothetical smaller covers;
no large-radius `top` oracle witness and no strict bound at the optimum are required. -/
namespace N11Formalization.ResumeSharpConsumer

theorem lower_bound_of_small_cover_relaxation {Ω : Type*} (D : Set Ω)
    (V2 : Ω → ℝ) (R r0 : ℝ) (hRr0 : R ≤ r0)
    (hrelax : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → r < r0 → Covers c r →
      ∃ y ∈ D, V2 y ≤ r ^ 2)
    (hglob : ∀ y ∈ D, R ^ 2 ≤ V2 y)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hc : Covers c r) : R ≤ r := by
  by_contra h
  have hrR : r < R := lt_of_not_ge h
  obtain ⟨y, hy, hv⟩ := hrelax r c hr (hrR.trans_le hRr0) hc
  have hb := (hglob y hy).trans hv
  nlinarith

/-- At the same exact root S. No assumptions are omitted from this consumer type. -/
theorem main_of_small_cover_relaxation (S : C891RootSpec) {Ω : Type*}
    (D : Set Ω) (V2 : Ω → ℝ) (r0 : ℝ) (hRr0 : Rstar S ≤ r0)
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S))
    (hrelax : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → r < r0 → Covers c r →
      ∃ y ∈ D, V2 y ≤ r ^ 2)
    (hglob : ∀ y ∈ D, (Rstar S) ^ 2 ≤ V2 y) :
    N11MainStatement (Rstar S) :=
  n11_main_conditional S hattain
    (lower_bound_of_small_cover_relaxation D V2 (Rstar S) r0 hRr0 hrelax hglob)

/-- Sharp mixing, independent of a coordinate convention for D. -/
theorem global_of_mixed_domains {Ω E L : Type*} (D : Set Ω)
    (domE : E → Set Ω) (domL : L → Set Ω) (V2 : Ω → ℝ) (R T : ℝ)
    (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hE : ∀ e y, y ∈ D → y ∈ domE e → T ^ 2 < V2 y)
    (hL : ∀ l y, y ∈ D → y ∈ domL l → R ^ 2 ≤ V2 y)
    (hcover : ∀ y ∈ D, (∃ e, y ∈ domE e) ∨ (∃ l, y ∈ domL l)) :
    ∀ y ∈ D, R ^ 2 ≤ V2 y := by
  intro y hy
  rcases hcover y hy with ⟨e, he⟩ | ⟨l, hl⟩
  · have h := hE e y hy he
    nlinarith
  · exact hL l y hy hl

#check @main_of_small_cover_relaxation
#print axioms main_of_small_cover_relaxation
#print axioms global_of_mixed_domains
end N11Formalization.ResumeSharpConsumer
