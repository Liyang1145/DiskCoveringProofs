import N11Formalization.Definitions

/-! Perturbation and rigorous dense-class reduction for arbitrary disk covers.
No general-position assertion is assumed silently. Distinctness is proved dense.
This does not prove a lower bound on the distinct class. -/
set_option autoImplicit false
namespace N11Formalization.CoverDensity
open N11Formalization

/-- Uniform perturbation of the eleven centers enlarges radius by at most epsilon. -/
theorem covers_perturb {c d : Fin 11 → Point} {r ε : ℝ}
    (hc : Covers c r) (hcd : ∀ i, dist (c i) (d i) ≤ ε) : Covers d (r + ε) := by
  intro x hx
  obtain ⟨i, hi⟩ := hc x hx
  exact ⟨i, (dist_triangle x (c i) (d i)).trans (add_le_add hi (hcd i))⟩

/-- A lower bound on any explicitly dense class extends to arbitrary centers.
The generic-class theorem is only needed for radii strictly below r0. -/
theorem lower_bound_of_dense_class (G : Set (Fin 11 → Point)) (hG : Dense G)
    (R r0 : ℝ) (hR0 : R ≤ r0)
    (hgood : ∀ (r : ℝ) (c : Fin 11 → Point), c ∈ G → 0 ≤ r → r < r0 →
      Covers c r → R ≤ r)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hc : Covers c r) : R ≤ r := by
  by_contra hn
  have hrR : r < R := lt_of_not_ge hn
  let ε : ℝ := (R - r) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨d, hdG, hcd⟩ := hG.exists_dist_lt c hε
  have hpert : Covers d (r + ε) := covers_perturb hc (fun i =>
    ((dist_le_pi_dist c d i).trans hcd.le))
  have hsmall : r + ε < r0 := by dsimp [ε]; linarith
  have hnonneg : 0 ≤ r + ε := add_nonneg hr hε.le
  have hbound := hgood (r + ε) d hdG hnonneg hsmall hpert
  dsimp [ε] at hbound
  linarith

/-- Finite lists of pairwise distinct planar points can approximate every list. -/
theorem exists_injective_near (n : ℕ) (c : Fin n → Point) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : Fin n → Point, Function.Injective d ∧ ∀ i, dist (c i) (d i) < ε := by
  classical
  induction n with
  | zero =>
      exact ⟨c, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨d, hd, hclose⟩ := ih (fun i => c i.succ)
      have hD : Dense ((Set.univ : Set Point) \ Set.range d) :=
        dense_univ.sdiff_finite (Set.finite_range d)
      obtain ⟨x, hx, hcx⟩ := hD.exists_dist_lt (c 0) hε
      have hxnot : x ∉ Set.range d := hx.2
      refine ⟨Fin.cons x d, ?_, ?_⟩
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => rfl
            | succ j =>
                have hxd : x = d j := by simpa using hij
                exact False.elim (hxnot ⟨j, hxd.symm⟩)
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                have hdx : d i = x := by simpa using hij
                exact False.elim (hxnot ⟨i, hdx⟩)
            | succ j =>
                have hij' : d i = d j := by simpa using hij
                exact congrArg Fin.succ (hd hij')
      · intro i
        cases i using Fin.cases with
        | zero => simpa using hcx
        | succ i => simpa using hclose i

/-- Repeated centers are no obstruction to a lower-bound proof: distinct configurations
are dense in the exact sup metric used by the perturbation consumer. -/
theorem dense_injective_centers : Dense {c : Fin 11 → Point | Function.Injective c} := by
  intro c
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hclose⟩ := exists_injective_near 11 c ε hε
  exact ⟨d, hd, (dist_pi_lt_iff hε).mpr hclose⟩

/-- Actual specialization removes the repeated-center class without a limit gap. -/
theorem lower_bound_of_injective_centers (R r0 : ℝ) (hR0 : R ≤ r0)
    (hgood : ∀ (r : ℝ) (c : Fin 11 → Point), Function.Injective c → 0 ≤ r → r < r0 →
      Covers c r → R ≤ r)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hc : Covers c r) : R ≤ r :=
  lower_bound_of_dense_class _ dense_injective_centers R r0 hR0 hgood r c hr hc

end N11Formalization.CoverDensity

#print N11Formalization.CoverDensity.lower_bound_of_dense_class
#print N11Formalization.CoverDensity.exists_injective_near
#print N11Formalization.CoverDensity.dense_injective_centers
#print N11Formalization.CoverDensity.lower_bound_of_injective_centers
#print axioms N11Formalization.CoverDensity.covers_perturb
#print axioms N11Formalization.CoverDensity.lower_bound_of_dense_class
#print axioms N11Formalization.CoverDensity.exists_injective_near
#print axioms N11Formalization.CoverDensity.dense_injective_centers
#print axioms N11Formalization.CoverDensity.lower_bound_of_injective_centers
