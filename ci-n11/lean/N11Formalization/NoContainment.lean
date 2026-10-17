/-
  NoContainment.V2.lean — geometric source of `hgap`, with the ORDER hypothesis made explicit
  (evidence draft 2026-10-01, producer = ownership-topology; **NOT kernel-checked by the
  producer** — the Lead owns the serial Lean slot.  NEW file; V1 is not edited.)

  ## Bearing correction (Lead, 2026-10-01): the order hypothesis was missing

  V1 (`NoContainment.V1.lean`) stated `endpoints_of_gap_le` and the two
  `gap_gt_abs_sub_of_…_no_containment` lemmas **without** a direction-order hypothesis, and
  they are **false** as stated (not merely unproved).  The Lead's counterexample, verbatim:

  * take `ψ i = 1`, `ψ (i+1) = 0`, `α i = α (i+1) = 0`.  Then the gap is `g = −1` and
    `h : g ≤ α (i+1) − α i` reads `−1 ≤ 0`, which is true, but the conclusion's second
    conjunct `R i ≤ R (i+1)` reads `1 ≤ 0`, false.  (Indeed
    `R (i+1) − R i = g + α (i+1) − α i`, so `R i ≤ R (i+1)` needs `g ≥ α i − α (i+1)`, which
    follows from `g ≤ α (i+1) − α i` only together with `g ≥ 0`.)
  * the same data (ψ's reversed, half-widths zero) gives two **singleton** caps at different
    angles: both containment statements are false, so both `hno1`, `hno2` hold, yet the
    conclusion `|α i − α (i+1)| < g` reads `0 < −1`, false.

  So the implication "no containment ⇒ gap dominates the half-width difference" is *not* a
  statement about an unordered pair of directions: it requires the **sorted/lifted order**
  `ψ i ≤ ψ (i+1)` (equivalently `g ≥ 0`), which is exactly the hypothesis that the geometric
  setting supplies (the nine directions are taken in cyclic order in a lift).  V2 adds
  `horder : ψ i ≤ ψ (i + 1)` to every lemma whose input is a *one-sided* gap inequality, and
  the proofs are then honest linear arithmetic.  No `linarith` is used to "prove" the false
  V1 statements.

  Which lemmas need the order and which do not:

  * `interval_subset_of_endpoint_le` — needs **no** order: its input is already the pair of
    lifted endpoint inequalities;
  * `cap_subset_of_interval_subset` — needs **no** order: no directions occur;
  * `endpoints_of_gap_le`, `gap_gt_abs_sub_of_no_containment`,
    `gap_gt_abs_sub_of_cap_no_containment`, `cap_subset_of_gap_le` — **need** `horder`.

  (Cross-check: the gated consumer side takes the *symmetric* hypothesis
  `|α i − α (i+1)| < ψ (i+1) − ψ i`, which implies `g > 0`, so `EndpointOrder.lean` and the
  frozen `EndpointInterval.V2-frozen.lean` are unaffected — their statements already carry the
  order implicitly.  Only V1's one-sided-gap lemmas were unsound.)

  ## V3 repairs gate2 of this file (Lead's log: math of the first three lemmas green,
  ## L116/118/131 failed to infer the `L`/`R` *functions*)

  `cap_subset_of_interval_subset`'s implicit `L R : ℕ → ℝ` (and `i j`) occur only inside its
  *hypotheses*' types (`… ↔ InPeriodicInterval (L i) (R i) t`), so when the call's expected
  result is a statement about `dist`/`circleMap` alone, Lean cannot solve the higher-order
  unification `L i ≡ ψ i − α i`.  V3 passes them explicitly at all call sites:
  `(L := fun k => ψ k - α k) (R := fun k => ψ k + α k)`, and `(i := i) (j := i + 1)` forward /
  `(i := i + 1) (j := i)` in the reverse branch (with `hcapI`, `hcapJ` swapped there), plus
  explicit `L₁ R₁ L₂ R₂` at the `interval_subset_of_endpoint_le` sites.  Math unchanged.

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.ArcCovering

set_option linter.unusedVariables false

namespace N11Formalization.NoContainment

open N11Formalization

/-- Periodic-interval membership (self-contained twin; same shape as the consumer side). -/
def InPeriodicInterval (L R t : ℝ) : Prop :=
  ∃ m : ℤ, L + m * (2 * Real.pi) ≤ t ∧ t ≤ R + m * (2 * Real.pi)

/-- **EASY direction of interval containment.**  Input is the pair of lifted endpoint
inequalities, so no direction order is needed. -/
theorem interval_subset_of_endpoint_le {L₁ R₁ L₂ R₂ : ℝ} (hL : L₂ ≤ L₁) (hR : R₁ ≤ R₂) :
    ∀ t, InPeriodicInterval L₁ R₁ t → InPeriodicInterval L₂ R₂ t := by
  rintro t ⟨m, h1, h2⟩
  exact ⟨m, by linarith, by linarith⟩

/-- **EASY direction at cap level.**  No directions occur, so no order hypothesis is needed. -/
theorem cap_subset_of_interval_subset {c : ℕ → Point} {r : ℝ} {L R : ℕ → ℝ} {i j : ℕ}
    (hcapI : ∀ t, dist (circleMap t) (c i) ≤ r ↔ InPeriodicInterval (L i) (R i) t)
    (hcapJ : ∀ t, dist (circleMap t) (c j) ≤ r ↔ InPeriodicInterval (L j) (R j) t)
    (hsub : ∀ t, InPeriodicInterval (L i) (R i) t → InPeriodicInterval (L j) (R j) t) :
    ∀ x : Point, ‖x‖ = 1 → dist x (c i) ≤ r → dist x (c j) ≤ r := by
  intro x hx hd
  have hx' : circleMap (circleAngle x) = x := circleMap_circleAngle x hx
  rw [← hx'] at hd ⊢
  exact (hcapJ _).mpr (hsub _ ((hcapI _).mp hd))

/-- **One-sided gap bound ⇒ lifted endpoint containment, WITH the direction order.**
`horder : ψ i ≤ ψ (i+1)` is exactly `0 ≤ g`, the missing hypothesis in V1. -/
theorem endpoints_of_gap_le {ψ α : ℕ → ℝ} {i : ℕ} (horder : ψ i ≤ ψ (i + 1))
    (h : ψ (i + 1) - ψ i ≤ α (i + 1) - α i) :
    ψ (i + 1) - α (i + 1) ≤ ψ i - α i ∧ ψ i + α i ≤ ψ (i + 1) + α (i + 1) :=
  ⟨by linarith, by linarith⟩

/-- **Geometric source of `hgap` (interval form), with the order hypothesis.**  No containment
in either direction (essentiality) plus the sorted lift forces the half-width difference to be
dominated by the gap. -/
theorem gap_gt_abs_sub_of_no_containment {ψ α : ℕ → ℝ} {i : ℕ} (horder : ψ i ≤ ψ (i + 1))
    (hno1 : ¬ (∀ t, InPeriodicInterval (ψ i - α i) (ψ i + α i) t →
      InPeriodicInterval (ψ (i + 1) - α (i + 1)) (ψ (i + 1) + α (i + 1)) t))
    (hno2 : ¬ (∀ t, InPeriodicInterval (ψ (i + 1) - α (i + 1)) (ψ (i + 1) + α (i + 1)) t →
      InPeriodicInterval (ψ i - α i) (ψ i + α i) t)) :
    |α i - α (i + 1)| < ψ (i + 1) - ψ i := by
  have h1 : ¬ (ψ (i + 1) - ψ i ≤ α (i + 1) - α i) := by
    intro h
    exact hno1 (interval_subset_of_endpoint_le (L₁ := ψ i - α i) (R₁ := ψ i + α i)
      (L₂ := ψ (i + 1) - α (i + 1)) (R₂ := ψ (i + 1) + α (i + 1))
      (by linarith) (by linarith [h, horder]))
  have h2 : ¬ (ψ (i + 1) - ψ i ≤ α i - α (i + 1)) := by
    intro h
    exact hno2 (interval_subset_of_endpoint_le (L₁ := ψ (i + 1) - α (i + 1))
      (R₁ := ψ (i + 1) + α (i + 1)) (L₂ := ψ i - α i) (R₂ := ψ i + α i)
      (by linarith [h, horder]) (by linarith))
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **Geometric source of `hgap` (cap form), with the order hypothesis.**  The identification
hypotheses have the exact shape `EndpointInterval.V3` produces; the two containment negations
are the essentiality interface (the `16β < 2π` measure count), still explicit. -/
theorem gap_gt_abs_sub_of_cap_no_containment {c : ℕ → Point} {r : ℝ} {ψ α : ℕ → ℝ} {i : ℕ}
    (horder : ψ i ≤ ψ (i + 1))
    (hcapI : ∀ t, dist (circleMap t) (c i) ≤ r ↔
      InPeriodicInterval (ψ i - α i) (ψ i + α i) t)
    (hcapJ : ∀ t, dist (circleMap t) (c (i + 1)) ≤ r ↔
      InPeriodicInterval (ψ (i + 1) - α (i + 1)) (ψ (i + 1) + α (i + 1)) t)
    (hno1 : ¬ (∀ x : Point, ‖x‖ = 1 → dist x (c i) ≤ r → dist x (c (i + 1)) ≤ r))
    (hno2 : ¬ (∀ x : Point, ‖x‖ = 1 → dist x (c (i + 1)) ≤ r → dist x (c i) ≤ r)) :
    |α i - α (i + 1)| < ψ (i + 1) - ψ i := by
  refine gap_gt_abs_sub_of_no_containment horder ?_ ?_
  · intro hsub
    exact hno1 (cap_subset_of_interval_subset (L := fun k => ψ k - α k)
      (R := fun k => ψ k + α k) (i := i) (j := i + 1) hcapI hcapJ hsub)
  · intro hsub
    exact hno2 (cap_subset_of_interval_subset (L := fun k => ψ k - α k)
      (R := fun k => ψ k + α k) (i := i + 1) (j := i) hcapJ hcapI hsub)

/-- **Positive direction, with the order hypothesis** (for the record): if the gap dominates
the half-width difference in the ordered lift, the cap of `i` is contained in that of `i + 1`. -/
theorem cap_subset_of_gap_le {c : ℕ → Point} {r : ℝ} {ψ α : ℕ → ℝ} {i : ℕ}
    (horder : ψ i ≤ ψ (i + 1))
    (hcapI : ∀ t, dist (circleMap t) (c i) ≤ r ↔
      InPeriodicInterval (ψ i - α i) (ψ i + α i) t)
    (hcapJ : ∀ t, dist (circleMap t) (c (i + 1)) ≤ r ↔
      InPeriodicInterval (ψ (i + 1) - α (i + 1)) (ψ (i + 1) + α (i + 1)) t)
    (h : ψ (i + 1) - ψ i ≤ α (i + 1) - α i) :
    ∀ x : Point, ‖x‖ = 1 → dist x (c i) ≤ r → dist x (c (i + 1)) ≤ r := by
  obtain ⟨hL, hR⟩ := endpoints_of_gap_le horder h
  exact cap_subset_of_interval_subset (L := fun k => ψ k - α k) (R := fun k => ψ k + α k)
    (i := i) (j := i + 1) hcapI hcapJ
    (interval_subset_of_endpoint_le (L₁ := ψ i - α i) (R₁ := ψ i + α i)
      (L₂ := ψ (i + 1) - α (i + 1)) (R₂ := ψ (i + 1) + α (i + 1)) hL hR)

/-! ## Core interface printout -/

#check @N11Formalization.NoContainment.InPeriodicInterval
#check @N11Formalization.NoContainment.interval_subset_of_endpoint_le
#check @N11Formalization.NoContainment.cap_subset_of_interval_subset
#check @N11Formalization.NoContainment.endpoints_of_gap_le
#check @N11Formalization.NoContainment.gap_gt_abs_sub_of_no_containment
#check @N11Formalization.NoContainment.gap_gt_abs_sub_of_cap_no_containment
#check @N11Formalization.NoContainment.cap_subset_of_gap_le

#print axioms N11Formalization.NoContainment.interval_subset_of_endpoint_le
#print axioms N11Formalization.NoContainment.cap_subset_of_interval_subset
#print axioms N11Formalization.NoContainment.endpoints_of_gap_le
#print axioms N11Formalization.NoContainment.gap_gt_abs_sub_of_no_containment
#print axioms N11Formalization.NoContainment.gap_gt_abs_sub_of_cap_no_containment
#print axioms N11Formalization.NoContainment.cap_subset_of_gap_le

end N11Formalization.NoContainment
