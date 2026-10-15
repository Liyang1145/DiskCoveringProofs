/-
  SortingLift.V4.lean — the cyclic sorted lift of the nine directions (V4)
  (evidence draft 2026-10-01, producer = ownership-topology; NOT kernel-checked by the
  producer — the Lead owns the serial Lean slot.  NEW file; V1/V2/V3 are not edited.)

  ## V4 repairs gate3 (lead/sortinglift-gate3): header only, math untouched

  V3 replaced the header but left the previous header prose in the file as bare Markdown,
  outside any comment ⇒ parser cascade.  Two lessons are encoded here: (a) a header
  auto-prepend/replace must re-check the comment delimiters, not only the imports; and
  (b) the delimiter sequences themselves must never appear inside the prose of a comment
  block, because Lean block comments nest and the first close-delimiter encountered ends the
  comment.  This V4 header therefore writes them as "close-delimiter"/"open-delimiter".
  The code below is V3 verbatim.

  ## What is open (explicit scope — this file is NOT "everything except structure")

  SortingLift CONSTRUCTS the sorted cyclic lift, so the consumer side no longer has to assume
  the bookkeeping horder, psi 9 = psi 0 + 2*pi, alpha 9 = alpha 0.  It does NOT settle:

    * the source-side distinctness of the nine site directions (cover + essentiality);
    * the root count no-bubble/uniqueness statement (ANALYSIS-V3.md section 1.3) — still
      paper, with its own audit-pending inputs;
    * the canonical two-fan / 33-row topology (section 4 lane) and the C450 / two-hub inputs;
    * Covers c r ⇒ circle cover (an in-tree reduction theorem exists per the Lead, not yet
      wired here).

  ## Content

    * sortedPerm / lift from Mathlib's probed Fin.Tuple API (Tuple.sort :79,
      Tuple.monotone_sort :94); lift_apply, lift_mono, lift_nine (wrap identity
      lift θ 9 = lift θ 0 + 2*pi);
    * lift_strict composes BOTH injectivities (gate1 fix): (sortedPerm θ).injective
      (hinj heq) removes the permutation after hinj heq removed θ, then congrArg Fin.val
      gives i = j;
    * windows split by endpoint convention (gate2 fix): lift_lt_wrap_Ico ([a, a + 2*pi)),
      lift_lt_wrap_Ioc ((a, a + 2*pi], matching circleAngle ∈ Set.Ioc (−π) π, so ±π cannot
      appear as two different phases), and lift_circleAngle_lt_wrap, which discharges the
      window hypothesis for the actual site directions via circleAngle_mem_Ioc;
    * imports include N11Formalization.Geometry.DiskToArc (where centerDir is defined, :84).

  STILL EXPLICIT: injectivity of the nine directions (source-side, from cover + essentiality).

  No sorry, no custom axiom, no native_decide.
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.ArcCovering
import N11Formalization.Geometry.DiskToArc

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.SortingLift

open N11Formalization

noncomputable section

/-- The permutation putting the nine directions in increasing order. -/
def sortedPerm (θ : Fin 9 → ℝ) : Equiv.Perm (Fin 9) := Tuple.sort θ

/-- The lifted sorted direction sequence: `0..8` are the sorted directions, `9` is the wrapped
copy of `0`. -/
def lift (θ : Fin 9 → ℝ) : ℕ → ℝ := fun k =>
  if hk : k < 9 then θ (sortedPerm θ ⟨k, hk⟩)
  else θ (sortedPerm θ 0) + 2 * Real.pi

theorem lift_apply {θ : Fin 9 → ℝ} {k : ℕ} (hk : k < 9) :
    lift θ k = θ (sortedPerm θ ⟨k, hk⟩) := by
  rw [lift, dif_pos hk]

/-- Sortedness of the lift on `0..8`. -/
theorem lift_mono {θ : Fin 9 → ℝ} : ∀ i j : ℕ, i ≤ j → j < 9 → lift θ i ≤ lift θ j := by
  intro i j hij hj
  have hi : i < 9 := by omega
  rw [lift_apply hi, lift_apply hj]
  exact Tuple.monotone_sort θ hij

/-- Strict sortedness when the nine directions are pairwise distinct.  Both injectivities are
composed: `θ`'s removes `θ`, the permutation's removes the permutation. -/
theorem lift_strict {θ : Fin 9 → ℝ} (hinj : Function.Injective θ) :
    ∀ i j : ℕ, i < j → j < 9 → lift θ i < lift θ j := by
  intro i j hij hj
  have hi : i < 9 := by omega
  rcases lt_or_eq_of_le (lift_mono i j hij.le hj) with hlt | heq
  · exact hlt
  · exfalso
    rw [lift_apply hi, lift_apply hj] at heq
    have hijFin : (⟨i, hi⟩ : Fin 9) = ⟨j, hj⟩ := (sortedPerm θ).injective (hinj heq)
    exact absurd (congrArg Fin.val hijFin) hij.ne

/-- The wrap identity. -/
theorem lift_nine (θ : Fin 9 → ℝ) : lift θ 9 = lift θ 0 + 2 * Real.pi := by
  have h9 : lift θ 9 = θ (sortedPerm θ 0) + 2 * Real.pi := by
    rw [lift, dif_neg (by omega : ¬ (9 : ℕ) < 9)]
  have h0 : lift θ 0 = θ (sortedPerm θ 0) := by
    rw [lift_apply (by omega : (0 : ℕ) < 9)]
    exact congrArg (fun a : Fin 9 => θ (sortedPerm θ a)) (Fin.ext rfl)
  rw [h9, h0]

/-- **Wrap gap, `Ico` window** `[a, a + 2π)`: every lifted direction is below `lift θ 0 + 2π`. -/
theorem lift_lt_wrap_Ico {θ : Fin 9 → ℝ} {a : ℝ}
    (hwin : ∀ k : Fin 9, θ k ∈ Set.Ico a (a + 2 * Real.pi)) {k : ℕ} (hk : k < 9) :
    lift θ k < lift θ 0 + 2 * Real.pi := by
  have hk' : lift θ k = θ (sortedPerm θ ⟨k, hk⟩) := lift_apply hk
  have h0 : lift θ 0 = θ (sortedPerm θ ⟨0, by omega⟩) := lift_apply (by omega)
  have hk_lt : θ (sortedPerm θ ⟨k, hk⟩) < a + 2 * Real.pi := (hwin _).2
  have h0_ge : a ≤ θ (sortedPerm θ ⟨0, by omega⟩) := (hwin _).1
  rw [hk', h0]
  linarith

/-- **Wrap gap, `Ioc` window** `(a, a + 2π]` — the convention matching `circleAngle`.  The
left end is strict, and the right end is the same circle point, so the gap is still strictly
positive. -/
theorem lift_lt_wrap_Ioc {θ : Fin 9 → ℝ} {a : ℝ}
    (hwin : ∀ k : Fin 9, θ k ∈ Set.Ioc a (a + 2 * Real.pi)) {k : ℕ} (hk : k < 9) :
    lift θ k < lift θ 0 + 2 * Real.pi := by
  have hk' : lift θ k = θ (sortedPerm θ ⟨k, hk⟩) := lift_apply hk
  have h0 : lift θ 0 = θ (sortedPerm θ ⟨0, by omega⟩) := lift_apply (by omega)
  have hk_le : θ (sortedPerm θ ⟨k, hk⟩) ≤ a + 2 * Real.pi := (hwin _).2
  have h0_gt : a < θ (sortedPerm θ ⟨0, by omega⟩) := (hwin _).1
  rw [hk', h0]
  linarith

/-- **Window discharged for the actual site directions.**  `circleAngle` takes values in
`Set.Ioc (-π) π`, so the `Ioc` wrap lemma applies with no window hypothesis left. -/
theorem lift_circleAngle_lt_wrap {c : ℕ → Point} {k : ℕ} (hk : k < 9) :
    lift (fun j : Fin 9 => circleAngle (centerDir (c j.val))) k
      < lift (fun j : Fin 9 => circleAngle (centerDir (c j.val))) 0 + 2 * Real.pi := by
  refine lift_lt_wrap_Ioc (a := -Real.pi) ?_ hk
  intro j
  have h := circleAngle_mem_Ioc (centerDir (c j.val))
  have hp : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rwa [hp]

/-! ## Core interface printout -/

#check @N11Formalization.SortingLift.sortedPerm
#check @N11Formalization.SortingLift.lift
#check @N11Formalization.SortingLift.lift_apply
#check @N11Formalization.SortingLift.lift_mono
#check @N11Formalization.SortingLift.lift_strict
#check @N11Formalization.SortingLift.lift_nine
#check @N11Formalization.SortingLift.lift_lt_wrap_Ico
#check @N11Formalization.SortingLift.lift_lt_wrap_Ioc
#check @N11Formalization.SortingLift.lift_circleAngle_lt_wrap

#print axioms N11Formalization.SortingLift.lift_mono
#print axioms N11Formalization.SortingLift.lift_strict
#print axioms N11Formalization.SortingLift.lift_nine
#print axioms N11Formalization.SortingLift.lift_lt_wrap_Ico
#print axioms N11Formalization.SortingLift.lift_lt_wrap_Ioc
#print axioms N11Formalization.SortingLift.lift_circleAngle_lt_wrap

end

end N11Formalization.SortingLift
