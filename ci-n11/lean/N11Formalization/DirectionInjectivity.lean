/-
  DirectionInjectivity.V2.lean — the nine site directions are pairwise distinct (V2)
  (evidence draft 2026-10-01, producer = ownership-topology; **NOT kernel-checked by the
  producer** — the Lead owns the serial Lean slot.  NEW file; V1 is not edited.)

  ## V2 repairs gate1 (`lead/direction-injectivity-gate1.log`, exit 1)

  Gate1 was red at exactly two sites, L68 and L76, both inside `cap_nested_or_of_same_dir`,
  and the four downstream declarations inherited `sorryAx` from it
  (`c_ne_zero_of_covers` was already green with the standard three axioms):

    * L67 `rw [hc]` and L60/L73-74 `rw [hc']` were used to move between the raw centre `c`
      and its canonical form `‖c‖ • centerDir c`.  `rw` rewrites *every* subterm occurrence of
      the pattern, so the occurrence of `c` inside `‖c‖` became `‖‖c‖ • centerDir c‖` and the
      occurrence inside `centerDir c` became `centerDir (‖c‖ • centerDir c)`.  The gate log
      shows exactly this: the expected type was printed with
      `‖‖c‖ • centerDir c‖ ^ 2` and `centerDir (‖c‖ • centerDir c)`.

  V2 fix (the Lead's prescription): factor the nesting argument into a helper that never
  mentions a raw centre, `cap_nested_or_of_same_scaled_dir {c c' u s s' r}` with
  `hc : c = s • u`, `hc' : c' = s' • u`.  Both `cap_iff_cos_threshold` call sites then have
  their canonical arguments `s • u`, `s' • u` **already**, so no `rw` touches `‖c‖` or
  `centerDir c`; the only rewrites are on the *hypotheses* `hd : dist x c ≤ r` /
  `dist x c' ≤ r`, where `c` and `c'` occur as bare arguments (no compound occurrence to
  pollute).  The helper is applied at the single canonical instantiation
  `u := centerDir c`, `s := ‖c‖`, `s' := ‖c'‖`, with `hc'` obtained from
  `self_eq_norm_smul_centerDir hne'` by `simpa only [← hdir]`.

  ## What is NOT changed (deliberately)

  * the five declaration **names and full types are identical to V1** — in particular
    `circleAngle_injective_of_covers` keeps the consumer type
    `0 ≤ r → r < 1 → r ≤ 19/50 → (∀ k < 9, c k ≠ 0) →
     (∀ x, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r) →
     ∀ i j < 9, i ≠ j → circleAngle (centerDir (c i)) ≠ circleAngle (centerDir (c j))`;
  * the proofs of `centerDir_injective_of_no_containment`,
    `circleAngle_centerDir_injective_of_no_containment`, `circleAngle_injective_of_covers`,
    `c_ne_zero_of_covers` are V1 verbatim (gate1 reported no error in them; their `sorryAx`
    tag came only from the failing `cap_nested_or_of_same_dir`);
  * the `#check` / `#print axioms` interface printout is V1's, plus one line for the helper.

  ## Scope / remaining (unchanged from V1)

  STILL OPEN: the `Fin 9` bookkeeping bridge from `circleAngle_injective_of_covers` to the
  exact `Function.Injective` hypothesis of `SortingLift.lift_strict` (adapter written out as
  the next obligation in the lane STATUS, not in this file); the root count no-bubble/
  uniqueness; the canonical 33-row topology; `Covers c r ⇒ circle cover`; and the 9-of-11
  bookkeeping (this file speaks about an explicit nine-disk circle cover — it is NOT a
  statement about the unrestricted 11-centre problem).

  No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.ArcCovering
import N11Formalization.Geometry.DiskToArc
import N11Formalization.Essentiality

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.DirectionInjectivity

open N11Formalization

noncomputable section

/-- **Same direction, canonical form ⇒ nested caps.**  Both centres are given in the canonical
form `s • u` / `s' • u` with one common unit vector `u`, so the two caps are *by definition*
threshold comparisons against the same vector and are therefore nested.  This is the
rewrite-free engine of `cap_nested_or_of_same_dir`: `cap_iff_cos_threshold` is applied at the
canonical arguments, so no `rw` on a raw centre can pollute `‖c‖` / `centerDir c`. -/
theorem cap_nested_or_of_same_scaled_dir {c c' u : Point} {s s' r : ℝ} (hu : ‖u‖ = 1)
    (hs : 0 < s) (hs' : 0 < s') (hc : c = s • u) (hc' : c' = s' • u) (hr0 : 0 ≤ r) :
    (∀ x : Point, ‖x‖ = 1 → dist x c ≤ r → dist x c' ≤ r) ∨
      (∀ x : Point, ‖x‖ = 1 → dist x c' ≤ r → dist x c ≤ r) := by
  have key : ∀ x : Point, ‖x‖ = 1 →
      (dist x (s • u) ≤ r ↔
        (1 + s ^ 2 - r ^ 2) / (2 * s) ≤ inner ℝ x u) :=
    fun x hx => cap_iff_cos_threshold (u := u) (x := x) (s := s) (r := r) hu hx hs hr0
  have key' : ∀ x : Point, ‖x‖ = 1 →
      (dist x (s' • u) ≤ r ↔
        (1 + s' ^ 2 - r ^ 2) / (2 * s') ≤ inner ℝ x u) :=
    fun x hx => cap_iff_cos_threshold (u := u) (x := x) (s := s') (r := r) hu hx hs' hr0
  rcases le_total ((1 + s ^ 2 - r ^ 2) / (2 * s))
    ((1 + s' ^ 2 - r ^ 2) / (2 * s')) with hle | hle
  · right
    intro x hx hd
    rw [hc'] at hd
    rw [hc]
    exact (key x hx).mpr (le_trans hle ((key' x hx).mp hd))
  · left
    intro x hx hd
    rw [hc] at hd
    rw [hc']
    exact (key' x hx).mpr (le_trans hle ((key x hx).mp hd))

/-- **Same direction ⇒ nested caps.**  If two nonzero centres have the same direction, their
radius-`r` caps are nested (the containment direction depends on the two threshold values and
is decided by `le_total`). -/
theorem cap_nested_or_of_same_dir {c c' : Point} {r : ℝ} (hr0 : 0 ≤ r) (hne : c ≠ 0)
    (hne' : c' ≠ 0) (hdir : centerDir c = centerDir c') :
    (∀ x : Point, ‖x‖ = 1 → dist x c ≤ r → dist x c' ≤ r) ∨
      (∀ x : Point, ‖x‖ = 1 → dist x c' ≤ r → dist x c ≤ r) := by
  have hu : ‖centerDir c‖ = 1 := centerDir_norm hne
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hne
  have hs' : 0 < ‖c'‖ := norm_pos_iff.mpr hne'
  have hc : c = ‖c‖ • centerDir c := self_eq_norm_smul_centerDir hne
  have hc' : c' = ‖c'‖ • centerDir c := by
    simpa only [← hdir] using self_eq_norm_smul_centerDir hne'
  exact cap_nested_or_of_same_scaled_dir (c := c) (c' := c') (u := centerDir c)
    (s := ‖c‖) (s' := ‖c'‖) (r := r) hu hs hs' hc hc' hr0

/-- **Direction injectivity from non-containment** (the raw hypothesis form). -/
theorem centerDir_injective_of_no_containment {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hcne : ∀ k < 9, c k ≠ 0)
    (hnc : ∀ i j : ℕ, i < 9 → j < 9 → j ≠ i →
      ¬ (∀ x : Point, ‖x‖ = 1 → dist x (c i) ≤ r → dist x (c j) ≤ r)) :
    ∀ i j : ℕ, i < 9 → j < 9 → i ≠ j → centerDir (c i) ≠ centerDir (c j) := by
  intro i j hi hj hij hdir
  rcases cap_nested_or_of_same_dir hr0 (hcne i hi) (hcne j hj) hdir with h | h
  · exact hnc i j hi hj (fun hji => hij hji.symm) h
  · exact hnc j i hj hi hij h

/-- Same statement for the **angles**: `circleAngle` is injective on the unit circle
(`circleMap_circleAngle`), so equal angles force equal directions. -/
theorem circleAngle_centerDir_injective_of_no_containment {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hcne : ∀ k < 9, c k ≠ 0)
    (hnc : ∀ i j : ℕ, i < 9 → j < 9 → j ≠ i →
      ¬ (∀ x : Point, ‖x‖ = 1 → dist x (c i) ≤ r → dist x (c j) ≤ r)) :
    ∀ i j : ℕ, i < 9 → j < 9 → i ≠ j →
      circleAngle (centerDir (c i)) ≠ circleAngle (centerDir (c j)) := by
  intro i j hi hj hij hEq
  refine centerDir_injective_of_no_containment hr0 hcne hnc i j hi hj hij ?_
  have h1 : circleMap (circleAngle (centerDir (c i))) = centerDir (c i) :=
    circleMap_circleAngle _ (centerDir_norm (hcne i hi))
  have h2 : circleMap (circleAngle (centerDir (c j))) = centerDir (c j) :=
    circleMap_circleAngle _ (centerDir_norm (hcne j hj))
  exact h1.symm.trans ((congrArg circleMap hEq).trans h2)

/-- **The angle injectivity in the form `SortingLift.lift_strict` consumes**, with the
non-containment discharged by the gated `Essentiality.not_cap_subset_of_covers`. -/
theorem circleAngle_injective_of_covers {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR0 : r ≤ (19 : ℝ) / 50) (hcne : ∀ k < 9, c k ≠ 0)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r) :
    ∀ i j : ℕ, i < 9 → j < 9 → i ≠ j →
      circleAngle (centerDir (c i)) ≠ circleAngle (centerDir (c j)) :=
  circleAngle_centerDir_injective_of_no_containment hr0 hcne
    (fun i j hi hj hji hsub =>
      Essentiality.not_cap_subset_of_covers hr0 hr1 hrR0 hcov hi hj hji hsub)

/-- **No site sits at the origin.**  Otherwise its cap is empty, contradicting the exclusive
point that `Essentiality.exists_cap_exclusive_point` produces for it. -/
theorem c_ne_zero_of_covers {c : ℕ → Point} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR0 : r ≤ (19 : ℝ) / 50)
    (hcov : ∀ x : Point, ‖x‖ = 1 → ∃ k < 9, dist x (c k) ≤ r) {k : ℕ} (hk : k < 9) :
    c k ≠ 0 := by
  intro hzero
  obtain ⟨t, _ht, hd, _hrest⟩ := Essentiality.exists_cap_exclusive_point hr0 hr1 hrR0 hcov hk
  rw [hzero, dist_zero_right, circleMap_norm] at hd
  linarith

/-! ## Core interface printout -/

#check @N11Formalization.DirectionInjectivity.cap_nested_or_of_same_scaled_dir
#check @N11Formalization.DirectionInjectivity.cap_nested_or_of_same_dir
#check @N11Formalization.DirectionInjectivity.centerDir_injective_of_no_containment
#check @N11Formalization.DirectionInjectivity.circleAngle_centerDir_injective_of_no_containment
#check @N11Formalization.DirectionInjectivity.circleAngle_injective_of_covers
#check @N11Formalization.DirectionInjectivity.c_ne_zero_of_covers

#print axioms N11Formalization.DirectionInjectivity.cap_nested_or_of_same_scaled_dir
#print axioms N11Formalization.DirectionInjectivity.cap_nested_or_of_same_dir
#print axioms N11Formalization.DirectionInjectivity.centerDir_injective_of_no_containment
#print axioms N11Formalization.DirectionInjectivity.circleAngle_centerDir_injective_of_no_containment
#print axioms N11Formalization.DirectionInjectivity.circleAngle_injective_of_covers
#print axioms N11Formalization.DirectionInjectivity.c_ne_zero_of_covers

end

end N11Formalization.DirectionInjectivity
