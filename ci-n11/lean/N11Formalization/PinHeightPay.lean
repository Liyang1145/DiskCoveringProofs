/-
n11-formalization — cline-six-20260930 / source-stress — **unbuilt draft, Lead owns the serial slot**.

# `PinHeightPayV6` — pin-height premise paid; gate-2 faults repaired

Dependency name **frozen canonical**: `import N11Formalization.PinBranchBind` (Pin4, GREEN, canonical
namespace).  No `.V2`/nested module import.  Every theorem here is stated with this file's own
`chordMid_mid` (definitionally `(2:ℝ)⁻¹ • (P + Q)`, the same point as the canonical `chordMid`).

Gate-2 faults (`lead/pin-height-gate2.log`) repaired:

* L73: the rewrite of the doubled midpoint must go **forward** (`hM : (2:ℝ) • m = P + Q`) against the
  target that contains `(2:ℝ) • m`; the bare `2 •` spelling was ambiguous between the `Nat`-smul and
  the `ℝ`-smul, so **every** coefficient is now written `(2 : ℝ) •`;
* L77: vector coefficients are no longer handled by `abel` (which cannot reconcile the smul
  coefficients) but by Mathlib's `module` tactic, as in the GREEN Pin4;
* L86: `hplus`/`hminus` must be used **backwards** (`rw [← hplus, ← hminus] at hpl`), because `hpl`
  (the parallelogram identity) is expressed in the `(U−M) ± (P−M)` form;
* L115/L128/L129 (**gate-3**, the only remaining faults): the three `arcEnd` distance lemmas live in
  namespace **`N11Formalization.FlashRootNetwork`** (declared at `FlashLeafRootNetwork.lean` L55 — the
  *file* name is `FlashLeafRootNetwork` but the **namespace is `FlashRootNetwork`**), so the calls are
  now `FlashRootNetwork.dist_arcEnd_ringCenter_succ` / `…_self` (with `open N11Formalization`).  Their
  binders are checked for real: `_self` takes `(k : Fin 9)`, `_succ` takes `(k : Fin 8)`, `_wrap`
  takes no index (it is the `k = 8` case).  This draft's scope is the controllable non-wrapping branch
  `k : Fin 8`; the wrap case `k = 8` needs the explicit `Fin 9` construction and is left to the next
  file.

## What is proved here

* `pinHeight_sq_of_equidistant` — **the height premise, paid**: `‖U − P‖ = ‖U − Q‖ = R` implies
  `‖U − M‖² = R² − ‖Q − P‖²/4`, branch-free (parallelogram law);
* `sub_midpoint_orthogonal` — reuse of the tree's `N11Formalization.sub_midpoint_orthogonal_of_equidistant`;
* `Uvec_sub_left`/`_right` — the reflection identities; `Uvec_equidistant_succ` — the fan pin's
  equidistances from the tree's green `arcEnd` distances; `fanPinHeight_sq` — the fan instance.

## Not proved here

Root-side `F_out > 0`, `y > 0`, the central `wPoint` instance, and the actual-TC stationarity →
`sourceB2` row.  No sorry, no custom axiom, no `native_decide`.
-/

import Mathlib
import N11Formalization.PinBranchBind
import N11Formalization.FlashLeafRootNetwork
import N11Formalization.FlashCoverReductionBlockerGeometry

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.PinHeightPayV6

open N11Formalization

noncomputable section

/-- This file's chord midpoint (the same point as the canonical `chordMid`). -/
def chordMid_mid (P Q : Point) : Point := (2 : ℝ)⁻¹ • (P + Q)

/-- `(2 : ℝ) • chordMid_mid P Q = P + Q`. -/
theorem two_smul_chordMid_mid (P Q : Point) : (2 : ℝ) • chordMid_mid P Q = P + Q := by
  unfold chordMid_mid
  rw [smul_smul]
  norm_num

/-- `(U − P) = (U − M) − (P − M)`. -/
theorem sub_eq_sub_sub (P Q U : Point) :
    U - P = (U - chordMid_mid P Q) - (P - chordMid_mid P Q) := by
  module

/-- `(U − Q) = (U − M) + (P − M)`. -/
theorem sub_eq_sub_add (P Q U : Point) :
    U - Q = (U - chordMid_mid P Q) + (P - chordMid_mid P Q) := by
  have hM := two_smul_chordMid_mid P Q
  have h1 : (U - chordMid_mid P Q) + (P - chordMid_mid P Q)
      = U + P - (2 : ℝ) • chordMid_mid P Q := by
    module
  rw [h1, hM]
  module

/-- **The height premise, paid in general**: equidistance to the chord endpoints forces
`‖U − M‖² = R² − ‖Q − P‖²/4`, with **no branch hypothesis**. -/
theorem pinHeight_sq_of_equidistant {P Q U : Point} {R : ℝ}
    (hP : ‖U - P‖ = R) (hQ : ‖U - Q‖ = R) :
    ‖U - chordMid_mid P Q‖ ^ 2 = R ^ 2 - (‖Q - P‖ / 2) ^ 2 := by
  have hM := two_smul_chordMid_mid P Q
  have ha := norm_add_sq_real (U - chordMid_mid P Q) (P - chordMid_mid P Q)
  have hb0 := norm_sub_sq_real (U - chordMid_mid P Q) (P - chordMid_mid P Q)
  have hpl : ‖(U - chordMid_mid P Q) + (P - chordMid_mid P Q)‖ ^ 2
      + ‖(U - chordMid_mid P Q) - (P - chordMid_mid P Q)‖ ^ 2
      = 2 * ‖U - chordMid_mid P Q‖ ^ 2 + 2 * ‖P - chordMid_mid P Q‖ ^ 2 := by
    rw [ha, hb0]
    ring
  have hplus := sub_eq_sub_add P Q U
  have hminus := sub_eq_sub_sub P Q U
  have hb : ‖P - chordMid_mid P Q‖ = ‖Q - P‖ / 2 := by
    have h2 : (2 : ℝ) • (P - chordMid_mid P Q) = P - Q := by
      rw [smul_sub, hM]
      module
    have hid : P - chordMid_mid P Q = (2 : ℝ)⁻¹ • (P - Q) := by
      rw [← h2, smul_smul]
      norm_num
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹),
      norm_sub_rev]
    ring
  rw [← hplus, ← hminus, hP, hQ] at hpl
  rw [hb] at hpl
  nlinarith

/-- **Orthogonality of the pin to the chord**, reusing the tree's green
`N11Formalization.sub_midpoint_orthogonal_of_equidistant`. -/
theorem sub_midpoint_orthogonal {P Q U : Point} (h : ‖U - P‖ = ‖U - Q‖) :
    (inner ℝ (U - chordMid_mid P Q) (Q - P) : ℝ) = 0 :=
  sub_midpoint_orthogonal_of_equidistant (by rfl) h

/-- `Uvec u k − C_k = C_{k+1} − arcEnd u k` (the reflection identity). -/
theorem Uvec_sub_left (u : Fin 12 → ℝ) (k : Fin 9) :
    Uvec u k - ringCenter u k = ringCenter u (k + 1) - arcEnd u k := by
  unfold Uvec
  module

/-- `Uvec u k − C_{k+1} = C_k − arcEnd u k`. -/
theorem Uvec_sub_right (u : Fin 12 → ℝ) (k : Fin 9) :
    Uvec u k - ringCenter u (k + 1) = ringCenter u k - arcEnd u k := by
  unfold Uvec
  module

/-- **The `Fin 9` addition literal**, so that `Fin`-addition spellings and literal spellings match.
The free variable is reverted first, so `decide` runs on the whole universally quantified finite
proposition (the route the Lead prescribed instead of guessing defeq). -/
theorem fin_add_one_literal (k : Fin 8) :
    ((⟨(k : ℕ), by omega⟩ : Fin 9) + 1) = ⟨(k : ℕ) + 1, by omega⟩ := by
  revert k
  decide

/-- **The fan pin is equidistant to its chord endpoints with radius `u 6`** (non-wrapping arcs),
from the tree's green `arcEnd` distances.  The `Fin`-addition spelling produced by `Uvec_sub_left` is
normalized with `fin_add_one_literal`; the second goal carries the *literal* spelling, so it is first
rewritten **back** to the addition spelling so that `Uvec_sub_right` applies. -/
theorem Uvec_equidistant_succ (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) (k : Fin 8) :
    ‖Uvec u ⟨(k : ℕ), by omega⟩ - ringCenter u ⟨(k : ℕ), by omega⟩‖ = u 6
      ∧ ‖Uvec u ⟨(k : ℕ), by omega⟩ - ringCenter u ⟨(k : ℕ) + 1, by omega⟩‖ = u 6 := by
  have h1 := FlashRootNetwork.dist_arcEnd_ringCenter_succ u hsin hR k
  have h2 := FlashRootNetwork.dist_arcEnd_ringCenter_self u hsin hR ⟨(k : ℕ), by omega⟩
  rw [dist_eq_norm] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [Uvec_sub_left, fin_add_one_literal k, norm_sub_rev]
    exact h1
  · rw [← fin_add_one_literal k, Uvec_sub_right, norm_sub_rev]
    exact h2

/-- **The fan pin's height, premise discharged**: `‖Uvec u k − M‖² = (u 6)² − (‖C_{k+1} − C_k‖/2)²`. -/
theorem fanPinHeight_sq (u : Fin 12 → ℝ)
    (hsin : ∀ k : Fin 9, Real.sin (angleVec u k) ^ 2 ≤ (u 6) ^ 2) (hR : 0 ≤ u 6) (k : Fin 8) :
    ‖Uvec u ⟨(k : ℕ), by omega⟩
        - chordMid_mid (ringCenter u ⟨(k : ℕ), by omega⟩)
            (ringCenter u ⟨(k : ℕ) + 1, by omega⟩)‖ ^ 2
      = (u 6) ^ 2
        - (‖ringCenter u ⟨(k : ℕ) + 1, by omega⟩ - ringCenter u ⟨(k : ℕ), by omega⟩‖ / 2) ^ 2 :=
  pinHeight_sq_of_equidistant (Uvec_equidistant_succ u hsin hR k).1
    (Uvec_equidistant_succ u hsin hR k).2

end

end N11Formalization.PinHeightPayV6

#print axioms N11Formalization.PinHeightPayV6.two_smul_chordMid_mid
#print axioms N11Formalization.PinHeightPayV6.sub_eq_sub_sub
#print axioms N11Formalization.PinHeightPayV6.sub_eq_sub_add
#print axioms N11Formalization.PinHeightPayV6.pinHeight_sq_of_equidistant
#print axioms N11Formalization.PinHeightPayV6.sub_midpoint_orthogonal
#print axioms N11Formalization.PinHeightPayV6.Uvec_equidistant_succ
#print axioms N11Formalization.PinHeightPayV6.fanPinHeight_sq

#check @N11Formalization.PinBranchBind.chordMid
#check @N11Formalization.PinBranchBind.Fout_eq_Fin_add_yh
