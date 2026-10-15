/-
n11-formalization — cline-six / harmonic-response (2026-10-01) — **unbuilt draft (new filename)**.

STATUS: NOT KERNEL-CHECKED.  Imports two modules:
  * `N11Formalization.HarmonicLiftExistence` — already built (Lead module build, exit 0);
  * `N11Formalization.HarmonicResponseConsumer` — the already-green consumer evidence source
    (`HarmonicResponseConsumer.lean`, sha DBEAE5904863985FA557385AA2E891F652C07BB093B4F96345EAEE8677C87231,
    gate4 exit 0, standard axioms); the Lead copies/builds it into the module tree.
It contains NO duplicate of the difference helper: the per-edge identity is called directly as
`HarmonicResponseConsumer.edgeVector_eq_of_balance`.

## Content

`exists_lift_reproducing_actual` — consumer-first synthesis: for α ≥ 0 and any actual zero-force
configuration `(C,Z)` at datum `U`, there is `H` with `hbal H` whose lift minimizes the Dirichlet
energy for EVERY datum and reproduces the actual anchor flux and weighted energy at `U`.
Premises: only `hα` and the geometric balance `ha`.  No `H`/`hbal` premise, no response/Gram/Schur
hypothesis, no connectivity or positivity of α on carrying edges, no `Σα = 1`.

## Provenance / gate history

* `HarmonicReproduceActual.lean` V1 (sha 210D61C85CF3F7647F785610CBEF45441BCFC334E83BDEAA760A0D0C94CC958D)
  gated once: exit 1 at L103 — my `Finset.sum_congr` rewrite used `(hterm e).symm` (wrong
  direction: it produces `∑ ‖…‖² = ∑ inner …`, while `h`'s LHS is the inner form).  V1 is kept
  byte-for-byte as `HarmonicReproduceActual.V1.lean` and is superseded by this file; the helper it
  carried is dropped here in favour of the module import.
* This V2 does not re-introduce that rewrite at all: the local helper (with its `rw`/`linarith`
  steps) lives in the green consumer module.

## Not claimed

No actual α construction (source-stress), no radial load identity beyond the explicit `ha`, no
Schur = Gram, no attainment / lower bound, no pointwise claim that the source's centers equal the
lift.  No sorry / custom axiom / native_decide.
-/
import Mathlib
import N11Formalization.HarmonicLiftExistence
import N11Formalization.HarmonicResponseConsumer
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeDirichlet
import N11Formalization.ResumeHarmonic
import N11Formalization.ResumeAnchorFlux

set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.HarmonicReproduceActualV2

open Finset
open N11Formalization
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeDirichlet
open N11Formalization.ResumeHarmonic
open N11Formalization.ResumeAnchorFlux

/-- **Consumer-first reproduction of the actual balanced configuration.**  Given α ≥ 0 and an
actual zero-force configuration `(C,Z)` at datum `U`, some balanced `H` exists whose lift
minimizes for every datum and reproduces the actual anchor flux and weighted energy at `U`. -/
theorem exists_lift_reproducing_actual
    {α : Edge → ℝ} {U : Fin 9 → Point} {C Z : Fin 11 → Point}
    (hα : ∀ e, 0 ≤ α e)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0) :
    ∃ H : Free → Fin 9 → ℝ,
      (∀ v j, ∑ e, (α e * incidence e v) * coeff H e j = 0) ∧
      (∀ W : Fin 9 → Point,
        energy α W (fun i => lift H W (.inl i)) (fun f => lift H W (.inr f))
          = dirichletEnergy α W) ∧
      (∀ i, flux α U (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f)) i
        = flux α U C Z i) ∧
      energy α U (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f))
        = energy α U C Z := by
  classical
  obtain ⟨H, hbal, hmin⟩ := HarmonicLiftExistence.harmonic_lift_exists α hα
  have hb : ∀ v : Free, ∑ e, (α e * incidence e v) •
      edgeVector U (fun i => lift H U (.inl i)) (fun f => lift H U (.inr f)) e = 0 :=
    fun v => balance_of_columns α H hbal U v
  have hedge := HarmonicResponseConsumer.edgeVector_eq_of_balance (α := α) (U := U)
    (C₁ := fun i => lift H U (.inl i)) (Z₁ := fun f => lift H U (.inr f)) (C₂ := C) (Z₂ := Z)
    hα hb ha
  refine ⟨H, hbal, hmin, ?_, ?_⟩
  · intro i
    unfold flux
    apply Finset.sum_congr rfl
    intro e _
    by_cases hae : α e = 0
    · simp [hae]
    · rw [hedge e hae]
  · unfold energy
    apply Finset.sum_congr rfl
    intro e _
    by_cases hae : α e = 0
    · simp [hae]
    · rw [edgeLength_eq_norm, edgeLength_eq_norm, hedge e hae]

end N11Formalization.HarmonicReproduceActualV2

#print axioms N11Formalization.HarmonicReproduceActualV2.exists_lift_reproducing_actual

set_option pp.explicit true
set_option pp.universes false

#check @N11Formalization.HarmonicReproduceActualV2.exists_lift_reproducing_actual
