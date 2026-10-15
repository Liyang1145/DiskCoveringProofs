/-
  **PairTemplate — the two PARAMETRIC lemmas that turn a per-pair packet into a batch.**

  STATUS: DRAFT handed to the Lead for the single serial build slot.  **Not compiled by the
  author.**  No `sorry`, no custom `axiom`, no `native_decide`.

  留痕 (gate1, Lead run, log `evidence/cline-six-20260930/lead/pair-template-gate1.log`): exit 1
  with two root errors, both in `pair_sigma_bounds`, none mathematical -- (i) `tval_eq_tlift` is
  in the `FlashCosineLeaf284Bridge` namespace and is now qualified; (ii) the `rw [hslo.symm]`
  step looked for the pattern `-dbm ...` (the negation is part of `hslo.symm`'s LHS), which does
  not occur in the hypothesis; replaced by the Lead's prescription: prove the real-level bridge
  `(dbm (castSucc j) (castSucc i) : ℝ) = -(slo : ℝ)` by `rw [hslo, Rat.cast_neg, neg_neg]`,
  then `linarith`.  Pre-fix byte copy: `PairTemplate.V1.lean`
  (SHA A0CD0D4BBD0669D425FA560C5E2C837DFCD4B6A10C0A835B40C764CA04DB7E91).

  WHAT IS NEW HERE (and why it is not a re-creation).

  * `pair_sigma_bounds` / `pair_arc_mem` generalise the pair-(0,5) packet's §1 (and the
    integrated leaf-284 `FlashCosineLeaf284Energy.arc_mem`) from one concrete pair to ARBITRARY
    `i < j`: the DBM rows give the chart increment bounds, `tval_eq_tlift` moves them to the
    `FlashLeafSplit` cell variables, and the compiled generic
    `FlashCosine.FlashCosineLeaf318.cell_bound` converts them into the ACTUAL angular interval
    `[A, B]` of `zval y i j` with the kernel's own rational brackets.  This is the interface an
    emitter needs once per pair; the packet only instantiates it at `(0,5)`.
  * `gamma_mixture_of_antitone_endpoints` composes the verified γ layer with the endpoint
    (`minorant_of_antitone_sin` / `rational_dec`) rule in ONE step: exactly the shape a pair
    packet needs on a `cos < 0` arc, where the QA form is inapplicable and every line is
    certified by its two rational endpoint deficits.  The existing γ layer has the interval form
    and the two *tangent* rule compositions, but not this endpoint composition.

  Reuse check (Lead's standing request): `FlashCosineCore.partial_energy_le` (pair-side weighted
  partial sum) and `ResumeSchurEnergy.cosine_energy_le_oracle` (field-side energy ≤ oracle) are
  already generic and are NOT re-proved here; `FlashCosineLeaf284Energy.rational_dec` is the
  existing per-line endpoint adapter and is consumed, not duplicated.

  CALIBER.  object: one unordered pair of one leaf's chart, `z = zval y i j`, with the leaf's DBM
  cell; units: length² on the unit disk; normalization: `γ ≥ 0`, `Σγ = 1`; threshold-free (no
  `T`/`T²`), and no energy/oracle statement appears as a hypothesis or a conclusion.
-/
import Mathlib
import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineLeaf284Energy
import N11Formalization.GammaMixture

namespace N11Formalization.PairTemplate

open Finset

set_option autoImplicit false

open N11Formalization.FlashCosine (Lq LQ Dq DQ Lc Dc L_mem D_mem tval zval zval_eq cell_bound)
open N11Formalization.FlashLeafSplit (Cell tlift)

/-! ## 1. The DBM → actual-interval interface, parametric in the pair -/

/-- **Parametric version of the leaf-284 `arc_mem` first half.**  Two DBM rows bound the chart
increment `t_j - t_i`; the bounds are moved to the `FlashLeafSplit` cell variables by the
integrated `tval_eq_tlift`.  Indices are written as `Fin.castSucc i` / `Fin.castSucc j`, exactly
as `zval_eq` produces them. -/
theorem pair_sigma_bounds (y : Fin 9 → ℝ) (i j : Fin 9) (hij : (i : ℕ) < (j : ℕ))
    {dbm : Fin 10 → Fin 10 → ℚ} {slo shi : ℚ}
    (hslo : slo = -dbm (Fin.castSucc j) (Fin.castSucc i))
    (hshi : shi = dbm (Fin.castSucc i) (Fin.castSucc j))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (slo : ℝ) ≤ tval y (Fin.castSucc j) - tval y (Fin.castSucc i) ∧
      tval y (Fin.castSucc j) - tval y (Fin.castSucc i) ≤ (shi : ℝ) := by
  have hsloR : (dbm (Fin.castSucc j) (Fin.castSucc i) : ℝ) = -(slo : ℝ) := by
    rw [hslo, Rat.cast_neg, neg_neg]
  have hshiR : (dbm (Fin.castSucc i) (Fin.castSucc j) : ℝ) = (shi : ℝ) := by
    rw [hshi]
  have h1 := hcell (Fin.castSucc i) (Fin.castSucc j)
  have h2 := hcell (Fin.castSucc j) (Fin.castSucc i)
  simp only [← N11Formalization.FlashCosineLeaf284Bridge.tval_eq_tlift] at h1 h2
  rw [hshiR] at h1
  rw [hsloR] at h2
  constructor <;> linarith

/-- **Parametric arc membership.**  From the DBM row bounds and the kernel's own brackets, the
compiled generic `cell_bound` puts `zval y i j` into the frozen rational interval
`[-(j-i)·LQ + Dq·slo, -(j-i)·Lq + DQ·shi]` (the ACTUAL angular interval of the cell; the recorded
certificate arc is a separate object). -/
theorem pair_arc_mem (y : Fin 9 → ℝ) (i j : Fin 9) (hij : (i : ℕ) < (j : ℕ))
    {slo shi : ℚ} (hslo0 : 0 ≤ slo)
    (hlo : (slo : ℝ) ≤ tval y (Fin.castSucc j) - tval y (Fin.castSucc i))
    (hhi : tval y (Fin.castSucc j) - tval y (Fin.castSucc i) ≤ (shi : ℝ)) :
    (((((i : ℕ) : ℚ) - ((j : ℕ) : ℚ)) * LQ + Dq * slo : ℚ) : ℝ) ≤ zval y i j ∧
      zval y i j ≤ (((((i : ℕ) : ℚ) - ((j : ℕ) : ℚ)) * Lq + DQ * shi : ℚ) : ℝ) := by
  have hb := cell_bound (i := (i : ℕ)) (j := (j : ℕ)) hij hslo0
    L_mem.1 L_mem.2 D_mem.1 D_mem.2 hlo hhi
  rw [zval_eq]
  exact hb

/-! ## 2. The γ layer composed with the endpoint (antitone) rule -/

/-- **γ-mixture over the endpoint rule (one step).**  On a decreasing-sine arc every line is
certified by its two RATIONAL endpoint deficits against the kernel's own `cosHiNLag`; the
γ-mixture then collapses to a single line with slope `Σ γ_l s_l` and intercept `Σ γ_l c_l`.
This is `FlashCosineLeaf284Energy.rational_dec` applied line-wise and then
`FlashCosineMixture.gamma_mixture_minorant` — the exact shape a pair packet needs on a
`cos < 0` arc (where the QA form cannot be used). -/
theorem gamma_mixture_of_antitone_endpoints {ι : Type*} [Fintype ι] {a b : ℚ}
    (γ : ι → ℝ) (hγ0 : ∀ l, 0 ≤ γ l) (hγ1 : ∑ l, γ l = 1)
    (hm : AntitoneOn Real.sin (Set.Icc (a : ℝ) (b : ℝ)))
    (s c : ι → ℚ)
    (ha : ∀ l, c l ≤ 1 - N11Formalization.cosHiNLag a - s l * a)
    (hb : ∀ l, c l ≤ 1 - N11Formalization.cosHiNLag b - s l * b) :
    ∀ z ∈ Set.Icc (a : ℝ) (b : ℝ),
      (∑ l, γ l * (s l : ℝ)) * z + (∑ l, γ l * (c l : ℝ)) ≤ 1 - Real.cos z :=
  FlashCosineMixture.gamma_mixture_minorant (a := (a : ℝ)) (b := (b : ℝ)) γ hγ0 hγ1
    (fun l => (s l : ℝ)) (fun l => (c l : ℝ))
    (fun l => FlashCosineLeaf284Energy.rational_dec (a := a) (b := b) hm (ha l) (hb l))

end N11Formalization.PairTemplate

#check @N11Formalization.PairTemplate.pair_sigma_bounds
#check @N11Formalization.PairTemplate.pair_arc_mem
#check @N11Formalization.PairTemplate.gamma_mixture_of_antitone_endpoints
#print axioms N11Formalization.PairTemplate.pair_sigma_bounds
#print axioms N11Formalization.PairTemplate.pair_arc_mem
#print axioms N11Formalization.PairTemplate.gamma_mixture_of_antitone_endpoints
