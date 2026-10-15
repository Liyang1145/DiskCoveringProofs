/-
  **BetaMixture — the β (field-mixture) layer of the C911 cosine-energy certificates, generic
  in the number of support fields.**

  STATUS: DRAFT handed to the Lead for the single serial build slot.  **Not compiled by the
  author** (author scope forbids running lean/lake).  No `sorry`, no custom `axiom`, no
  `native_decide`.

  留痕 (gate3, Lead serial run): exit 1, one implementation error and no mathematical
  obstruction -- the last step of `mixture_identity_of_weights` used the reverse of
  `Finset.sum_mul`, whose pattern is `sum (f i * a)` with `a` independent of `i`, while the goal
  had `sum (beta f * g k)` (constant on the LEFT).  Fixed as the Lead prescribed: fold with two
  forward `Finset.mul_sum` steps and close by `Finset.sum_congr` plus `ring` (the same fix is
  applied to the earlier step of that theorem that had the same shape).  `mixture_le_of_field_bounds`
  and `mixture_energy_le` were already standard axioms in gate3.  Pre-fix byte copy:
  `BetaMixture.V1-pre-gate4.lean`.

  WHY THIS FILE EXISTS (reuse check, Lead's request).  The pair-side extension
  `Σ_{p ∈ S} w p (1 - cos z p) ≤ Σ_{i<j} w i j (1 - cos z i j)` ALREADY EXISTS, generic in the
  weights, in the root cone: `N11Formalization.FlashCosine.partial_energy_le`
  (`FlashCosineCore.lean`, consumed by `FlashCosineLeaf318.stage1`).  The field-side energy bound
  `energy (α,H) ≤ V2` also already exists, generic in the field data:
  `ResumeSchurEnergy.cosine_energy_le_oracle` / `ResumeHarmonic.harmonic_energy_le_oracle`.
  What does NOT exist anywhere is the mixture layer **generic in the field count**: leaf 284's
  `FlashCosineLeaf284Oracle.mixture_le_oracle` is generic in `θ` only, with `Field := Fin 6`,
  a fixed `β` and a fixed field table.  The 2386-leaf census
  (`evidence/cline-six-20260930/energy-semantic/census-source-certificates.json`) shows the
  support size runs 1…8 (`{1:100, 2:251, 3:327, 4:509, 5:571, 6:437, 7:171, 8:20}`), so the
  `Fin 6` shape is leaf-specific and the layer must be Fin-*n*.

  CALIBER.  object: one energy leaf's 36 unordered-pair weights `W` and its support fields
  `f : Fin n` with pair weights `weight f k`; units: length² on the unit disk (`1 - cos` energies
  and `T²` share those units); normalization: `β_f ≥ 0` and `Σ_f β_f = 1` (the source's recorded
  mixture), and `Σ_k` refers to the canonical 36-pair index order `(0,1),(0,2),…,(7,8)`;
  threshold-free (no `T`/`T²` in this file).  `mixture_identity_of_weights` is a **data identity**
  (it consumes the recorded `hmix` as a hypothesis, e.g. leaf 284's kernel-checked
  `mixture_weights`); `mixture_energy_le_oracle` takes the per-field bound `E f ≤ V2` as a
  hypothesis, exactly as `FlashCosineLeaf284Oracle.mixture_le_oracle` consumes
  `source_energy_le_oracle`.  No final energy/oracle statement is a field of any checker here.
-/
import Mathlib

namespace N11Formalization.FlashCosineBeta

open Finset

set_option autoImplicit false

/-- The weighted cosine energy of ONE support field, in the consumer's shape:
`2 * Σ_k weight_f k * (1 - cos (z k))` (compare `FlashCosineLeaf284Oracle.fieldEnergy`). -/
noncomputable def fieldEnergy {n : ℕ} (weight : Fin n → Fin 36 → ℝ) (f : Fin n)
    (z : Fin 36 → ℝ) : ℝ :=
  2 * ∑ k, weight f k * (1 - Real.cos (z k))

/-- **The β layer, generic in the support size.**  `β ≥ 0`, `Σβ = 1`, and every support field's
energy below a common bound `V` give the mixture below `V`.  (This is
`FlashCosineLeaf284Oracle.mixture_le_oracle`'s proof with `Fin 6` replaced by `Fin n` and `V`
abstracted.) -/
theorem mixture_le_of_field_bounds {n : ℕ} (β : Fin n → ℝ) (E : Fin n → ℝ) (V : ℝ)
    (hβ0 : ∀ f, 0 ≤ β f) (hβ1 : ∑ f, β f = 1) (hE : ∀ f, E f ≤ V) :
    ∑ f, β f * E f ≤ V := by
  have h2 : ∑ f, β f * E f ≤ ∑ f, β f * V :=
    Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hE f) (hβ0 f)
  rwa [← Finset.sum_mul, hβ1, one_mul] at h2

/-- **The mixture identity (data layer), generic in the support size.**  If the recorded pair
weights are the β-mixture of the support fields' pair weights, `W k = Σ_f β_f * 2 * weight_f k`,
then the recorded 36-pair cosine energy equals the β-mixture of the fields' energies:
`Σ_k W_k g_k = Σ_f β_f * (2 Σ_k weight_f k g_k)`, `g_k = 1 - cos (z k)`.  (Leaf 284's
`mixture_identity` is this statement with `Fin 6` and the concrete field table.) -/
theorem mixture_identity_of_weights {n : ℕ} (β : Fin n → ℝ) (W : Fin 36 → ℝ)
    (weight : Fin n → Fin 36 → ℝ) (z : Fin 36 → ℝ)
    (hmix : ∀ k, W k = ∑ f, β f * 2 * weight f k) :
    ∑ k, W k * (1 - Real.cos (z k))
      = ∑ f, β f * fieldEnergy weight f z := by
  have h : ∀ k, W k * (1 - Real.cos (z k))
      = ∑ f, β f * (2 * weight f k * (1 - Real.cos (z k))) := by
    intro k
    rw [hmix k, Finset.sum_mul]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [fieldEnergy, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Consumer-shaped corollary, oracle value abstract.**  At the call site instantiate
`V := ResumeNetwork.V2 (fun j => circleMap (θ j))` (so `V2`/`circleMap` need not be imported
here) and `hE f` with the per-field bound
`FlashCosineLeaf284Oracle.source_energy_le_oracle`-shaped proof, which is where the field data
`(α, H)` and the premises `hα/hs/hbal/hH` live (root cone). -/
theorem mixture_energy_le {n : ℕ} (β : Fin n → ℝ) (V : ℝ)
    (weight : Fin n → Fin 36 → ℝ) (z : Fin 36 → ℝ)
    (hβ0 : ∀ f, 0 ≤ β f) (hβ1 : ∑ f, β f = 1)
    (hE : ∀ f, fieldEnergy weight f z ≤ V) :
    ∑ f, β f * fieldEnergy weight f z ≤ V :=
  mixture_le_of_field_bounds β (fun f => fieldEnergy weight f z) V hβ0 hβ1 hE

end N11Formalization.FlashCosineBeta

/-
  REUSE NOTE (not a theorem, kept as prose to avoid a vacuous declaration).

  The pair-side extension is NOT re-proved here: `N11Formalization.FlashCosine.partial_energy_le`
  (root cone, generic in the weights `w`, the pair set `S` and `z`) already gives

      Σ_{p ∈ S} w p.1 p.2 * (1 - cos (z p.1 p.2)) ≤ Σ_{i<j} w i j * (1 - cos (z i j))

  for `w ≥ 0` and `∀ p ∈ S, p.1 < p.2`, which is exactly the bridge from a recorded support of
  pairs to the full 36-pair energy (consumed by `FlashCosineLeaf318.stage1`).  This file only adds
  the missing β layer above it and the data identity that ties the recorded `W` to the fields.
-/

#check @N11Formalization.FlashCosineBeta.fieldEnergy
#check @N11Formalization.FlashCosineBeta.mixture_le_of_field_bounds
#check @N11Formalization.FlashCosineBeta.mixture_identity_of_weights
#check @N11Formalization.FlashCosineBeta.mixture_energy_le
#print axioms N11Formalization.FlashCosineBeta.mixture_le_of_field_bounds
#print axioms N11Formalization.FlashCosineBeta.mixture_identity_of_weights
#print axioms N11Formalization.FlashCosineBeta.mixture_energy_le
