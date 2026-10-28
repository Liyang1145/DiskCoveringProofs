/-
  **GammaMixture — the shared multi-tangent (γ-mixture) layer for the C911 cosine-energy
  leaves.**

  STATUS: DRAFT handed to the Lead for the single serial build slot.  **Not compiled by the
  author** (author scope forbids running lean/lake).  Every library fact used here is either
  already consumed by a file in the root import cone (`FlashCosineCore`, `FlashCosineSupport`)
  or by the standalone-checked `QASupport`; no `sorry`, no custom `axiom`, no `native_decide`.

  留痕 (gate1, Lead serial run, 2026-09-30): exit 1, two implementation errors only, no
  mathematical obstruction -- (i) the term-mode `simpa` in `pair_mixture_lower_bound` lacked
  a `by` (unknown identifier / unexpected token at that spot); (ii) `gammaCal` needed
  `noncomputable` (depends on `Real.instDivInvMonoid`).  Both fixed here; a one-line
  unused-variable warning in `gamma_mixture_minorant` was silenced by naming the point `z`
  explicitly.  The pre-fix byte copy is `GammaMixture.V1-pre-gate2.lean` (same SHA as the
  file gate1 consumed); the red log is `gamma-mixture-gate1.log` in this directory.  Gates
  1 and 2 of the red log did show `sorryAx` for the five declarations downstream of the
  failed `simpa`; that is an artefact of the failed declaration, not a proof feature, and is
  not accepted as evidence.

  WHAT THIS IS.  The recorded source certificate of an energy leaf carries, per unordered pair
  `k`, a *list* of affine lines `(s_l, v_l)` with mixture weights `γ_l ≥ 0`, `Σ_l γ_l = 1`,
  each line a whole-arc minorant of `1 - cos`:

        ∀ l, ∀ z ∈ [a,b],  s_l * z + v_l  ≤  1 - cos z.

  The existing leaf-284 consumer (`FlashCosineLeaf284Energy.all_minorants`,
  `FlashCosineLeaf284Oracle.mixture_identity` / `mixture_le_oracle`) uses only the
  **single-line** case `γ = 1`.  This file supplies the missing mixture layer, i.e. the
  reflection step

        per-line minorants + (γ ≥ 0, Σγ = 1)  ⟹  per-pair γ-mixture minorant,

  together with the two facts the LP/duality layer and the emitter need:

  * `gamma_mixture_is_affine` — the γ-mixture of affine lines IS one affine line, with slope
    `Σ_l γ_l s_l` and intercept `Σ_l γ_l v_l`.  Hence multi-tangency costs the LP / weak-duality
    layer (`FlashCosineCore.lp_step9`) *nothing*: only the collapsed pair
    `(Σ_l γ_l s_l, Σ_l γ_l v_l)` enters it (the "γ-collapse").
  * `gamma_mixture_of_approx_support` / `gamma_mixture_of_QA` — the per-line hypotheses are
    exactly the hypotheses of the two *already compiled* per-line rules
    (`FlashCosineSupport.minorant_of_approx_support`: endpoint / approximate tangent;
    `QASupport.minorant_of_second_order_support`: the `e^2/(2m)` quadratic form), so the
    γ-mixture layer composes with both without new analytic content.

  CALIBER.  object: the angular-difference vector `z` of ONE energy leaf's cell
  (`z k = zval y (i k) (j k)`, `k` over the leaf's unordered pairs); units: length² on the unit
  disk (`1 - cos` energies and `T²` share those units); normalization: the mixture weights `γ`
  are per PAIR nonnegative and sum to `1`; the pair weights `W_k ≥ 0` are the consumer's own
  data and carry no normalization here (`Σ_k W_k` is a property of the recorded table, not a
  premise of these lemmas); threshold-free: `T` / `T²` never appear in this file.  The final
  implication `γ-mixture minorant + cell membership ⟹ T² < V2 (circleMap ∘ θ)` is deliberately
  NOT a field of any predicate here; it stays with the consumer
  (`FlashCosineLeaf284Oracle.leaf284_oracle_gt` / `leaf284_radius_gt`).
-/
import Mathlib
import N11Formalization.FlashCosineCore
import N11Formalization.FlashCosineSupport
import N11Formalization.QASupport

namespace N11Formalization.FlashCosineMixture

open Finset

set_option autoImplicit false

/-! ## 1. The γ-collapse identity (pair level) -/

/-- **The γ-collapse identity.**  The γ-mixture of affine lines is one affine line with slope
`Σ γ_l s_l` and intercept `Σ γ_l c_l`.  This is what makes the LP / weak-duality layer
γ-blind (only the collapsed pair enters `lp_step9`). -/
theorem gamma_mixture_is_affine {ι : Type*} [Fintype ι] (γ s c : ι → ℝ) (z : ℝ) :
    ∑ l, γ l * (s l * z + c l) = (∑ l, γ l * s l) * z + ∑ l, γ l * c l := by
  have h1 : ∀ l, γ l * (s l * z + c l) = (γ l * s l) * z + γ l * c l := fun l => by ring
  simp only [h1]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]

/-! ## 2. The pointwise mixture step -/

/-- **γ-mixture at a point.**  A convex combination (`γ ≥ 0`, `Σ γ = 1`) of affine functions
each dominated by `1 - cos` at `z` is again dominated by `1 - cos` at `z`.  No interval, no
monotonicity, no threshold. -/
theorem gamma_mixture_at {ι : Type*} [Fintype ι] {z : ℝ} (γ : ι → ℝ)
    (hγ0 : ∀ l, 0 ≤ γ l) (hγ1 : ∑ l, γ l = 1) (s c : ι → ℝ)
    (hline : ∀ l, s l * z + c l ≤ 1 - Real.cos z) :
    ∑ l, γ l * (s l * z + c l) ≤ 1 - Real.cos z := by
  have h2 : ∑ l, γ l * (s l * z + c l) ≤ ∑ l, γ l * (1 - Real.cos z) :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hline l) (hγ0 l)
  rwa [← Finset.sum_mul, hγ1, one_mul] at h2

/-! ## 3. The requested shared multi-tangent lemma -/

/-- **Per-pair γ-mixture lower bound (shared multi-tangent lemma).**  Given the recorded lines
of ONE pair, each certified as a whole-arc minorant on the *enlarged* arc `[a,b]`, and a cell
point `z ∈ [a,b]`, the γ-mixture is a lower bound at `z`, with the γ-collapsed slope and
intercept.  This is the statement the emitter needs per pair; it consumes the per-line
minorant hypothesis verbatim. -/
theorem pair_mixture_lower_bound {ι : Type*} [Fintype ι] {a b z : ℝ}
    (hz : z ∈ Set.Icc a b) (γ : ι → ℝ) (hγ0 : ∀ l, 0 ≤ γ l) (hγ1 : ∑ l, γ l = 1)
    (s c : ι → ℝ)
    (hline : ∀ l, ∀ z' ∈ Set.Icc a b, s l * z' + c l ≤ 1 - Real.cos z') :
    (∑ l, γ l * s l) * z + (∑ l, γ l * c l) ≤ 1 - Real.cos z := by
  simpa only [gamma_mixture_is_affine]
    using gamma_mixture_at γ hγ0 hγ1 s c fun l => hline l z hz

/-- **γ-mixture interval minorant.**  Same statement in the interval form consumed by the leaf
consumers (compare `FlashCosineLeaf284Energy.all_minorants`): the mixture is a whole-arc
minorant on `[a,b]`, with the collapsed slope/intercept. -/
theorem gamma_mixture_minorant {ι : Type*} [Fintype ι] {a b : ℝ} (γ : ι → ℝ)
    (hγ0 : ∀ l, 0 ≤ γ l) (hγ1 : ∑ l, γ l = 1) (s c : ι → ℝ)
    (hline : ∀ l, ∀ z' ∈ Set.Icc a b, s l * z' + c l ≤ 1 - Real.cos z') :
    ∀ z ∈ Set.Icc a b, (∑ l, γ l * s l) * z + (∑ l, γ l * c l) ≤ 1 - Real.cos z :=
  fun z hz => pair_mixture_lower_bound (z := z) hz γ hγ0 hγ1 s c hline

/-! ## 4. Assembly over the leaf's pairs (consumer-facing shape) -/

/-- **Weighted assembly (collapsed form).**  With pair weights `W ≥ 0` and per-pair
γ-mixtures certified by per-line minorants, the recorded *collapsed* affine functional is below
the leaf's weighted cosine energy `Σ_k W_k (1 - cos (z k))`.  `W` is arbitrary data here: the
leaf-284 consumer instantiates `W := wt`, `z k := zval y (iOf k) (jOf k)`. -/
theorem mixture_energy_ge_affine {n m : ℕ} (W : Fin n → ℝ) (hW : ∀ k, 0 ≤ W k)
    (z : Fin n → ℝ) (γ : Fin n → Fin m → ℝ)
    (hγ0 : ∀ k l, 0 ≤ γ k l) (hγ1 : ∀ k, ∑ l, γ k l = 1)
    (s c : Fin n → Fin m → ℝ)
    (hline : ∀ k l, s k l * z k + c k l ≤ 1 - Real.cos (z k)) :
    ∑ k, W k * ((∑ l, γ k l * s k l) * z k + ∑ l, γ k l * c k l)
      ≤ ∑ k, W k * (1 - Real.cos (z k)) := by
  refine Finset.sum_le_sum fun k _ => ?_
  have h := gamma_mixture_at (γ k) (hγ0 k) (hγ1 k) (s k) (c k) (fun l => hline k l)
  simpa only [gamma_mixture_is_affine] using mul_le_mul_of_nonneg_left h (hW k)

/-- Same as `mixture_energy_ge_affine` but with the *un-collapsed* recorded lines on the left
(the form an emitter that lists lines directly produces). -/
theorem mixture_energy_ge_recorded {n m : ℕ} (W : Fin n → ℝ) (hW : ∀ k, 0 ≤ W k)
    (z : Fin n → ℝ) (γ : Fin n → Fin m → ℝ)
    (hγ0 : ∀ k l, 0 ≤ γ k l) (hγ1 : ∀ k, ∑ l, γ k l = 1)
    (s c : Fin n → Fin m → ℝ)
    (hline : ∀ k l, s k l * z k + c k l ≤ 1 - Real.cos (z k)) :
    ∑ k, W k * (∑ l, γ k l * (s k l * z k + c k l))
      ≤ ∑ k, W k * (1 - Real.cos (z k)) := by
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left
    (gamma_mixture_at (γ k) (hγ0 k) (hγ1 k) (s k) (c k) (fun l => hline k l)) (hW k)

/-! ## 5. Composing with the two ALREADY COMPILED per-line rules -/

/-- **γ-mixture over the endpoint/approximate-tangent rule.**  Each line carries a rational
tangent point `t_l`, slope error `e_l` and cosine upper bound `H_l`; the per-line hypothesis is
exactly `FlashCosineSupport.minorant_of_approx_support`'s premise list, and the conclusion is
the collapsed γ-mixture on `[a,b]`.  Note `sin` need only be monotone on one arc `[a,b]`. -/
theorem gamma_mixture_of_approx_support {ι : Type*} [Fintype ι] {a b : ℝ} (γ : ι → ℝ)
    (hγ0 : ∀ l, 0 ≤ γ l) (hγ1 : ∑ l, γ l = 1)
    (hm : MonotoneOn Real.sin (Set.Icc a b))
    (t s c e H : ι → ℝ) (he : ∀ l, 0 ≤ e l) (ht : ∀ l, t l ∈ Set.Icc a b)
    (hs : ∀ l, |Real.sin (t l) - s l| ≤ e l) (hH : ∀ l, Real.cos (t l) ≤ H l)
    (hc : ∀ l, c l ≤ 1 - H l - s l * t l - e l * (b - a)) :
    ∀ z ∈ Set.Icc a b, (∑ l, γ l * s l) * z + (∑ l, γ l * c l) ≤ 1 - Real.cos z :=
  gamma_mixture_minorant γ hγ0 hγ1 s c fun l =>
    FlashCosineSupport.minorant_of_approx_support hm (ht l) (he l) (hs l) (hH l) (hc l)

/-- **γ-mixture over the quadratic (QA) rule.**  Each line carries a tangent point `t_l`, a
slope error `e_l` and a *shape-free* cosine floor `m_l > 0` on `[a,b]`; the per-line hypothesis
is exactly `QASupport.minorant_of_second_order_support`'s premise list, and the absorbed loss is
the quadratic `e^2/(2m)`.  (`QASupport` is standalone-checked but not root-imported.) -/
theorem gamma_mixture_of_QA {ι : Type*} [Fintype ι] {a b : ℝ} (γ : ι → ℝ)
    (hγ0 : ∀ l, 0 ≤ γ l) (hγ1 : ∑ l, γ l = 1) (hab : a ≤ b)
    (m t s c e : ι → ℝ) (hm0 : ∀ l, 0 < m l)
    (hcos : ∀ l, ∀ z ∈ Set.Icc a b, m l ≤ Real.cos z) (ht : ∀ l, t l ∈ Set.Icc a b)
    (he : ∀ l, 0 ≤ e l) (hs : ∀ l, |Real.sin (t l) - s l| ≤ e l)
    (hc : ∀ l, c l ≤ 1 - Real.cos (t l) - s l * t l - (e l) ^ 2 / (2 * m l)) :
    ∀ z ∈ Set.Icc a b, (∑ l, γ l * s l) * z + (∑ l, γ l * c l) ≤ 1 - Real.cos z :=
  gamma_mixture_minorant γ hγ0 hγ1 s c fun l =>
    QASupport.minorant_of_second_order_support hab (hm0 l) (hcos l) (ht l) (he l) (hs l) (hc l)

/-! ## 6. Calibration instance (known answer) and the `γ ≥ 0` negative control -/

/-- Calibration data: two equal weights, both lines the zero line. -/
noncomputable def gammaCal : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- Calibration data: slopes. -/
def gammaCalS : Fin 2 → ℝ := fun _ => 0

/-- Calibration data: intercepts. -/
def gammaCalC : Fin 2 → ℝ := fun _ => 0

/-- **Calibration on a known answer**: with the *proved* two-line data (`s = 0`, `c = 0` on
both lines, valid on `[-1,1]` by the compiled `FlashCosineSupport.known_zero_support`), the
γ-mixture gives `0 ≤ 1 - cos z` for every `z ∈ [-1,1]`.  This only exercises the mixture
assembly, not the analytic rules. -/
theorem calibrate_zero_support :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (∑ l : Fin 2, gammaCal l * gammaCalS l) * z + (∑ l : Fin 2, gammaCal l * gammaCalC l)
        ≤ 1 - Real.cos z := by
  have hline : ∀ l : Fin 2, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      gammaCalS l * z + gammaCalC l ≤ 1 - Real.cos z := by
    intro l z hz
    fin_cases l <;> simpa [gammaCalS, gammaCalC] using
      FlashCosineSupport.known_zero_support z hz
  have hγ0 : ∀ l : Fin 2, 0 ≤ gammaCal l := by
    intro l; fin_cases l <;> norm_num [gammaCal]
  have hγ1 : ∑ l : Fin 2, gammaCal l = 1 := by norm_num [gammaCal, Fin.sum_univ_two]
  exact gamma_mixture_minorant gammaCal hγ0 hγ1 gammaCalS gammaCalC hline

/-- Negative-control weights: `γ = (2, -1)` — sums to `1`, but one weight is negative. -/
def ctrlG : Fin 2 → ℝ := fun k => match (k : ℕ) with | 0 => 2 | _ => -1

/-- Negative-control slopes: the zero line. -/
def ctrlS : Fin 2 → ℝ := fun _ => 0

/-- Negative-control intercepts: `c = (0, -1)`. -/
def ctrlC : Fin 2 → ℝ := fun k => match (k : ℕ) with | 0 => 0 | _ => -1

/-- Negative control: **`γ ≥ 0` cannot be dropped.**  Two valid minorants on `[0,1]`
(`l = 0`: `0·z + 0`; `l = 1`: `0·z - 1`; validity uses only `cos ≤ 1`) with the signed weights
`γ = (2, -1)` — still `Σ γ = 1`, but one weight is negative — have mixture value `1` at
`z = 0`, while `1 - cos 0 = 0`.  So the hypothesis `hγ0` in the lemmas above is load-bearing,
and the intended failure is mathematical (a violated sign), not a parse error. -/
theorem gamma_nonneg_necessary :
    (∑ l : Fin 2, ctrlG l = 1) ∧ (ctrlG 1 < 0)
      ∧ (∀ l : Fin 2, ∀ z ∈ Set.Icc (0 : ℝ) 1, ctrlS l * z + ctrlC l ≤ 1 - Real.cos z)
      ∧ ¬ (∀ z ∈ Set.Icc (0 : ℝ) 1,
            ∑ l : Fin 2, ctrlG l * (ctrlS l * z + ctrlC l) ≤ 1 - Real.cos z) := by
  refine ⟨by norm_num [ctrlG, Fin.sum_univ_two], by norm_num [ctrlG], ?_, ?_⟩
  · intro l z _
    fin_cases l <;> simp [ctrlS, ctrlC] <;> linarith [Real.cos_le_one z]
  · intro h
    have h0 := h 0 (by norm_num)
    have hL : (∑ l : Fin 2, ctrlG l * (ctrlS l * 0 + ctrlC l)) = 1 := by
      norm_num [ctrlG, ctrlS, ctrlC, Fin.sum_univ_two]
    rw [hL, Real.cos_zero, sub_self] at h0
    exact absurd h0 (by norm_num)

end N11Formalization.FlashCosineMixture

/-! Full consumer types (all arguments explicit; no `#print` of proof terms). -/

#check @N11Formalization.FlashCosineMixture.gamma_mixture_is_affine
#check @N11Formalization.FlashCosineMixture.gamma_mixture_at
#check @N11Formalization.FlashCosineMixture.pair_mixture_lower_bound
#check @N11Formalization.FlashCosineMixture.gamma_mixture_minorant
#check @N11Formalization.FlashCosineMixture.mixture_energy_ge_affine
#check @N11Formalization.FlashCosineMixture.mixture_energy_ge_recorded
#check @N11Formalization.FlashCosineMixture.gamma_mixture_of_approx_support
#check @N11Formalization.FlashCosineMixture.gamma_mixture_of_QA
#check @N11Formalization.FlashCosineMixture.calibrate_zero_support
#check @N11Formalization.FlashCosineMixture.gamma_nonneg_necessary

#print axioms N11Formalization.FlashCosineMixture.gamma_mixture_is_affine
#print axioms N11Formalization.FlashCosineMixture.gamma_mixture_at
#print axioms N11Formalization.FlashCosineMixture.pair_mixture_lower_bound
#print axioms N11Formalization.FlashCosineMixture.gamma_mixture_minorant
#print axioms N11Formalization.FlashCosineMixture.mixture_energy_ge_affine
#print axioms N11Formalization.FlashCosineMixture.mixture_energy_ge_recorded
#print axioms N11Formalization.FlashCosineMixture.gamma_mixture_of_approx_support
#print axioms N11Formalization.FlashCosineMixture.gamma_mixture_of_QA
#print axioms N11Formalization.FlashCosineMixture.calibrate_zero_support
#print axioms N11Formalization.FlashCosineMixture.gamma_nonneg_necessary
