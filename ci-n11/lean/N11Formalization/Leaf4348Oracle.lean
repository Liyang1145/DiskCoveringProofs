import Mathlib
import N11Formalization.Leaf4348Assembly
import N11Formalization.Leaf4348Fields7

/-!
  **Leaf 4348: whole DBM cell => `T^2 < V2 (circleMap ∘ theta)`.**

  DRAFT for the Lead's serial slot.  No `sorry`, no custom `axiom`, no `native_decide`.

  This is the payload the Lead asked for: the actual `V2` consumer at the leaf's chart points, with
  the whole-cell hypothesis (the DBM `Cell`) -- not a bare "mixture <= V2".  Its two inputs are

  * `Leaf4348Assembly.leaf4348_energy_gt` : `T^2 < pairEnergy4348 y` on the cell, which consumes
    the per-pair safe minorants (the pairs layer's `cell<i><j>` through the stage-B dispatch); the
    family is the only hypothesis left explicit here;
  * `Leaf4348Fields7.mixture_le_oracle` : `mixtureEnergy θ ≤ V2 (circleMap ∘ θ)` -- gate-green,
    the real field-level oracle consumer;

  glued by `mixture_identity4348`, which holds because `zval y i j` is *defined* as
  `theta y i - theta y j`.
-/

namespace N11Formalization.Leaf4348Oracle

open Finset ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeSchurEnergy
open N11Formalization.FlashCosine (Lq LQ Dq DQ Lc Dc L_mem D_mem tval zval zval_eq
  tval_sub lp_step9 theta)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 400000000

/-- The bridge's and the fields-file's weights are the same data (literal comparison). -/
theorem wt_data_eq (k : Fin 36) :
    N11Formalization.Leaf4348Bridge.wt k = N11Formalization.Leaf4348Fields7.wt k := by
  fin_cases k <;> norm_num [N11Formalization.Leaf4348Bridge.wt, N11Formalization.Leaf4348Fields7.wt]

/-- The field mixture at the chart points IS the leaf's pair energy. -/
theorem mixture_identity4348 (y : Fin 9 → ℝ) :
    N11Formalization.Leaf4348Fields7.mixtureEnergy (theta y)
      = N11Formalization.Leaf4348Assembly.pairEnergy4348 y := by
  unfold N11Formalization.Leaf4348Fields7.mixtureEnergy
    N11Formalization.Leaf4348Fields7.fieldEnergy
    N11Formalization.Leaf4348Assembly.pairEnergy4348 zval
  simp only [Finset.mul_sum]
  have hr : ∀ f : Fin 7, ∀ k : Fin 36,
      (N11Formalization.Leaf4348Fields7.beta f : ℝ) *
        (2 * (N11Formalization.Leaf4348Fields7.weight f k *
          (1 - Real.cos (theta y (N11Formalization.FlashCosineLeaf284Bridge.iOf k)
            - theta y (N11Formalization.FlashCosineLeaf284Bridge.jOf k))))) =
      ((N11Formalization.Leaf4348Fields7.beta f : ℝ) * 2 *
          N11Formalization.Leaf4348Fields7.weight f k) *
        (1 - Real.cos (theta y (N11Formalization.FlashCosineLeaf284Bridge.iOf k)
          - theta y (N11Formalization.FlashCosineLeaf284Bridge.jOf k))) := by
    intro f k; ring
  simp_rw [hr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- factor the (1 - cos) out of the inner sum FIRST: otherwise the `mixture_weights` pattern does
  -- not occur (the gate reported exactly this at L59).
  rw [← Finset.sum_mul, ← N11Formalization.Leaf4348Fields7.mixture_weights k, ← wt_data_eq k]

/-- **The payload**: on the whole cell, the frozen threshold is below the canonical oracle. -/
theorem leaf4348_oracle_gt (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : N11Formalization.FlashLeafSplit.Cell
      (fun i j => (N11Formalization.Leaf4348LP.dbm i j : ℝ))
      (N11Formalization.FlashLeafSplit.tlift y))
    (hsafe : ∀ k : Fin 36,
      (N11Formalization.Leaf4348Bridge.wt k : ℝ) *
        ((N11Formalization.Leaf4348Bridge.sl k : ℝ) *
            zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k)
              (N11Formalization.FlashCosineLeaf284Bridge.jOf k)
          + ((N11Formalization.Leaf4348Bridge.cc k : ℝ)
             - (N11Formalization.Leaf4348Assembly.dd k : ℝ)))
      ≤ (N11Formalization.Leaf4348Bridge.wt k : ℝ) *
        (1 - Real.cos (zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k)
          (N11Formalization.FlashCosineLeaf284Bridge.jOf k)))) :
    (N11Formalization.Leaf4348LP.T : ℝ) ^ 2
      < V2 (fun j => circleMap (theta y j)) := by
  have hl := N11Formalization.Leaf4348Assembly.leaf4348_energy_gt y hy0 hy1 hcell hsafe
  rw [← mixture_identity4348 y] at hl
  exact hl.trans_le (N11Formalization.Leaf4348Fields7.mixture_le_oracle (theta y))

#print axioms N11Formalization.Leaf4348Oracle.wt_data_eq
#print axioms N11Formalization.Leaf4348Oracle.mixture_identity4348
#print axioms N11Formalization.Leaf4348Oracle.leaf4348_oracle_gt

end N11Formalization.Leaf4348Oracle
