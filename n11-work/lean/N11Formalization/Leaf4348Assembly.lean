import Mathlib
import N11Formalization.Leaf4348Bridge

/-!
  **Leaf 4348 assembly, V4 -- the drop payment carried by `lower4348`.**

  DRAFT for the Lead's serial slot.  No `sorry`, no custom `axiom`, no `native_decide`.

  V3 (kept for the record) had a bearing inference error: `T^2 < affine` plus
  `0 <= sum wt*dd` does NOT give `T^2 < affine - sum wt*dd`.  V4 adds the payment as a kernel
  lemma (`drop_margin`, an exact rational comparison against `lower4348`) and carries the
  lower bound through `affine_lower` instead of `affine_gt`.

  `stored`/`energy_lower` appear nowhere; the threshold is the exact frozen `T`.
-/

namespace N11Formalization.Leaf4348Assembly

open Finset
open N11Formalization.FlashCosine (Lq LQ Dq DQ Lc Dc L_mem D_mem tval zval zval_eq tval_sub
  theta)
open N11Formalization.Leaf4348Bridge (wt sl cc cl cv pairAffine affine pair_expand
  affine_identity)
open N11Formalization.Leaf4348LP (rowA rowb m4348 lower4348 T frozen_gt_T2 lower4348_eq
)
open N11Formalization.FlashCosineLeaf284Bridge (tval_eq_tlift)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 400000000

/-- Per-pair drop actually charged (the REAL per-line drops, not a uniform simplification). -/
def dd : Fin 36 → ℚ := ![
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 5000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000),
    ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000), ((1 : ℚ) / 100000000000)]

theorem wt_nonneg (k : Fin 36) : (0 : ℝ) ≤ (wt k : ℝ) := by
  fin_cases k <;> norm_num [wt]

theorem dd_nonneg (k : Fin 36) : (0 : ℝ) ≤ (dd k : ℝ) := by
  fin_cases k <;> norm_num [dd]

/-- The total charged drop, as one exact rational. -/
theorem dd_sum_eq : (∑ k : Fin 36, (wt k : ℝ) * (dd k : ℝ)) = (((7077534006193671694861741180281877669601132658890011995184835317781180253949117262371231355708065043477167004504970822689912217046727192657352695801473937884467317817645512674147221678532690900913479128668662891465232049354662610938499340269662910838873962266656648157877948662847971410358957685416687335499199650439847990641040716941815737587769836985774006914242200126895091781400851719769421596134712407648643811087439762433953896071977418450731715634531504390666528829469223308653348460047221584645864058394012485397302315020320488613796092557979381976092530467624845971766678446755249492247294463158380475372351174263481985385499881536770981178562188820647884454714020233296028057644183555453319455833331673755978416045187057341966312571870659660430921791459803963529760968053393852914580583135088136604768236259608347624193 : ℚ) / 763133819554422008957521888019925586948823953852947680675399258384692083216225133733317377799913617400483438276299641016616568454186905420427698691765104269417126053150500939468861688558708643688553181840445554762075155732386817930701843697695444637989948745587950845075267473936375146493290164431098985526440022542751006345348568593929745048687380601844894866883952383736176291700498786264561690040204099466610582411368676041533985567168002953885088022062927032606660274057238062169031213853835908522725127180918377834261543429062543710240093587819372420126424956883701461813546954851795906047352626118587218651139133882027754206943376333114106068042809992245498413949196310866015074687810774384446429398819824613172087532072704593945340460068101615234791365701481230715157773153977175024476187821892873795849881004000000000000000000000000) : ℝ) := by
  norm_num [wt, dd, Fin.sum_univ_succ]

/-- **THE PAYMENT** (this is the kernel fact V3 was missing): after charging the drops, the frozen
threshold still sits strictly below the LP lower bound. -/
theorem drop_margin : (T : ℝ) ^ 2 + (∑ k : Fin 36, (wt k : ℝ) * (dd k : ℝ)) < (lower4348 : ℝ) := by
  rw [dd_sum_eq, lower4348_eq]
  norm_num [T]

noncomputable def pairEnergy4348 (y : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 36, (wt k : ℝ) * (1 - Real.cos (zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k) (N11Formalization.FlashCosineLeaf284Bridge.jOf k)))

noncomputable def pairAffineSafe4348 (y : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 36, (wt k : ℝ) * ((sl k : ℝ) * zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k) (N11Formalization.FlashCosineLeaf284Bridge.jOf k)
    + ((cc k : ℝ) - (dd k : ℝ)))

/-- The safe affine form is the bridge's affine form minus the charged drop (a constant). -/
theorem pairAffineSafe_eq (y : Fin 9 → ℝ) :
    pairAffineSafe4348 y = pairAffine y - ∑ k : Fin 36, (wt k : ℝ) * (dd k : ℝ) := by
  unfold pairAffineSafe4348 pairAffine
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The only input still needed from the pairs layer: the per-pair safe minorants. -/
theorem safe_le_energy (y : Fin 9 → ℝ)
    (hsafe : ∀ k : Fin 36, (wt k : ℝ) * ((sl k : ℝ) * zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k) (N11Formalization.FlashCosineLeaf284Bridge.jOf k)
      + ((cc k : ℝ) - (dd k : ℝ)))
      ≤ (wt k : ℝ) * (1 - Real.cos (zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k) (N11Formalization.FlashCosineLeaf284Bridge.jOf k)))) :
    pairAffineSafe4348 y ≤ pairEnergy4348 y := by
  unfold pairAffineSafe4348 pairEnergy4348
  exact Finset.sum_le_sum fun k _ => hsafe k

/-- The leaf's payoff, carried through `lower4348` (V4): `affine_gt` is NOT used. -/
theorem leaf4348_energy_gt (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : N11Formalization.FlashLeafSplit.Cell (fun i j => (N11Formalization.Leaf4348LP.dbm i j : ℝ))
      (N11Formalization.FlashLeafSplit.tlift y))
    (hsafe : ∀ k : Fin 36, (wt k : ℝ) * ((sl k : ℝ) * zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k) (N11Formalization.FlashCosineLeaf284Bridge.jOf k)
      + ((cc k : ℝ) - (dd k : ℝ)))
      ≤ (wt k : ℝ) * (1 - Real.cos (zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k) (N11Formalization.FlashCosineLeaf284Bridge.jOf k)))) :
    (T : ℝ) ^ 2 < pairEnergy4348 y := by
  have hrow := N11Formalization.Leaf4348Bridge.rows_of_cell y hcell
  have haff : (lower4348 : ℝ) ≤ N11Formalization.Leaf4348Bridge.affine Lc Dc y :=
    N11Formalization.Leaf4348Bridge.affine_lower Lc Dc y L_mem D_mem.2 hy0 hy1 hrow
  have hpay := drop_margin
  have hid := N11Formalization.Leaf4348Bridge.affine_identity y
  have hsplit : N11Formalization.Leaf4348Bridge.affine Lc Dc y
      = pairAffineSafe4348 y + ∑ k : Fin 36, (wt k : ℝ) * (dd k : ℝ) := by
    rw [pairAffineSafe_eq, ← hid]
    ring
  have hsafe' := safe_le_energy y hsafe
  linarith [haff, hpay, hsplit, hsafe']

#print axioms N11Formalization.Leaf4348Assembly.wt_nonneg
#print axioms N11Formalization.Leaf4348Assembly.dd_nonneg
#print axioms N11Formalization.Leaf4348Assembly.dd_sum_eq
#print axioms N11Formalization.Leaf4348Assembly.drop_margin
#print axioms N11Formalization.Leaf4348Assembly.pairAffineSafe_eq
#print axioms N11Formalization.Leaf4348Assembly.safe_le_energy
#print axioms N11Formalization.Leaf4348Assembly.leaf4348_energy_gt

end N11Formalization.Leaf4348Assembly
