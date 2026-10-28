/-
  Leaf284TreeBridge (v2) — auditor-side interface file (lives under
  evidence/team-resume-20260930/tree-audit/; NOT a shared/root module).

  v2 (2026-09-30 20:0x): single delta vs v1 `Leaf284TreeBridge.lean`
  (SHA256 8596B647D576A37ADC50245FF684DA185DC09BA57C38DB8BB206F82D128520C5, kept as history):
  explicit `Fin 9` binder domains on `theta_funext_anchorAngle` (v1 failed elaboration with the
  right lambda inferred as `ℕ → ℝ` vs expected `Fin 9 → ℝ`).  No other change.

  Purpose: connect the literal DBM tree witness
      `FlashLeafSplit.Cell (matrix DBMSourceTree.data 4096 284) t`
  (the object a future full-tree consumer obtains from `terminal_cover`) to the
  existing leaf-284 consumers
      `FlashCosineLeaf284Oracle.leaf284_oracle_gt` / `leaf284_radius_gt`,
  whose cell hypothesis is stated with the rational table `FlashCosineLeaf284Bridge.dbm`.

  Provenance (auditor-verified, 2026-09-30):
    * `lean/N11Formalization/DBMSourceTreeData.lean` SHA256 BD4E71CB29804A5A3D5953727558F4656D23253A83B69F5C3D6E25EEB4EA8ED5
      (LF-normalised D4ADF6A06F2A319FF36BFF0C7D86364025BEEBE3952AA8FE22D8562A2C3EBA1E),
      bound entrywise to the source JSON 6706B426... at scale 4096 (0 mismatches / 501100 entries).
    * `db284` below is machine-copied from the auditor's independent parse
      (`evidence/team-resume-20260930/tree-audit/literal_table.json`, node 284) and is
      re-bound to the emitted dispatcher in `db284_eq` by `decide +kernel`.
    * `FlashCosineLeaf284Bridge.dbm` is SHA-bound separately; the equality
      `(data 284).db / 4096 = dbm` is TRUE entrywise (auditor check: 100/100).

  This file adds no axiom, assumes no `forall n, Valid data n`, and claims no global
  coverage: it is exactly the leaf-284 interface.
-/
import N11Formalization.DBMSourceTreeData
import N11Formalization.FlashCosineLeaf284Oracle
import N11Formalization.ResumeGlobalAnchor

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace N11Formalization.Leaf284TreeBridge

open DBMTreeKernel DBMSourceTree

/-- Auditor transcription of node 284's integer rows (common scale 4096). -/
def db284 (i j : Fin 10) : ℤ := match (i : ℕ), (j : ℕ) with
  | 0, 0 => (0 : ℤ)
  | 0, 1 => (2048 : ℤ)
  | 0, 2 => (2048 : ℤ)
  | 0, 3 => (2048 : ℤ)
  | 0, 4 => (2048 : ℤ)
  | 0, 5 => (3072 : ℤ)
  | 0, 6 => (4096 : ℤ)
  | 0, 7 => (4096 : ℤ)
  | 0, 8 => (4096 : ℤ)
  | 0, 9 => (4096 : ℤ)
  | 1, 0 => (0 : ℤ)
  | 1, 1 => (0 : ℤ)
  | 1, 2 => (2048 : ℤ)
  | 1, 3 => (2048 : ℤ)
  | 1, 4 => (2048 : ℤ)
  | 1, 5 => (3072 : ℤ)
  | 1, 6 => (4096 : ℤ)
  | 1, 7 => (4096 : ℤ)
  | 1, 8 => (4096 : ℤ)
  | 1, 9 => (4096 : ℤ)
  | 2, 0 => (0 : ℤ)
  | 2, 1 => (0 : ℤ)
  | 2, 2 => (0 : ℤ)
  | 2, 3 => (2048 : ℤ)
  | 2, 4 => (2048 : ℤ)
  | 2, 5 => (3072 : ℤ)
  | 2, 6 => (4096 : ℤ)
  | 2, 7 => (4096 : ℤ)
  | 2, 8 => (4096 : ℤ)
  | 2, 9 => (4096 : ℤ)
  | 3, 0 => (-1024 : ℤ)
  | 3, 1 => (0 : ℤ)
  | 3, 2 => (0 : ℤ)
  | 3, 3 => (0 : ℤ)
  | 3, 4 => (1024 : ℤ)
  | 3, 5 => (2048 : ℤ)
  | 3, 6 => (2048 : ℤ)
  | 3, 7 => (2048 : ℤ)
  | 3, 8 => (3072 : ℤ)
  | 3, 9 => (3072 : ℤ)
  | 4, 0 => (-1024 : ℤ)
  | 4, 1 => (0 : ℤ)
  | 4, 2 => (0 : ℤ)
  | 4, 3 => (0 : ℤ)
  | 4, 4 => (0 : ℤ)
  | 4, 5 => (1024 : ℤ)
  | 4, 6 => (2048 : ℤ)
  | 4, 7 => (2048 : ℤ)
  | 4, 8 => (2048 : ℤ)
  | 4, 9 => (3072 : ℤ)
  | 5, 0 => (-2048 : ℤ)
  | 5, 1 => (0 : ℤ)
  | 5, 2 => (0 : ℤ)
  | 5, 3 => (0 : ℤ)
  | 5, 4 => (0 : ℤ)
  | 5, 5 => (0 : ℤ)
  | 5, 6 => (2048 : ℤ)
  | 5, 7 => (2048 : ℤ)
  | 5, 8 => (2048 : ℤ)
  | 5, 9 => (2048 : ℤ)
  | 6, 0 => (-2048 : ℤ)
  | 6, 1 => (0 : ℤ)
  | 6, 2 => (0 : ℤ)
  | 6, 3 => (0 : ℤ)
  | 6, 4 => (0 : ℤ)
  | 6, 5 => (0 : ℤ)
  | 6, 6 => (0 : ℤ)
  | 6, 7 => (2048 : ℤ)
  | 6, 8 => (2048 : ℤ)
  | 6, 9 => (2048 : ℤ)
  | 7, 0 => (-2048 : ℤ)
  | 7, 1 => (-1024 : ℤ)
  | 7, 2 => (-1024 : ℤ)
  | 7, 3 => (-1024 : ℤ)
  | 7, 4 => (-1024 : ℤ)
  | 7, 5 => (0 : ℤ)
  | 7, 6 => (0 : ℤ)
  | 7, 7 => (0 : ℤ)
  | 7, 8 => (1024 : ℤ)
  | 7, 9 => (2048 : ℤ)
  | 8, 0 => (-3072 : ℤ)
  | 8, 1 => (-2048 : ℤ)
  | 8, 2 => (-2048 : ℤ)
  | 8, 3 => (-2048 : ℤ)
  | 8, 4 => (-1024 : ℤ)
  | 8, 5 => (-1024 : ℤ)
  | 8, 6 => (0 : ℤ)
  | 8, 7 => (0 : ℤ)
  | 8, 8 => (0 : ℤ)
  | 8, 9 => (1024 : ℤ)
  | 9, 0 => (-4096 : ℤ)
  | 9, 1 => (-2048 : ℤ)
  | 9, 2 => (-2048 : ℤ)
  | 9, 3 => (-2048 : ℤ)
  | 9, 4 => (-2048 : ℤ)
  | 9, 5 => (-1024 : ℤ)
  | 9, 6 => (0 : ℤ)
  | 9, 7 => (0 : ℤ)
  | 9, 8 => (0 : ℤ)
  | 9, 9 => (0 : ℤ)
  | _, _ => 0

/-- Kernel binding of the transcription to the emitted dispatcher: node 284's rows
    are exactly `db284`.  (Integer equalities only; `decide +kernel` as requested.)
    Fallback if the whole-`∀` kernel reduction is too heavy:
    `fin_cases i <;> fin_cases j <;> decide +kernel`, or 100 per-entry lemmas. -/
theorem db284_eq : ∀ i j : Fin 10, (data (284 : Fin 5011)).db i j = db284 i j := by
  decide +kernel

/-- The rational bridge used by the leaf-284 consumers.
    Two-step on purpose: the kernel keeps only integer arithmetic (`decide +kernel`),
    while the ℚ literals are handled by `norm_num` (precedent: `rowb_dbm`).  A direct
    `∀ i j, ... := by decide +kernel` would ask the kernel to reduce `Rat.div`/`natGcd`
    on ~100-digit numerators, which is not guaranteed to be kernel-reducible. -/
theorem leaf284_dbm_eq (i j : Fin 10) :
    (((data (284 : Fin 5011)).db i j : ℚ) / 4096) = FlashCosineLeaf284Bridge.dbm i j := by
  rw [db284_eq i j]
  fin_cases i <;> fin_cases j <;> norm_num [db284, FlashCosineLeaf284Bridge.dbm]

/-- Real matrix identity (Rat.cast_div / Int.cast), the form the cell statements use.
    Fallback for the cast step: `exact_mod_cast leaf284_dbm_eq i j` then `simpa [matrix]`. -/
theorem leaf284_matrix_eq (i j : Fin 10) :
    matrix data 4096 (284 : Fin 5011) i j = (FlashCosineLeaf284Bridge.dbm i j : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (leaf284_dbm_eq i j)
  push_cast at h
  simpa [matrix] using h

/-- Cell transfer: the tree cell at node 284 is exactly the `dbm` cell. -/
theorem leaf284_cell_iff (t : Fin 10 → ℝ) :
    FlashLeafSplit.Cell (matrix data 4096 (284 : Fin 5011)) t ↔
      FlashLeafSplit.Cell (fun i j => (FlashCosineLeaf284Bridge.dbm i j : ℝ)) t := by
  constructor
  · intro h i j
    simpa [leaf284_matrix_eq i j] using h i j
  · intro h i j
    simpa [leaf284_matrix_eq i j] using h i j

/-- The explicit terminal flag of node 284 (the tag a coverage consumer stops on). -/
theorem leaf284_is_terminal : (data (284 : Fin 5011)).terminal = true := by decide +kernel

/-! ## Actual `theta` = canonical anchor angle at the Fin 9 index -/

/-- `FlashCosine.theta` (the actual angle used by the oracle) equals
    `ResumeGlobal.anchorAngle Lc Dc` at the Fin 9 index.  Reuses the existing
    `FlashCosineLeaf284Bridge.tval_eq_tlift`; the filter-sum form of `tlift` is definitional. -/
theorem theta_eq_anchorAngle (y : Fin 9 → ℝ) (i : Fin 9) :
    FlashCosine.theta y i = ResumeGlobal.anchorAngle FlashCosine.Lc FlashCosine.Dc y (i : ℕ) := by
  have h : FlashCosine.tval y (Fin.castSucc i)
      = ∑ j ∈ (Finset.univ.filter fun j : Fin 9 => (j : ℕ) < (i : ℕ)), y j := by
    rw [FlashCosineLeaf284Bridge.tval_eq_tlift]
    simp only [FlashLeafSplit.tlift, Fin.val_castSucc]
  unfold FlashCosine.theta ResumeGlobal.anchorAngle
  rw [h]

/-- Interface form: the 9 actual anchors are the canonical anchors.
    v2: both binders carry the explicit `Fin 9` domain (v1's right lambda was inferred `ℕ → ℝ`). -/
theorem theta_funext_anchorAngle (y : Fin 9 → ℝ) :
    (fun j : Fin 9 => FlashCosine.theta y j)
      = fun j : Fin 9 => ResumeGlobal.anchorAngle FlashCosine.Lc FlashCosine.Dc y (j : ℕ) := by
  funext j
  exact theta_eq_anchorAngle y j

/-! ## Consumers: source cell (scale 4096) + simplex ⇒ leaf-284 oracle/radius,
    with NO `forall n, Valid data n` hypothesis. -/

theorem leaf284_tree_oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : FlashLeafSplit.Cell (matrix data 4096 (284 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ) ^ 2
      < ResumeNetwork.V2 (fun j => circleMap (FlashCosine.theta y j)) :=
  FlashCosineLeaf284Oracle.leaf284_oracle_gt y hy0 hy1
    ((leaf284_cell_iff (FlashLeafSplit.tlift y)).mp hcell)

theorem leaf284_tree_radius_gt (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : FlashLeafSplit.Cell (matrix data 4096 (284 : Fin 5011)) (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (fun j => circleMap (FlashCosine.theta y j)) C Z r) :
    (FlashCosineLeaf284Bridge.T : ℝ) < r :=
  FlashCosineLeaf284Oracle.leaf284_radius_gt y hy0 hy1
    ((leaf284_cell_iff (FlashLeafSplit.tlift y)).mp hcell) C Z r hf

/-! ## Mathematical negative controls (rejections are arithmetic, not parser) -/

/-- One-unit-lower mutation of the (0,4) row of the `dbm` table. -/
def dbmBad (i j : Fin 10) : ℚ :=
  if i = 0 ∧ j = 4 then (2047 : ℚ) / 4096 else FlashCosineLeaf284Bridge.dbm i j

/-- The mutation is detected at an explicit entry: 2048/4096 = 1/2 ≠ 2047/4096. -/
theorem dbmBad_entry_mismatch :
    (((db284 0 4 : ℚ) / 4096)) ≠ dbmBad 0 4 := by
  norm_num [dbmBad, FlashCosineLeaf284Bridge.dbm, db284]

/-- Hence the bridge statement is not vacuous: the mutated table fails it. -/
theorem dbmBad_detected :
    ¬ (∀ i j : Fin 10,
      (((data (284 : Fin 5011)).db i j : ℚ) / 4096) = dbmBad i j) := by
  intro h
  have h04 := h 0 4
  rw [db284_eq 0 4] at h04
  exact dbmBad_entry_mismatch h04

/-- Explicit rational witness: `t_k = k/8` satisfies the original row (0,4)
    (1/2 ≤ 1/2) but violates the mutated row (1/2 ≤ 2047/4096 is false). -/
theorem row_mutation_witness :
    ((4 : ℕ) : ℝ) / 8 - ((0 : ℕ) : ℝ) / 8 ≤ (FlashCosineLeaf284Bridge.dbm 0 4 : ℝ)
      ∧ ¬ (((4 : ℕ) : ℝ) / 8 - ((0 : ℕ) : ℝ) / 8 ≤ (dbmBad 0 4 : ℝ)) := by
  constructor <;> norm_num [dbmBad, FlashCosineLeaf284Bridge.dbm]

/-- Single-entry kernel value of node 285 at a row where it differs from node 284. -/
theorem db285_entry_int :
    (data (285 : Fin 5011)).db (0 : Fin 10) (1 : Fin 10) = (256 : ℤ) := by
  decide +kernel

/-- The value at that entry is not the leaf-284 table value. -/
theorem node285_entry_mismatch :
    ((((256 : ℤ)) : ℚ) / 4096)
      ≠ FlashCosineLeaf284Bridge.dbm (0 : Fin 10) (1 : Fin 10) := by
  norm_num [FlashCosineLeaf284Bridge.dbm]

/-- The leaf index is load-bearing: the same row identity at id 285 fails. -/
theorem wrong_leaf_index_detected :
    ¬ (∀ i j : Fin 10,
      (((data (285 : Fin 5011)).db i j : ℚ) / 4096) = FlashCosineLeaf284Bridge.dbm i j) := by
  intro h
  have hij := h (0 : Fin 10) (1 : Fin 10)
  rw [db285_entry_int] at hij
  exact node285_entry_mismatch hij

end N11Formalization.Leaf284TreeBridge

#check @N11Formalization.Leaf284TreeBridge.db284_eq
#check @N11Formalization.Leaf284TreeBridge.leaf284_dbm_eq
#check @N11Formalization.Leaf284TreeBridge.leaf284_matrix_eq
#check @N11Formalization.Leaf284TreeBridge.leaf284_cell_iff
#check @N11Formalization.Leaf284TreeBridge.leaf284_is_terminal
#check @N11Formalization.Leaf284TreeBridge.theta_eq_anchorAngle
#check @N11Formalization.Leaf284TreeBridge.leaf284_tree_oracle_gt
#check @N11Formalization.Leaf284TreeBridge.leaf284_tree_radius_gt
#print axioms N11Formalization.Leaf284TreeBridge.db284_eq
#print axioms N11Formalization.Leaf284TreeBridge.leaf284_dbm_eq
#print axioms N11Formalization.Leaf284TreeBridge.leaf284_matrix_eq
#print axioms N11Formalization.Leaf284TreeBridge.leaf284_cell_iff
#print axioms N11Formalization.Leaf284TreeBridge.leaf284_is_terminal
#print axioms N11Formalization.Leaf284TreeBridge.theta_eq_anchorAngle
#print axioms N11Formalization.Leaf284TreeBridge.leaf284_tree_oracle_gt
#print axioms N11Formalization.Leaf284TreeBridge.leaf284_tree_radius_gt
#print axioms N11Formalization.Leaf284TreeBridge.dbmBad_detected
#print axioms N11Formalization.Leaf284TreeBridge.row_mutation_witness
#print axioms N11Formalization.Leaf284TreeBridge.wrong_leaf_index_detected
