import N11Formalization.DBMSourceTreeData
import N11Formalization.Leaf4348Dispatch
import N11Formalization.Leaf4348Radius

/-!
  **Leaf 4348 tree bridge: the SOURCE-TREE kernel identity and the tree-cell payloads.**

  DRAFT for the Lead's serial slot.  No `sorry`, no custom `axiom`; the only `decide +kernel` uses
  are the committed integer-reduction pattern of `N11Formalization.Leaf284TreeBridge`.
  Mirrors that file (probed, not guessed); its `theta = anchorAngle` pair is deliberately not
  mirrored (leaf-284 chart fact; the payloads below need only the CELL identity).

  Pre-checked before emission: node-4348's `db` equals the source `db * 4096` for all 100
  entries, and its `terminal` flag is `true`.

  Wording: draft; the payloads it consumes (`Leaf4348Dispatch`, `Leaf4348Radius`) are still passing
  the serial gate queue, and this file itself has not been gated.
-/

namespace N11Formalization.Leaf4348TreeBridge

open DBMTreeKernel DBMSourceTree

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 400000000

/-- The node's DBM as integer data (the tree stores it at scale 4096). -/
def db4348 (i j : Fin 10) : ℤ := match (i : ℕ), (j : ℕ) with
  | 0, 0 => 0
  | 0, 1 => 88
  | 0, 2 => 96
  | 0, 3 => 176
  | 0, 4 => 1392
  | 0, 5 => 1952
  | 0, 6 => 2144
  | 0, 7 => 2336
  | 0, 8 => 2880
  | 0, 9 => 4096
  | 1, 0 => -40
  | 1, 1 => 0
  | 1, 2 => 48
  | 1, 3 => 128
  | 1, 4 => 1344
  | 1, 5 => 1904
  | 1, 6 => 2096
  | 1, 7 => 2288
  | 1, 8 => 2832
  | 1, 9 => 4056
  | 2, 0 => -80
  | 2, 1 => -8
  | 2, 2 => 0
  | 2, 3 => 88
  | 2, 4 => 1312
  | 2, 5 => 1872
  | 2, 6 => 2048
  | 2, 7 => 2256
  | 2, 8 => 2800
  | 2, 9 => 4016
  | 3, 0 => -168
  | 3, 1 => -80
  | 3, 2 => -72
  | 3, 3 => 0
  | 3, 4 => 1224
  | 3, 5 => 1784
  | 3, 6 => 1976
  | 3, 7 => 2168
  | 3, 8 => 2712
  | 3, 9 => 3928
  | 4, 0 => -1384
  | 4, 1 => -1304
  | 4, 2 => -1296
  | 4, 3 => -1216
  | 4, 4 => 0
  | 4, 5 => 560
  | 4, 6 => 752
  | 4, 7 => 944
  | 4, 8 => 1488
  | 4, 9 => 2712
  | 5, 0 => -1936
  | 5, 1 => -1848
  | 5, 2 => -1840
  | 5, 3 => -1760
  | 5, 4 => -544
  | 5, 5 => 0
  | 5, 6 => 208
  | 5, 7 => 400
  | 5, 8 => 944
  | 5, 9 => 2160
  | 6, 0 => -2128
  | 6, 1 => -2056
  | 6, 2 => -2032
  | 6, 3 => -1960
  | 6, 4 => -736
  | 6, 5 => -176
  | 6, 6 => 0
  | 6, 7 => 208
  | 6, 8 => 752
  | 6, 9 => 1968
  | 7, 0 => -2328
  | 7, 1 => -2240
  | 7, 2 => -2232
  | 7, 3 => -2160
  | 7, 4 => -936
  | 7, 5 => -376
  | 7, 6 => -184
  | 7, 7 => 0
  | 7, 8 => 552
  | 7, 9 => 1768
  | 8, 0 => -2872
  | 8, 1 => -2792
  | 8, 2 => -2784
  | 8, 3 => -2704
  | 8, 4 => -1480
  | 8, 5 => -928
  | 8, 6 => -736
  | 8, 7 => -536
  | 8, 8 => 0
  | 8, 9 => 1224
  | 9, 0 => -4096
  | 9, 1 => -4008
  | 9, 2 => -4000
  | 9, 3 => -3920
  | 9, 4 => -2704
  | 9, 5 => -2144
  | 9, 6 => -1952
  | 9, 7 => -1760
  | 9, 8 => -1216
  | 9, 9 => 0
  | _, _ => 0

/-- The kernel identity: the source tree's node-4348 carries exactly this table. -/
theorem db4348_eq : ∀ i j : Fin 10, (data (4348 : Fin 5011)).db i j = db4348 i j := by
  decide +kernel

/-- Rational bridge, two-step on purpose: the kernel handles integer arithmetic, `norm_num` the ℚ
literals (precedent: the committed `rowb_dbm`).  `decide +kernel` on `Rat.div`/`natGcd` with big
numerals is not guaranteed to be kernel-reducible, exactly as the committed bridge documents. -/
theorem leaf4348_dbm_eq (i j : Fin 10) :
    (((data (4348 : Fin 5011)).db i j : ℚ) / 4096) = N11Formalization.Leaf4348LP.dbm i j := by
  rw [db4348_eq i j]
  fin_cases i <;> fin_cases j <;> norm_num [db4348, N11Formalization.Leaf4348LP.dbm]

/-- Real matrix identity (the form the cell statements use). -/
theorem leaf4348_matrix_eq (i j : Fin 10) :
    matrix data 4096 (4348 : Fin 5011) i j = (N11Formalization.Leaf4348LP.dbm i j : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (leaf4348_dbm_eq i j)
  push_cast at h
  simpa [matrix] using h

/-- Cell transfer: the tree cell at node 4348 is exactly the `Leaf4348LP.dbm` cell. -/
theorem leaf4348_cell_iff (t : Fin 10 → ℝ) :
    FlashLeafSplit.Cell (matrix data 4096 (4348 : Fin 5011)) t ↔
      FlashLeafSplit.Cell (fun i j => (N11Formalization.Leaf4348LP.dbm i j : ℝ)) t := by
  constructor
  · intro h i j
    simpa [leaf4348_matrix_eq i j] using h i j
  · intro h i j
    simpa [leaf4348_matrix_eq i j] using h i j

/-- The terminal flag of node 4348 (the tag a coverage consumer stops on). -/
theorem leaf4348_is_terminal : (data (4348 : Fin 5011)).terminal = true := by decide +kernel

/-- **Tree-cell payload**: on the tree's own cell at node 4348, with no `forall n, Valid data n`
hypothesis, the frozen threshold sits below the canonical oracle. -/
theorem leaf4348_tree_oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : FlashLeafSplit.Cell (matrix data 4096 (4348 : Fin 5011)) (FlashLeafSplit.tlift y)) :
    (N11Formalization.Leaf4348LP.T : ℝ) ^ 2
      < ResumeNetwork.V2 (fun j => circleMap (FlashCosine.theta y j)) :=
  N11Formalization.Leaf4348Dispatch.leaf4348_oracle_gt y hy0 hy1
    ((leaf4348_cell_iff (FlashLeafSplit.tlift y)).mp hcell)

/-- **Tree-cell radius consumer**. -/
theorem leaf4348_tree_radius_gt (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : FlashLeafSplit.Cell (matrix data 4096 (4348 : Fin 5011)) (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (fun j => circleMap (FlashCosine.theta y j)) C Z r) :
    (N11Formalization.Leaf4348LP.T : ℝ) < r :=
  N11Formalization.Leaf4348Radius.leaf4348_radius_gt y hy0 hy1
    ((leaf4348_cell_iff (FlashLeafSplit.tlift y)).mp hcell) C Z r hf

/-! ## Mathematical negative controls (rejections are arithmetic, not parser) -/

/-- One-unit-lower mutation of the (0,1) entry of the table. -/
def dbmBad4348 (i j : Fin 10) : ℚ :=
  if i = 0 ∧ j = 1 then (87 : ℚ) / 4096
  else N11Formalization.Leaf4348LP.dbm i j

/-- The mutation is detected at that explicit entry. -/
theorem dbmBad4348_entry_mismatch :
    (((db4348 0 1 : ℚ) / 4096)) ≠ dbmBad4348 0 1 := by
  norm_num [dbmBad4348, N11Formalization.Leaf4348LP.dbm, db4348]

/-- Hence the bridge statement is not vacuous: the mutated table fails it. -/
theorem dbmBad4348_detected :
    ¬ (∀ i j : Fin 10,
      (((data (4348 : Fin 5011)).db i j : ℚ) / 4096) = dbmBad4348 i j) := by
  intro h
  have hmn := h 0 1
  rw [db4348_eq 0 1] at hmn
  exact dbmBad4348_entry_mismatch hmn

/-- Single-entry kernel value of node 285 at a row where it differs from node 4348. -/
theorem db285_entry_int :
    (data (285 : Fin 5011)).db (0 : Fin 10) (1 : Fin 10) = (256 : ℤ) := by
  decide +kernel

/-- That value is not the node-4348 table value. -/
theorem node285_entry_mismatch :
    ((((256 : ℤ)) : ℚ) / 4096)
      ≠ N11Formalization.Leaf4348LP.dbm (0 : Fin 10) (1 : Fin 10) := by
  norm_num [N11Formalization.Leaf4348LP.dbm]

/-- The leaf index is load-bearing: the same identity at node 285 fails. -/
theorem wrong_node_detected :
    ¬ (∀ i j : Fin 10,
      (((data (285 : Fin 5011)).db i j : ℚ) / 4096)
        = N11Formalization.Leaf4348LP.dbm i j) := by
  intro h
  have hij := h (0 : Fin 10) (1 : Fin 10)
  rw [db285_entry_int] at hij
  exact node285_entry_mismatch hij

#print axioms N11Formalization.Leaf4348TreeBridge.db4348_eq
#print axioms N11Formalization.Leaf4348TreeBridge.leaf4348_dbm_eq
#print axioms N11Formalization.Leaf4348TreeBridge.leaf4348_matrix_eq
#print axioms N11Formalization.Leaf4348TreeBridge.leaf4348_cell_iff
#print axioms N11Formalization.Leaf4348TreeBridge.leaf4348_is_terminal
#print axioms N11Formalization.Leaf4348TreeBridge.leaf4348_tree_oracle_gt
#print axioms N11Formalization.Leaf4348TreeBridge.leaf4348_tree_radius_gt

end N11Formalization.Leaf4348TreeBridge
