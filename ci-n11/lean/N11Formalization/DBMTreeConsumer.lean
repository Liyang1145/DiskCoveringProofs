/-
# DBMTreeConsumer — consumer-first instantiation of `terminal_cover` on the real source DBM tree

## Object

* Source tree: `N11Formalization.DBMSourceTree.data : Fin 5011 → DBMTreeKernel.Node 5011`, emitted
  from `cosine_dbm_local920.json` (sha256 `6706b426…`) at integer scale 4096
  (`DBMSourceTreeData.lean`, `dbm-tree-emission.json`; 2505 splits / 2506 terminals).
  Kernel: accepted `DBMTreeKernel` (`Node`/`Valid`/`matrix`/`terminal_cover`, SHA `5A8A8A28…`).
* Chart: `y : Fin 9 → ℝ`, `0 ≤ y`, `Σ y = 1`; cumulative `t = FlashLeafSplit.tlift y`
  (`t_k = Σ_{q<k} y_q`) — the convention of the real leaf consumers
  (`FlashCosineLeaf284Energy` / `FlashCosineLeaf284Oracle`).

## Proved here (against the literal emitted rows, not an abstract root predicate)

1. `root_rows` — the root node's 100 integer rows, kernel-checked by `decide +kernel`.
2. `root_cell_chart9` — the source root cell `matrix data 4096 0` contains the whole real chart;
   unconditional (no `hv` used).
3. `cell_of_FlashLeafP` — bridge: skeleton root predicate `FlashLeaf.P` implies membership in the
   *actual* root cell (skeleton and literal data are not silently identified).
4. `tlift_eq_flashLeaf` — `FlashLeafSplit.tlift` and `FlashLeaf.tlift 9` are the same function.
5. Fin 8 route (`Chart8`/`lift8`), plus `lift8 = ResumeGlobal.extend` and `Chart8 ↔ InChart8`
   (the other live Fin 8 copy).
6. `terminal_cover_chart9` / `terminal_cover_chart8` — `DBMTreeKernel.terminal_cover` on the real
   root.

## NOT proved here (explicit interfaces)

* `hv : ∀ n : Fin 5011, Valid data n` is an explicit hypothesis of every terminal statement below.
  It is NOT discharged, NOT hidden, NOT weakened.  Chunked discharge and leaf semantics are the
  lead's integration steps.
* Not a certified whole-source-tree theorem, not arbitrary-`Covers` coverage, not a radius bound.
  Scope = full continuous source chart → terminal cell coverage, conditional on `hv`.
* No `sorry`, no `axiom`, no `native_decide`; sheet of full types + axioms at the end.

## Controls

* `uniform_chart_mem` — positive calibration at `y ≡ 1/9`.
* `root_cell_rejects_zero_lift` — the nonnegative lift of `y ≡ 0` (`Σy = 0 ≠ 1`) is rejected by the
  real root cell, so `Σy = 1` and the pin row are load-bearing (reader non-vacuous).
* `root_rows_naive_pattern_rejected` — the monotone-only row pattern is not the emitted one.
-/
import N11Formalization.DBMTreeKernel
import N11Formalization.DBMSourceTreeData
import N11Formalization.FlashLeafCover
import N11Formalization.ResumeGlobalDomain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace N11Formalization.DBMTreeConsumer

open N11Formalization.DBMTreeKernel (Valid matrix terminal_cover)

/-! ## 1. Literal root rows and index-frame identifications -/

/-- Actual root-row pattern of node 0 (integer rows at scale 4096): `4096` for `i < j`, the pin
`−4096` at `(9,0)`, `0` otherwise.  Kernel-checked against the emitted literal data by enumeration
over the 100 index pairs. -/
theorem root_rows : ∀ i j : Fin 10,
    (N11Formalization.DBMSourceTree.data (0 : Fin 5011)).db i j =
      (if (i : ℕ) < (j : ℕ) then (4096 : ℤ)
        else if i = 9 ∧ j = 0 then (-4096 : ℤ) else 0) := by
  decide +kernel

/-- Concrete pin entry of the literal root: `(9,0) ↦ −4096` (no `if` matching in the controls). -/
theorem root_db_nine_zero :
    (N11Formalization.DBMSourceTree.data (0 : Fin 5011)).db 9 0 = (-4096 : ℤ) := by
  decide +kernel

/-- The two `tlift` conventions (split kernel vs. skeleton) are the same function. -/
theorem tlift_eq_flashLeaf :
    N11Formalization.FlashLeafSplit.tlift = N11Formalization.FlashLeaf.tlift 9 := rfl

/-- The two live copies of the Fin 8 → Fin 9 lift are the same function. -/
theorem lift8_eq_extend :
    N11Formalization.FlashLeaf.lift8 = N11Formalization.ResumeGlobal.extend := rfl

/-- The two live copies of the Fin 8 chart predicate are the same predicate. -/
theorem chart8_iff_inChart8 (z : Fin 8 → ℝ) :
    N11Formalization.FlashLeaf.Chart8 z ↔ N11Formalization.ResumeGlobal.InChart8 z := Iff.rfl

/-! ## 2. The real chart is in the real root cell -/

/-- Row facts sufficient for the actual root cell: monotone drops `≤ 0`, rises `≤ 1`, pin
`t 0 − t 9 ≤ −1`.  All rows are the literal ones (`root_rows`), at scale 4096. -/
theorem cell_of_bound_rows (t : Fin 10 → ℝ)
    (hmono : ∀ i j : Fin 10, (j : ℕ) < (i : ℕ) → t j - t i ≤ 0)
    (hone : ∀ i j : Fin 10, (i : ℕ) < (j : ℕ) → t j - t i ≤ 1)
    (hpin : t 0 - t 9 ≤ -1) :
    N11Formalization.FlashLeafSplit.Cell
      (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011)) t := by
  intro i j
  unfold matrix
  rw [root_rows i j]
  by_cases hij : (i : ℕ) < (j : ℕ)
  · rw [if_pos hij]
    have h := hone i j hij
    norm_num
    linarith
  · rw [if_neg hij]
    by_cases h90 : i = 9 ∧ j = 0
    · rw [if_pos h90, h90.1, h90.2]
      norm_num
      linarith
    · rw [if_neg h90]
      by_cases heq : i = j
      · rw [heq]
        norm_num
      · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => heq (Fin.ext h)
        have hji : (j : ℕ) < (i : ℕ) :=
          lt_of_le_of_ne (Nat.le_of_not_lt hij) (Ne.symm hne)
        have h := hmono i j hji
        norm_num
        linarith

/-- **The real chart is in the real root cell** (unconditional; no `hv`). -/
theorem root_cell_chart9 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1) :
    N11Formalization.FlashLeafSplit.Cell
      (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011))
      (N11Formalization.FlashLeafSplit.tlift y) :=
  cell_of_bound_rows (N11Formalization.FlashLeafSplit.tlift y)
    (fun i j hji => by
      have hle : N11Formalization.FlashLeafSplit.tlift y j
          ≤ N11Formalization.FlashLeafSplit.tlift y i :=
        N11Formalization.FlashLeafSplit.tlift_mono hy0
          (Fin.le_iff_val_le_val.mpr (le_of_lt hji))
      linarith)
    (fun i j hij => by
      have hi : 0 ≤ N11Formalization.FlashLeafSplit.tlift y i :=
        N11Formalization.FlashLeafSplit.tlift_nonneg hy0 i
      have hj : N11Formalization.FlashLeafSplit.tlift y j ≤ 1 :=
        N11Formalization.FlashLeafSplit.tlift_le_one hy0 hy1 j
      linarith)
    (by
      rw [N11Formalization.FlashLeafSplit.tlift_zero y,
        N11Formalization.FlashLeafSplit.tlift_nine hy1]
      norm_num)

/-- Bridge: the skeleton root predicate `FlashLeaf.P` implies membership in the *actual* literal
root cell.  Consumers of the skeleton can enter the real tree through this. -/
theorem cell_of_FlashLeafP {t : Fin 10 → ℝ} (ht : N11Formalization.FlashLeaf.P t) :
    N11Formalization.FlashLeafSplit.Cell
      (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011)) t :=
  cell_of_bound_rows t
    (fun i j hji => ht.1.2 i j (Fin.lt_def.mpr hji))
    (fun i j hij => ht.1.1 i j (Fin.lt_def.mpr hij))
    ht.2.2.2

/-- Second route to `root_cell_chart9`: skeleton `root_contains_chart` + `cell_of_FlashLeafP`
(shares only `root_rows` with the first route; independent on the chart side). -/
theorem root_cell_chart9_via_P (y : Fin 9 → ℝ) (hy : N11Formalization.FlashLeaf.Chart9 y) :
    N11Formalization.FlashLeafSplit.Cell
      (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011))
      (N11Formalization.FlashLeafSplit.tlift y) := by
  rw [tlift_eq_flashLeaf]
  exact cell_of_FlashLeafP (N11Formalization.FlashLeaf.root_contains_chart hy)

/-- Fin 8 (generator free coordinates) form of the root coverage. -/
theorem root_cell_chart8 (z : Fin 8 → ℝ) (hz : N11Formalization.FlashLeaf.Chart8 z) :
    N11Formalization.FlashLeafSplit.Cell
      (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011))
      (N11Formalization.FlashLeafSplit.tlift (N11Formalization.FlashLeaf.lift8 z)) := by
  obtain ⟨h0, h1⟩ := N11Formalization.FlashLeaf.chart_of_chart8 hz
  exact root_cell_chart9 _ h0 h1

/-- Fin 8 route in the `ResumeGlobal` frame (the other live copy of the generator chart). -/
theorem root_cell_of_InChart8 (z : Fin 8 → ℝ) (hz : N11Formalization.ResumeGlobal.InChart8 z) :
    N11Formalization.FlashLeafSplit.Cell
      (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011))
      (N11Formalization.FlashLeafSplit.tlift (N11Formalization.ResumeGlobal.extend z)) := by
  rw [← lift8_eq_extend]
  exact root_cell_chart8 z ((chart8_iff_inChart8 z).mpr hz)

/-! ## 3. Terminal cover on the real root — with the explicit `hv` interface -/

/-- **Main consumer.** `DBMTreeKernel.terminal_cover` on the real root at scale 4096.
The validity interface `hv` is an explicit, undischarged hypothesis. -/
theorem terminal_cover_chart9
    (hv : ∀ n : Fin 5011, Valid N11Formalization.DBMSourceTree.data n)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1) :
    ∃ l : Fin 5011, (N11Formalization.DBMSourceTree.data l).terminal = true ∧
      N11Formalization.FlashLeafSplit.Cell
        (matrix N11Formalization.DBMSourceTree.data 4096 l)
        (N11Formalization.FlashLeafSplit.tlift y) :=
  terminal_cover N11Formalization.DBMSourceTree.data 4096 (by norm_num) hv
    (N11Formalization.FlashLeafSplit.tlift y) 0 (root_cell_chart9 y hy0 hy1)

/-- **Fin 8 consumer.** Same cover on the generator free chart; `hv` explicit. -/
theorem terminal_cover_chart8
    (hv : ∀ n : Fin 5011, Valid N11Formalization.DBMSourceTree.data n)
    (z : Fin 8 → ℝ) (hz : N11Formalization.FlashLeaf.Chart8 z) :
    ∃ l : Fin 5011, (N11Formalization.DBMSourceTree.data l).terminal = true ∧
      N11Formalization.FlashLeafSplit.Cell
        (matrix N11Formalization.DBMSourceTree.data 4096 l)
        (N11Formalization.FlashLeafSplit.tlift (N11Formalization.FlashLeaf.lift8 z)) :=
  terminal_cover N11Formalization.DBMSourceTree.data 4096 (by norm_num) hv
    (N11Formalization.FlashLeafSplit.tlift (N11Formalization.FlashLeaf.lift8 z)) 0
    (root_cell_chart8 z hz)

/-! ## 4. Explicit terminal id from the root-attainment walk (id preserved, energy NOT claimed) -/

/-- The terminal id reached by the root-attainment chart point (66 splits; external walk
`evidence/team-flash-20260930/root-attainment/tree_walk_terminal.py`, mpmath 80 dps) is a genuine
terminal of the literal emitted data.  Only the terminal flag of that id is formalized here; the
walk itself and any energy statement about it are NOT. -/
theorem terminal_4863_is_terminal :
    (N11Formalization.DBMSourceTree.data (4863 : Fin 5011)).terminal = true := by
  decide +kernel

/-! ## 5. Calibration controls -/

/-- Positive calibration: the uniform chart point `y ≡ 1/9` lies in the real root cell. -/
theorem uniform_chart_mem :
    N11Formalization.FlashLeafSplit.Cell
      (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011))
      (N11Formalization.FlashLeafSplit.tlift (fun _ : Fin 9 => (1 : ℝ) / 9)) :=
  root_cell_chart9 _ (fun _ => by norm_num) (by simp)

/-- Discriminating negative control: the nonnegative lift of `y ≡ 0` (`Σy = 0 ≠ 1`) is rejected by
the real root cell — the pin row `(9,0) = −4096` is load-bearing. -/
theorem root_cell_rejects_zero_lift :
    ¬ N11Formalization.FlashLeafSplit.Cell
        (matrix N11Formalization.DBMSourceTree.data 4096 (0 : Fin 5011))
        (N11Formalization.FlashLeafSplit.tlift (fun _ : Fin 9 => 0)) := by
  intro h
  have h90 := h 9 0
  have hz : ∀ k : Fin 10,
      N11Formalization.FlashLeafSplit.tlift (fun _ : Fin 9 => 0) k = 0 := by
    intro k
    simp [N11Formalization.FlashLeafSplit.tlift]
  unfold matrix at h90
  rw [root_db_nine_zero, hz 0, hz 9] at h90
  norm_num at h90

/-- Reader is discriminating: the naive monotone-only pattern (no pin row) is **not** the emitted
root matrix. -/
theorem root_rows_naive_pattern_rejected :
    ¬ (∀ i j : Fin 10, (N11Formalization.DBMSourceTree.data (0 : Fin 5011)).db i j =
        if (i : ℕ) < (j : ℕ) then (4096 : ℤ) else 0) := by
  intro h
  have h90 := h 9 0
  rw [root_db_nine_zero] at h90
  rw [if_neg (by decide : ¬ (((9 : Fin 10) : ℕ) < ((0 : Fin 10) : ℕ)))] at h90
  norm_num at h90

end N11Formalization.DBMTreeConsumer

#print N11Formalization.DBMTreeConsumer.root_rows
#print N11Formalization.DBMTreeConsumer.root_db_nine_zero
#print N11Formalization.DBMTreeConsumer.root_cell_chart9
#print N11Formalization.DBMTreeConsumer.terminal_cover_chart9
#print N11Formalization.DBMTreeConsumer.terminal_cover_chart8
#check @N11Formalization.DBMTreeConsumer.cell_of_bound_rows
#check @N11Formalization.DBMTreeConsumer.cell_of_FlashLeafP
#check @N11Formalization.DBMTreeConsumer.root_cell_chart9_via_P
#check @N11Formalization.DBMTreeConsumer.tlift_eq_flashLeaf
#check @N11Formalization.DBMTreeConsumer.lift8_eq_extend
#check @N11Formalization.DBMTreeConsumer.chart8_iff_inChart8
#check @N11Formalization.DBMTreeConsumer.root_cell_chart8
#check @N11Formalization.DBMTreeConsumer.root_cell_of_InChart8
#check @N11Formalization.DBMTreeConsumer.terminal_4863_is_terminal
#check @N11Formalization.DBMTreeConsumer.root_db_nine_zero
#check @N11Formalization.DBMTreeConsumer.uniform_chart_mem
#check @N11Formalization.DBMTreeConsumer.root_cell_rejects_zero_lift
#check @N11Formalization.DBMTreeConsumer.root_rows_naive_pattern_rejected
#print axioms N11Formalization.DBMTreeConsumer.root_rows
#print axioms N11Formalization.DBMTreeConsumer.root_db_nine_zero
#print axioms N11Formalization.DBMTreeConsumer.cell_of_bound_rows
#print axioms N11Formalization.DBMTreeConsumer.root_cell_chart9
#print axioms N11Formalization.DBMTreeConsumer.cell_of_FlashLeafP
#print axioms N11Formalization.DBMTreeConsumer.root_cell_chart9_via_P
#print axioms N11Formalization.DBMTreeConsumer.tlift_eq_flashLeaf
#print axioms N11Formalization.DBMTreeConsumer.lift8_eq_extend
#print axioms N11Formalization.DBMTreeConsumer.chart8_iff_inChart8
#print axioms N11Formalization.DBMTreeConsumer.root_cell_chart8
#print axioms N11Formalization.DBMTreeConsumer.root_cell_of_InChart8
#print axioms N11Formalization.DBMTreeConsumer.terminal_cover_chart9
#print axioms N11Formalization.DBMTreeConsumer.terminal_cover_chart8
#print axioms N11Formalization.DBMTreeConsumer.terminal_4863_is_terminal
#print axioms N11Formalization.DBMTreeConsumer.uniform_chart_mem
#print axioms N11Formalization.DBMTreeConsumer.root_cell_rejects_zero_lift
#print axioms N11Formalization.DBMTreeConsumer.root_rows_naive_pattern_rejected
