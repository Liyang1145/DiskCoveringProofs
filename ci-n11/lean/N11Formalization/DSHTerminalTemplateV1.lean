/-
  DSHTerminalTemplateV1 — DSH-TERM-T0: FULL-INTERFACE CLOSED-LOOP TEMPLATE for ONE energy terminal.

  Terminal paid here: the leaf-284 terminal of the source DBM tree
  (`N11Formalization.DBMSourceTree.data`, N = 5011, scale 4096, node 284).  Leaf 284 is the family
  whose every layer is already kernel-accepted end to end:
    * tree data + terminal flag + integer rows:  DBMSourceTreeData / DBMTreeKernel;
    * energy side F: `FlashCosineLeaf284Oracle.leaf284_oracle_gt` (leaf-284 whole-cell pair
      energy, its mixture identity, and the canonical 51-edge oracle).

  WHY NOT THE L0_G+_Z+ FAMILY (562, 984, 1112, 2166): that family is the SIMPLEST to *certify next*
  (lambda layer empty, gamma layer already root-imported as `GammaMixture`), but it is NOT yet
  kernel-paid: each of its 4 terminals needs 64 per-line minorants plus the intercept-drop step
  (term-survey's caliber warning: the stored `intercept_lower` is a ~78-80-digit terminating decimal
  string, so the per-line drop is required and cannot be replaced by an exact rational literal).
  This module therefore does NOT quantify its batch over those 4 ids — that would be a fake payment.
  The index-set machinery below is generic in the terminal id (`terminalIndexSet n`), so it is
  exactly the shape a later batch file must instantiate for those ids.

  WHAT THIS FILE IS (the seven payment items, for this one terminal)
  ==================================================================
  (1) EXACT TYPE + INDEX DOMAIN.  The terminal index domain is `Fin 5011` (the source tree's own
      index type).  A node counts as a terminal only through the kernel-checked pair
      `(data l).terminal = true` and the closed-cell membership
      `Cell (matrix data 4096 l) (tlift y)`.  Nothing else is accepted as "a terminal".
  (2) REAL INPUTS.  anchor map `anchorOf y = fun j => circleMap (theta y j)` (the actual canonical
      anchors of the Fin 9 chart); the integer DBM table of node 284, bound to the emitted
      dispatcher by `leaf284_dbm_eq` (kernel `decide +kernel` on integers plus `norm_num`, NOT a
      copied certificate); the center / face-auxiliary variables `C Z : Fin 11 → Point`; the
      radius `r` is a real input of the consumer, not a parameter of the terminal theorem.
  (3) ACTUAL DIRECTION.  The energy side is F = the leaf-284 whole-cell pair energy
      `FlashCosineLeaf284Energy.pairEnergy y`, and the direction used is the correct one
          F ≤ mixtureEnergy ≤ V2 (circleMap ∘ theta y)
      i.e. the weighted/stress energy is bounded ABOVE by the 51-edge oracle `ResumeNetwork.V2`
      (equivalently `V2 ≤ r^2` for feasible data, via `oracle_le_feasible`).  This file therefore
      proves `T^2 < V2 (anchorOf y)` and then `T < r`.  It never proves or uses `V2 ≤ F`.
  (4) COMPLETE BOUND INEQUALITY.  `T^2 < V2 (anchorOf y)` and, for every `Feasible` radius,
      `T < r`; the 51-edge consumer form is `T ≤ r`.
  (5) REAL KERNEL CONSUMER.  `dsh_terminal_leaf284_radius_from_witnesses` applies the terminal
      theorem to the 18 boundary + 33 face geometric witnesses (the shape of
      `ResumeNetwork.oracle_le_of_geometric_witnesses`) and outputs `T ≤ r`.  It is an actual
      application, not a `#check`.
  (6) DEGENERATE / BOUNDARY BRANCHES AND QUANTIFIERS.  `y` ranges over the CLOSED simplex
      (`∀ q, 0 ≤ y q` and `∑ q, y q = 1`): repeated anchors (zero components), both degenerate
      simplex endpoints, and the boundary row `(9,0)` of the DBM table are all inside the domain.
      The cell hypothesis is the CLOSED cell (`≤`), so cell-boundary points are included.  Every
      quantifier is explicit and every premise appears in the printed type.
  (7) EVIDENCE.  Source SHA256, standalone gate log + `.result.json`, module build log + binding
      JSON, verbatim `#check` types and `#print axioms`, in `evidence/dsh/terminals/template/`.

  WHAT THIS FILE IS NOT
  =====================
  * It is NOT a statement about arbitrary covers (`Covers c r`), NOT the unrestricted lower bound,
    and NOT a claim that all 5011 tree terminals are discharged.  The batch theorem is proved for
    the index set actually paid (`terminalIndexSet 284`); non-emptiness and the per-member
    conclusions are proved, exact cardinality `= 1` is NOT claimed (§4 lists it as a labelled gap).
  * No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `maxHeartbeats` bump, no
    float / decimal / Python premise.  The only non-kernel evidence outside Lean is the source hash.
  * The old C911 energy table is NOT used as a source response: the energy side is the accepted
    leaf-284 mixture (`mixture_identity`, `mixture_le_oracle`), the index data is derived from the
    emitted tree dispatcher, and node 285 is an explicit wrong-index negative control.
-/
import N11Formalization.DBMSourceTreeData
import N11Formalization.FlashCosineLeaf284Oracle
import N11Formalization.Leaf284TreeBridge

set_option autoImplicit false
set_option maxRecDepth 100000

namespace N11Formalization.DSHTerminalTemplate

open N11Formalization.DBMTreeKernel
open N11Formalization.DBMSourceTree
open N11Formalization.FlashLeafSplit

/-! ## §0  Real inputs of the terminal -/

/-- The threshold `T` of the threshold family (the frozen `T` of the leaf consumers). -/
noncomputable abbrev T : ℝ := (N11Formalization.FlashCosineLeaf284Bridge.T : ℝ)

/-- The canonical anchors of a chart `y` (the real input "anchor" of the terminal). -/
noncomputable abbrev anchorOf (y : Fin 9 → ℝ) : Fin 9 → Point :=
  fun j => circleMap (N11Formalization.FlashCosine.theta y j)

/-! ## §1  Exact terminal index domain and kernel binding of its real data -/

/-- The leaf-284 rational table equals the emitted dispatcher's rows (integer kernel check). -/
theorem leaf284_dbm_eq (i j : Fin 10) :
    (((data (284 : Fin 5011)).db i j : ℚ) / 4096)
      = N11Formalization.FlashCosineLeaf284Bridge.dbm i j :=
  N11Formalization.Leaf284TreeBridge.leaf284_dbm_eq i j

/-- The real matrix the leaf consumers use is exactly the emitted dispatcher's table at scale 4096. -/
theorem leaf284_matrix_eq (i j : Fin 10) :
    matrix data 4096 (284 : Fin 5011) i j
      = (N11Formalization.FlashCosineLeaf284Bridge.dbm i j : ℝ) :=
  N11Formalization.Leaf284TreeBridge.leaf284_matrix_eq i j

/-- Function-level form of the binding: the whole tree matrix is the leaf-284 table. -/
theorem leaf284_matrix_funext :
    (fun i j : Fin 10 => matrix data 4096 (284 : Fin 5011) i j)
      = fun i j : Fin 10 => (N11Formalization.FlashCosineLeaf284Bridge.dbm i j : ℝ) :=
  funext fun i => funext fun j => leaf284_matrix_eq i j

/-- Node 284 is a terminal of the emitted tree (kernel check on the dispatcher). -/
theorem leaf284_is_terminal : (data (284 : Fin 5011)).terminal = true :=
  N11Formalization.Leaf284TreeBridge.leaf284_is_terminal

/-! ## §2  The terminal theorem (payment items 1-4 and 6) -/

/-- **DSH-TERM-T0 terminal theorem.**  The leaf-284 terminal: for every point `y` of the CLOSED
    chart simplex whose lift lies in the CLOSED node-284 cell, the complete energy inequality
    `T^2 < V2 (anchorOf y)` holds, where `V2` is the canonical 51-edge oracle on the actual
    canonical anchors.  No stationarity, no source-value, no feasibility premise. -/
theorem dsh_terminal_leaf284 (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : Cell (matrix data 4096 (284 : Fin 5011)) (tlift y)) :
    T ^ 2 < N11Formalization.ResumeNetwork.V2 (anchorOf y) := by
  have hc : Cell (fun i j : Fin 10 =>
      (N11Formalization.FlashCosineLeaf284Bridge.dbm i j : ℝ)) (tlift y) := by
    intro i j
    have h1 := hcell i j
    rw [leaf284_matrix_eq i j] at h1
    exact h1
  exact N11Formalization.FlashCosineLeaf284Oracle.leaf284_oracle_gt y hy0 hy1 hc

/-- The terminal theorem in the radius direction: any feasible radius of the same 51-edge network
    exceeds `T`.  This is the form consumed by the unrestricted lower-bound route. -/
theorem dsh_terminal_leaf284_radius_gt (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : Cell (matrix data 4096 (284 : Fin 5011)) (tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : N11Formalization.ResumeNetwork.Feasible (anchorOf y) C Z r) :
    T < r := by
  have hc : Cell (fun i j : Fin 10 =>
      (N11Formalization.FlashCosineLeaf284Bridge.dbm i j : ℝ)) (tlift y) := by
    intro i j
    have h1 := hcell i j
    rw [leaf284_matrix_eq i j] at h1
    exact h1
  exact N11Formalization.FlashCosineLeaf284Oracle.leaf284_radius_gt y hy0 hy1 hc C Z r hf

/-! ## §3  The batch theorem: generic index set, instantiated at the paid terminal

`terminalIndexSet n` is the set of terminals of the emitted tree whose matrix is *the matrix of node
`n`* (compared at the integer level, hence decidable).  This is the shape a batch theorem must
quantify over: replace `n` by a family id and the per-terminal proof is the remaining obligation. -/

/-- The table predicate of a tree index, relative to a reference node `n`, at the consumer's own
    matrix (scale 4096). -/
def terminalTable (n : Fin 5011) (l : Fin 5011) : Prop :=
  ∀ i j : Fin 10, matrix data 4096 l i j = matrix data 4096 n i j

/-- The same predicate at the integer level (sharp, decidable). -/
def terminalTableInt (n : Fin 5011) (l : Fin 5011) : Prop :=
  ∀ i j : Fin 10, (data l).db i j = (data n).db i j

/-- Computable form of the table predicate, decided at the integer level. -/
def terminalTableBool (n : Fin 5011) (l : Fin 5011) : Bool :=
  (List.finRange 10).all fun i =>
    (List.finRange 10).all fun j =>
      decide ((data l).db i j = (data n).db i j)

/-- The real (matrix) table predicate is the integer table predicate. -/
theorem terminalTable_iff_int (n l : Fin 5011) : terminalTable n l ↔ terminalTableInt n l := by
  constructor
  · intro h i j
    have hmul : ((data l).db i j : ℝ) * 4096 = ((data n).db i j : ℝ) * 4096 := by
      have hR := h i j
      simp only [matrix] at hR
      field_simp at hR
      linarith
    have hint : (data l).db i j * 4096 = (data n).db i j * 4096 := by exact_mod_cast hmul
    exact mul_right_cancel₀ (by norm_num : (4096 : ℤ) ≠ 0) hint
  · intro h i j
    simp only [matrix, h i j]

/-- The integer table predicate is the computable form. -/
theorem terminalTableInt_iff_bool (n l : Fin 5011) :
    terminalTableInt n l ↔ terminalTableBool n l = true := by
  simp only [terminalTableInt, terminalTableBool, List.all_eq_true]
  constructor
  · intro h i _ j _
    exact decide_eq_true (h i j)
  · intro h i j
    exact of_decide_eq_true (h i (List.mem_finRange i) j (List.mem_finRange j))

/-- The index set of terminals carrying the table of the reference node `n`. -/
def terminalIndexSet (n : Fin 5011) : Finset (Fin 5011) :=
  Finset.univ.filter fun l => (data l).terminal && terminalTableBool n l

/-- Membership is exactly "terminal AND carries the table of `n`". -/
theorem mem_terminalIndexSet_iff (n l : Fin 5011) :
    l ∈ terminalIndexSet n ↔ ((data l).terminal = true ∧ terminalTable n l) := by
  simp only [terminalIndexSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.and_eq_true_iff, terminalTable_iff_int, terminalTableInt_iff_bool]

/-- The paid index set for the leaf-284 terminal. -/
def leaf284IndexSet : Finset (Fin 5011) := terminalIndexSet (284 : Fin 5011)

/-- Node 284 belongs to its own index set (so the batch quantifier is not vacuous). -/
theorem leaf284_mem_indexSet : (284 : Fin 5011) ∈ leaf284IndexSet := by
  rw [leaf284IndexSet, mem_terminalIndexSet_iff]
  exact ⟨leaf284_is_terminal, fun i j => rfl⟩

/-- Every member of the paid index set is a terminal of the emitted tree. -/
theorem terminal_of_mem_indexSet {l : Fin 5011} (hl : l ∈ leaf284IndexSet) :
    (data l).terminal = true :=
  ((mem_terminalIndexSet_iff (284 : Fin 5011) l).mp (by simpa only [leaf284IndexSet] using hl)).1

/-- Every member of the paid index set carries the leaf-284 table. -/
theorem table_of_mem_indexSet {l : Fin 5011} (hl : l ∈ leaf284IndexSet) :
    terminalTable (284 : Fin 5011) l :=
  ((mem_terminalIndexSet_iff (284 : Fin 5011) l).mp (by simpa only [leaf284IndexSet] using hl)).2

/-- The paid index set is nonempty, witnessed by node 284. -/
theorem leaf284IndexSet_nonempty : leaf284IndexSet.Nonempty :=
  ⟨(284 : Fin 5011), leaf284_mem_indexSet⟩

/-- **Batch theorem, honest paid index set.**  Every terminal carrying the leaf-284 table is
    discharged: for every chart point in its cell, the complete energy inequality holds.  The
    quantifier is exactly `l ∈ leaf284IndexSet`; nothing about other terminal tables is claimed. -/
theorem dsh_terminal_batch_leaf284 (l : Fin 5011) (hl : l ∈ leaf284IndexSet)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : Cell (matrix data 4096 l) (tlift y)) :
    T ^ 2 < N11Formalization.ResumeNetwork.V2 (anchorOf y) := by
  have htab := table_of_mem_indexSet hl
  have hc : Cell (fun i j : Fin 10 =>
      (N11Formalization.FlashCosineLeaf284Bridge.dbm i j : ℝ)) (tlift y) := by
    intro i j
    have h1 := hcell i j
    rw [htab i j, leaf284_matrix_eq i j] at h1
    exact h1
  exact N11Formalization.FlashCosineLeaf284Oracle.leaf284_oracle_gt y hy0 hy1 hc

/-- The batch theorem in the radius direction, same index set. -/
theorem dsh_terminal_batch_leaf284_radius_gt (l : Fin 5011) (hl : l ∈ leaf284IndexSet)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : Cell (matrix data 4096 l) (tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : N11Formalization.ResumeNetwork.Feasible (anchorOf y) C Z r) :
    T < r := by
  have htab := table_of_mem_indexSet hl
  have hc : Cell (matrix data 4096 (284 : Fin 5011)) (tlift y) := by
    intro i j
    have h1 := hcell i j
    rw [htab i j] at h1
    exact h1
  exact dsh_terminal_leaf284_radius_gt y hy0 hy1 hc C Z r hf

/-- Non-emptiness plus the per-member conclusions: exactly what the batch theorem uses. -/
theorem leaf284IndexSet_characterization :
    leaf284IndexSet.Nonempty ∧
      (∀ l ∈ leaf284IndexSet, (data l).terminal = true ∧ terminalTable (284 : Fin 5011) l) :=
  ⟨leaf284IndexSet_nonempty, fun _ hl => ⟨terminal_of_mem_indexSet hl, table_of_mem_indexSet hl⟩⟩

/-! ## §4  The wider batch: exact shape, explicitly labelled gap (NOT a payment) -/

/-- Shape of the wider batch theorem over an arbitrary family index list `S : Finset (Fin 5011)`:
    each listed terminal's own cell implies the same threshold conclusion.  For the L0_G+_Z+ family
    `S = {562, 984, 1112, 2166}` this is the shape a later batch file must prove; it is NOT proved
    here (those terminals' per-line minorants and intercept drops are unpaid). -/
def dsh_terminal_batch_shape (S : Finset (Fin 5011)) : Prop :=
  ∀ (l : Fin 5011), l ∈ S →
    (data l).terminal = true →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      Cell (matrix data 4096 l) (tlift y) →
      T ^ 2 < N11Formalization.ResumeNetwork.V2 (anchorOf y)

/-- The precise missing implication of the wider batch (documented interface note, NOT a payment).
    A full 51-edge feasibility witness batch must provide, for every chart point, the terminal `l`
    produced by the tree cover together with the single comparison `matrix l ≤ leaf-284 table`
    entrywise, so the returned leaf is identified with a dischargeable family member.  Without it
    the cover gives only `∃ l` and the concrete leaf consumers cannot be applied. -/
def dsh_terminal_missing_cell_le : Prop :=
  ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
    ∀ (l : Fin 5011), (data l).terminal = true →
      Cell (matrix data 4096 l) (tlift y) →
      ∀ i j : Fin 10, matrix data 4096 l i j
        ≤ (N11Formalization.FlashCosineLeaf284Bridge.dbm i j : ℝ)

/-- Conditional wider batch: IF the missing implication is supplied, the wider shape follows for
    every index list.  The hypothesis is visible in the printed type. -/
theorem dsh_terminal_batch_of_cell_le
    (hmiss : dsh_terminal_missing_cell_le) (S : Finset (Fin 5011)) :
    dsh_terminal_batch_shape S := by
  intro l _ hl y hy0 hy1 hcell
  have hc : Cell (fun i j : Fin 10 =>
      (N11Formalization.FlashCosineLeaf284Bridge.dbm i j : ℝ)) (tlift y) := by
    intro i j
    exact le_trans (hcell i j) (hmiss y hy0 hy1 l hl hcell i j)
  exact N11Formalization.FlashCosineLeaf284Oracle.leaf284_oracle_gt y hy0 hy1 hc

/-! ## §5  Real kernel consumer: the 51-edge geometric-witness interface -/

/-- The 18 boundary geometric witnesses (shape of `oracle_le_of_geometric_witnesses`; the auxiliary
    `Z` argument is carried for signature identity with the 51-edge consumer). -/
def residual51_boundary (U : Fin 9 → Point) (C _Z : Fin 11 → Point) (r : ℝ) : Prop :=
  ∀ i : Fin 9, ∀ side : Fin 2,
    dist (C ⟨i.val, by omega⟩) (U (N11Formalization.ResumeNetwork.anchorIndex i side)) ≤ r

/-- The 33 face geometric witnesses (shape of `oracle_le_of_geometric_witnesses`). -/
def residual51_faces (C Z : Fin 11 → Point) (r : ℝ) : Prop :=
  ∀ f : Fin 11, ∀ v : Fin 3,
    dist (C (N11Formalization.ResumeNetwork.face f v)) (Z f) ≤ r

/-- Both halves together: the full 51-edge feasibility witness for the canonical anchors. -/
def witnesses_hold (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ) : Prop :=
  residual51_boundary U C Z r ∧ residual51_faces C Z r

/-- The 51-edge witness batch is exactly `Feasible` on the canonical graph. -/
theorem feasible_of_witnesses {U : Fin 9 → Point} {C Z : Fin 11 → Point} {r : ℝ}
    (hr : 0 ≤ r) (h : witnesses_hold U C Z r) :
    N11Formalization.ResumeNetwork.Feasible U C Z r := by
  refine ⟨hr, ?_⟩
  intro e
  rcases e with ⟨i, side⟩ | ⟨f, v⟩
  · exact h.1 i side
  · exact h.2 f v

/-- **REAL KERNEL CONSUMER.**  The leaf-284 terminal, consumed through the 18 + 33 geometric
    witnesses: `T ≤ r` for every radius that carries a full 51-edge feasibility witness.  The
    terminal theorem is applied here (not merely `#check`ed), in the lower-bound direction. -/
theorem dsh_terminal_leaf284_radius_from_witnesses (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : Cell (matrix data 4096 (284 : Fin 5011)) (tlift y))
    (C Z : Fin 11 → Point) (r : ℝ) (hr : 0 ≤ r)
    (hw : witnesses_hold (anchorOf y) C Z r) :
    T ≤ r :=
  le_of_lt (dsh_terminal_leaf284_radius_gt y hy0 hy1 hcell C Z r
    (feasible_of_witnesses hr hw))

/-- The same consumer with the two halves of the witness separated (the literal call shape of
    `ResumeNetwork.oracle_le_of_geometric_witnesses`). -/
theorem dsh_terminal_leaf284_radius_of_geometric_witnesses (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : Cell (matrix data 4096 (284 : Fin 5011)) (tlift y))
    (C Z : Fin 11 → Point) (r : ℝ) (hr : 0 ≤ r)
    (hboundary : residual51_boundary (anchorOf y) C Z r)
    (hfaces : residual51_faces C Z r) :
    T ≤ r :=
  dsh_terminal_leaf284_radius_from_witnesses y hy0 hy1 hcell C Z r hr
    ⟨hboundary, hfaces⟩

/-- The oracle comparison in the exact shape of the 51-edge consumer: for the leaf-284 anchors,
    `V2 ≤ r^2` follows from the geometric witnesses. -/
theorem leaf284_oracle_le_of_witnesses (y : Fin 9 → ℝ)
    (C Z : Fin 11 → Point) (r : ℝ) (hr : 0 ≤ r)
    (hboundary : residual51_boundary (anchorOf y) C Z r)
    (hfaces : residual51_faces C Z r) :
    N11Formalization.ResumeNetwork.V2 (anchorOf y) ≤ r ^ 2 :=
  N11Formalization.ResumeNetwork.oracle_le_of_geometric_witnesses
    (U := anchorOf y) (C := C) (Z := Z) (r := r) hr hboundary hfaces

/-! ## §6  Negative controls (rejections are arithmetic, not parser failures) -/

/-- The arithmetic core of the control: the mutated entry `1638/4096` is strictly BELOW `4/9`, so
    the closed-cell inequality `4/9 ≤ entry` fails at the uniform chart.  (Checked: the naive
    "one-unit-lower" mutation `2047/4096 ≈ 0.4998` is ABOVE `4/9 ≈ 0.4444` and would NOT break the
    cell inequality — the direction matters, and getting it wrong would be a vacuous control.) -/
theorem dbmBad_entry_lt : (1638 : ℚ) / 4096 < (4 : ℚ) / 9 := by
  norm_num

/-- On a constant chart the lift difference over the row `(0,4)` is exactly `4 * c`. -/
theorem tlift_const_sub (c : ℝ) :
    tlift (fun _ : Fin 9 => c) 4 - tlift (fun _ : Fin 9 => c) 0 = 4 * c := by
  have hset : (Finset.univ.filter fun q : Fin 9 => (q : ℕ) < ((4 : Fin 10) : ℕ))
      = Finset.univ.image (fun q : Fin 4 => (⟨q.val, by have := q.isLt; omega⟩ : Fin 9)) := by
    ext q
    constructor
    · intro hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact Finset.mem_image.mpr ⟨⟨q.val, hq⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨a, -, ha⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← ha]
      exact a.isLt
  have hsub : tlift (fun _ : Fin 9 => c) 4 - tlift (fun _ : Fin 9 => c) 0
      = ∑ q ∈ (Finset.univ.filter fun q : Fin 9 => (q : ℕ) < ((4 : Fin 10) : ℕ)), c := by
    simp only [tlift]
    rw [show (Finset.univ.filter fun q : Fin 9 => (q : ℕ) < ((0 : Fin 10) : ℕ)) = ∅ from by
      ext q; simp]
    simp
  rw [hsub, hset, Finset.sum_image]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  · intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)

/-- **Negative control (arithmetic, not parser).**  Perturb the `(0,4)` entry of the leaf-284 table
    down to `1638/4096`: the resulting cell predicate is FALSE at the uniform chart, because the
    entry demands `4/9 ≤ 1638/4096` and `1638/4096 < 4/9`.  Hence the cell hypothesis is
    load-bearing. -/
theorem dbmBad_cell_false :
    ¬ Cell (fun i j : Fin 10 =>
        if i = 0 ∧ j = 4 then (1638 : ℚ) / 4096
        else N11Formalization.FlashCosineLeaf284Bridge.dbm i j)
      (tlift (fun _ : Fin 9 => (1 : ℝ) / 9)) := by
  intro h
  have h04 : tlift (fun _ : Fin 9 => (1 : ℝ) / 9) 4
      - tlift (fun _ : Fin 9 => (1 : ℝ) / 9) 0 ≤ ((1638 : ℚ) / 4096 : ℝ) := by
    have hh : tlift (fun _ : Fin 9 => (1 : ℝ) / 9) 4
        - tlift (fun _ : Fin 9 => (1 : ℝ) / 9) 0
        ≤ (if (0 : Fin 10) = 0 ∧ (4 : Fin 10) = 4 then ((1638 : ℚ) / 4096 : ℝ)
            else (N11Formalization.FlashCosineLeaf284Bridge.dbm 0 4 : ℝ)) := by
      simpa only [] using h 0 4
    rw [if_pos (show (0 : Fin 10) = 0 ∧ (4 : Fin 10) = 4 from ⟨rfl, rfl⟩)] at hh
    exact hh
  rw [tlift_const_sub] at h04
  have h4 : (4 : ℝ) / 9 ≤ ((1638 : ℚ) / 4096 : ℝ) := by linarith
  have hlt : ((1638 : ℚ) / 4096 : ℝ) < ((4 : ℚ) / 9 : ℝ) := by
    exact_mod_cast dbmBad_entry_lt
  linarith

/-- The real data of node 285 differs from the leaf-284 table at entry `(0,1)` (kernel check on the
    dispatcher), so the leaf index is load-bearing. -/
theorem node285_entry_int :
    (data (285 : Fin 5011)).db (0 : Fin 10) (1 : Fin 10) = (256 : ℤ) := by
  decide +kernel

/-- Hence node 285 does NOT carry the leaf-284 table. -/
theorem node285_not_leaf284_table : ¬ terminalTable (284 : Fin 5011) (285 : Fin 5011) := by
  intro h
  have hint := (terminalTable_iff_int (284 : Fin 5011) (285 : Fin 5011)).mp h
  have h01 := hint 0 1
  rw [node285_entry_int] at h01
  have h2 : (data (284 : Fin 5011)).db (0 : Fin 10) (1 : Fin 10) = (2048 : ℤ) := by
    rw [show (data (284 : Fin 5011)).db (0 : Fin 10) (1 : Fin 10)
      = N11Formalization.Leaf284TreeBridge.db284 0 1
      from N11Formalization.Leaf284TreeBridge.db284_eq 0 1]
    norm_num [N11Formalization.Leaf284TreeBridge.db284]
  rw [h2] at h01
  norm_num at h01

/-- Node 285 is outside the paid index set (the wrong-index control). -/
theorem node285_not_mem_indexSet : (285 : Fin 5011) ∉ leaf284IndexSet :=
  fun hmem => node285_not_leaf284_table (table_of_mem_indexSet hmem)

end N11Formalization.DSHTerminalTemplate

/-! ## §7  Verbatim interface printout (types and axioms) -/

#check @N11Formalization.DSHTerminalTemplate.T
#check @N11Formalization.DSHTerminalTemplate.anchorOf
#check @N11Formalization.DSHTerminalTemplate.leaf284_dbm_eq
#check @N11Formalization.DSHTerminalTemplate.leaf284_matrix_eq
#check @N11Formalization.DSHTerminalTemplate.leaf284_matrix_funext
#check @N11Formalization.DSHTerminalTemplate.leaf284_is_terminal
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284_radius_gt
#check @N11Formalization.DSHTerminalTemplate.terminalTable
#check @N11Formalization.DSHTerminalTemplate.terminalTableInt
#check @N11Formalization.DSHTerminalTemplate.terminalTableBool
#check @N11Formalization.DSHTerminalTemplate.terminalTable_iff_int
#check @N11Formalization.DSHTerminalTemplate.terminalTableInt_iff_bool
#check @N11Formalization.DSHTerminalTemplate.terminalIndexSet
#check @N11Formalization.DSHTerminalTemplate.mem_terminalIndexSet_iff
#check @N11Formalization.DSHTerminalTemplate.leaf284IndexSet
#check @N11Formalization.DSHTerminalTemplate.leaf284_mem_indexSet
#check @N11Formalization.DSHTerminalTemplate.terminal_of_mem_indexSet
#check @N11Formalization.DSHTerminalTemplate.table_of_mem_indexSet
#check @N11Formalization.DSHTerminalTemplate.leaf284IndexSet_nonempty
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_batch_leaf284
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_batch_leaf284_radius_gt
#check @N11Formalization.DSHTerminalTemplate.leaf284IndexSet_characterization
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_batch_shape
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_missing_cell_le
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_batch_of_cell_le
#check @N11Formalization.DSHTerminalTemplate.residual51_boundary
#check @N11Formalization.DSHTerminalTemplate.residual51_faces
#check @N11Formalization.DSHTerminalTemplate.witnesses_hold
#check @N11Formalization.DSHTerminalTemplate.feasible_of_witnesses
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284_radius_from_witnesses
#check @N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284_radius_of_geometric_witnesses
#check @N11Formalization.DSHTerminalTemplate.leaf284_oracle_le_of_witnesses
#check @N11Formalization.DSHTerminalTemplate.tlift_const_sub
#check @N11Formalization.DSHTerminalTemplate.dbmBad_entry_lt
#check @N11Formalization.DSHTerminalTemplate.dbmBad_cell_false
#check @N11Formalization.DSHTerminalTemplate.node285_entry_int
#check @N11Formalization.DSHTerminalTemplate.node285_not_leaf284_table
#check @N11Formalization.DSHTerminalTemplate.node285_not_mem_indexSet
#check @N11Formalization.ResumeNetwork.oracle_le_of_geometric_witnesses

#print axioms N11Formalization.DSHTerminalTemplate.leaf284_dbm_eq
#print axioms N11Formalization.DSHTerminalTemplate.leaf284_matrix_eq
#print axioms N11Formalization.DSHTerminalTemplate.leaf284_matrix_funext
#print axioms N11Formalization.DSHTerminalTemplate.leaf284_is_terminal
#print axioms N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284
#print axioms N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284_radius_gt
#print axioms N11Formalization.DSHTerminalTemplate.terminalTable_iff_int
#print axioms N11Formalization.DSHTerminalTemplate.terminalTableInt_iff_bool
#print axioms N11Formalization.DSHTerminalTemplate.mem_terminalIndexSet_iff
#print axioms N11Formalization.DSHTerminalTemplate.leaf284_mem_indexSet
#print axioms N11Formalization.DSHTerminalTemplate.terminal_of_mem_indexSet
#print axioms N11Formalization.DSHTerminalTemplate.table_of_mem_indexSet
#print axioms N11Formalization.DSHTerminalTemplate.leaf284IndexSet_nonempty
#print axioms N11Formalization.DSHTerminalTemplate.dsh_terminal_batch_leaf284
#print axioms N11Formalization.DSHTerminalTemplate.dsh_terminal_batch_leaf284_radius_gt
#print axioms N11Formalization.DSHTerminalTemplate.leaf284IndexSet_characterization
#print axioms N11Formalization.DSHTerminalTemplate.dsh_terminal_batch_of_cell_le
#print axioms N11Formalization.DSHTerminalTemplate.feasible_of_witnesses
#print axioms N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284_radius_from_witnesses
#print axioms N11Formalization.DSHTerminalTemplate.dsh_terminal_leaf284_radius_of_geometric_witnesses
#print axioms N11Formalization.DSHTerminalTemplate.leaf284_oracle_le_of_witnesses
#print axioms N11Formalization.DSHTerminalTemplate.tlift_const_sub
#print axioms N11Formalization.DSHTerminalTemplate.dbmBad_entry_lt
#print axioms N11Formalization.DSHTerminalTemplate.dbmBad_cell_false
#print axioms N11Formalization.DSHTerminalTemplate.node285_entry_int
#print axioms N11Formalization.DSHTerminalTemplate.node285_not_leaf284_table
#print axioms N11Formalization.DSHTerminalTemplate.node285_not_mem_indexSet
