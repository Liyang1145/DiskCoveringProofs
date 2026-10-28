import Mathlib

/-!
# FlashLeafSplit — the concrete source split at the tree root, disposed

Matrices read off `cosine_dbm_local920.json` (rules verified entrywise against the source by
`evidence/flash-leaves/gen_tables.py`: 0 mismatches for both children).

## Conventions (source-aligned; `t_0 = 0`, `t_9 = 1`)

* chart `y : Fin 9 → ℝ`, `y ≥ 0`, `∑_{q<9} y_q = 1` (**`Fin 9`**, not `Fin 8, Σ = 1`);
* cumulative `t = tlift y`: `t_0 = 0`, `t_9 = 1`;
* cells store UPPER bounds on `t_j − t_i`: `Cell d t := ∀ i j, t_j − t_i ≤ d i j`.
  Orientation settled by exact data: min-plus closure of `root + {t_4 − t_0 ≤ 1/2}` reproduces
  node 1 entrywise, and `root + {t_0 − t_4 ≤ −1/2}` reproduces node 2.

## Matrix rules

* `L1` : `1/2` if `i < j ≤ 4`; `1` if `i < j`, `j ≥ 5`; `−1/2` if `i = 9`, `1 ≤ j ≤ 4`;
         `−1` if `(9,0)`; `0` otherwise.
* `R2` : `1` if `i < j`, `i ≤ 3`; `1/2` if `i < j`, `i ≥ 4`; `−1` if `(9,0)`;
         `−1/2` if `4 ≤ i ≤ 8`, `j = 0`; `0` otherwise.

## Proved

`split_cover` : for every chart point `y`, `Cell L1 (tlift y) ∨ Cell R2 (tlift y)` — the concrete
root split, disposed.  The proof uses only monotonicity of `k ↦ t_k`, `0 ≤ t_k`, `t_k ≤ 1`,
`t_0 = 0`, `t_9 = 1` and the split threshold.
-/

namespace N11Formalization.FlashLeafSplit

abbrev M := Fin 10 → Fin 10 → ℝ

/-! ## The `t`-lift -/

/-- `t_k = Σ_{q<k} y_q`. -/
def tlift (y : Fin 9 → ℝ) : Fin 10 → ℝ :=
  fun k => ∑ q ∈ Finset.univ.filter (fun q : Fin 9 => (q : ℕ) < (k : ℕ)), y q

theorem tlift_zero (y : Fin 9 → ℝ) : tlift y 0 = 0 := by
  unfold tlift
  rw [show (Finset.univ.filter (fun q : Fin 9 => (q : ℕ) < ((0 : Fin 10) : ℕ))) = ∅ from by
    ext q; simp]
  simp

theorem tlift_nine {y : Fin 9 → ℝ} (hy : ∑ q, y q = 1) : tlift y 9 = 1 := by
  unfold tlift
  rw [show (Finset.univ.filter (fun q : Fin 9 => (q : ℕ) < ((9 : Fin 10) : ℕ))) = Finset.univ
      from by ext q; simp, hy]

theorem tlift_nonneg {y : Fin 9 → ℝ} (hy : ∀ q, 0 ≤ y q) (k : Fin 10) : 0 ≤ tlift y k := by
  unfold tlift
  exact Finset.sum_nonneg (fun q _ => hy q)

theorem tlift_le_sum {y : Fin 9 → ℝ} (hy : ∀ q, 0 ≤ y q) (k : Fin 10) :
    tlift y k ≤ ∑ q, y q := by
  unfold tlift
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q _ _ => hy q)

theorem tlift_mono {y : Fin 9 → ℝ} (hy : ∀ q, 0 ≤ y q) {k j : Fin 10} (h : k ≤ j) :
    tlift y k ≤ tlift y j := by
  unfold tlift
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact lt_of_lt_of_le hq (Fin.le_iff_val_le_val.mp h)
  · intro q _ _; exact hy q

/-- `Cell d t` : every row of `d` bounds the corresponding difference of `t`. -/
def Cell (d : M) (t : Fin 10 → ℝ) : Prop := ∀ i j, t j - t i ≤ d i j

/-! ## The concrete matrices -/

/-- Stored LEFT child of the root (source node 1). -/
noncomputable def L1 : M := fun i j =>
  if i < j ∧ (j : ℕ) ≤ 4 then (1/2 : ℝ)
  else if i < j then 1
  else if i = 9 ∧ (1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 4) then (-1/2 : ℝ)
  else if i = 9 ∧ j = 0 then -1
  else 0

/-- Stored RIGHT child of the root (source node 2). -/
noncomputable def R2 : M := fun i j =>
  if i < j ∧ (i : ℕ) ≤ 3 then 1
  else if i < j then (1/2 : ℝ)
  else if i = 9 ∧ j = 0 then -1
  else if 4 ≤ (i : ℕ) ∧ j = 0 then (-1/2 : ℝ)
  else 0

/-- `t_k ≤ 1` on the chart. -/
theorem tlift_le_one {y : Fin 9 → ℝ} (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (k : Fin 10) : tlift y k ≤ 1 := by
  have := tlift_le_sum hy0 k; linarith

/-! ## The cover step -/

/-- **The concrete root split covers the chart.** -/
theorem split_cover {y : Fin 9 → ℝ} (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1) :
    Cell L1 (tlift y) ∨ Cell R2 (tlift y) := by
  have h9 : tlift y 9 = 1 := tlift_nine hy1
  have h0 : tlift y 0 = 0 := tlift_zero y
  have hnn : ∀ a : Fin 10, 0 ≤ tlift y a := tlift_nonneg hy0
  have hle1 : ∀ a : Fin 10, tlift y a ≤ 1 := tlift_le_one hy0 hy1
  have hm : ∀ a b : Fin 10, a ≤ b → tlift y a ≤ tlift y b := fun a b h => tlift_mono hy0 h
  have hle_of_not : ∀ a b : Fin 10, ¬ a < b → tlift y b ≤ tlift y a := by
    intro a b h; exact hm b a (le_of_not_gt h)
  by_cases hsplit : tlift y 4 - tlift y 0 ≤ (1/2 : ℝ)
  · left
    have h4 : tlift y 4 ≤ (1/2 : ℝ) := by linarith [hsplit, h0]
    -- every `t_j` with `j ≤ 4` is at most `1/2`
    have hj4 : ∀ j : Fin 10, (j : ℕ) ≤ 4 → tlift y j ≤ (1/2 : ℝ) :=
      fun j hj => le_trans (hm j 4 (Fin.le_iff_val_le_val.mpr hj)) h4
    intro i j
    unfold L1
    by_cases h1 : i < j ∧ (j : ℕ) ≤ 4
    · rw [if_pos h1]
      have hij : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp h1.1
      have hi4 : (i : ℕ) ≤ 4 := by omega
      have hj : tlift y j ≤ (1/2 : ℝ) := hj4 j h1.2
      have hi : 0 ≤ tlift y i := hnn i
      linarith
    · by_cases h2 : i < j
      · rw [if_neg h1, if_pos h2]
        have hj : tlift y j ≤ 1 := hle1 j
        have hi : 0 ≤ tlift y i := hnn i
        linarith
      · by_cases h3 : i = 9 ∧ (1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 4)
        · rw [if_neg h1, if_neg h2, if_pos h3]
          have hj : tlift y j ≤ (1/2 : ℝ) := hj4 j h3.2.2
          rw [h3.1]
          linarith
        · by_cases h4c : i = 9 ∧ j = 0
          · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4c]
            rw [h4c.1, h4c.2]
            linarith
          · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4c]
            have hji : tlift y j ≤ tlift y i := hle_of_not i j h2
            linarith
  · right
    have h4gt : (1/2 : ℝ) < tlift y 4 := by linarith [hsplit, h0]
    -- every `t_i` with `4 ≤ i` exceeds `1/2`
    have hi4 : ∀ i : Fin 10, 4 ≤ (i : ℕ) → (1/2 : ℝ) < tlift y i :=
      fun i hi => lt_of_lt_of_le h4gt (hm 4 i (Fin.le_iff_val_le_val.mpr hi))
    intro i j
    unfold R2
    by_cases h1 : i < j ∧ (i : ℕ) ≤ 3
    · rw [if_pos h1]
      have hj : tlift y j ≤ 1 := hle1 j
      have hi : 0 ≤ tlift y i := hnn i
      linarith
    · by_cases h2 : i < j
      · rw [if_neg h1, if_pos h2]
        have hi3 : 4 ≤ (i : ℕ) := by
          have hiv : (i : ℕ) ≤ 9 := Fin.le_last i
          omega
        have hti : (1/2 : ℝ) < tlift y i := hi4 i hi3
        have hj : tlift y j ≤ 1 := hle1 j
        linarith
      · by_cases h3 : i = 9 ∧ j = 0
        · rw [if_neg h1, if_neg h2, if_pos h3]
          rw [h3.1, h3.2]
          linarith
        · by_cases h4c : 4 ≤ (i : ℕ) ∧ j = 0
          · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4c]
            have hti : (1/2 : ℝ) < tlift y i := hi4 i h4c.1
            rw [h4c.2]
            linarith [h0, hti]
          · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4c]
            have hji : tlift y j ≤ tlift y i := hle_of_not i j h2
            linarith

end N11Formalization.FlashLeafSplit

#print axioms N11Formalization.FlashLeafSplit.split_cover
#print axioms N11Formalization.FlashLeafSplit.tlift_nine
#print axioms N11Formalization.FlashLeafSplit.tlift_mono
