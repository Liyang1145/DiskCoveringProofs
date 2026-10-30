import N11Formalization.SevenClassQ0Deg3SectorPeak

/-! Lane A: adjacent-step reduction for the nine sector rows.

The edge bracket is reused algebraically through `sectorEdgeBridge`.  The
piecewise node table prevents using edge `MonotoneOn` results directly, so the
sector shape is factored into adjacent finite steps.  A prefix is monotone if
every step below its witness is monotone; a suffix is antitone if every step
at or above its witness is antitone. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorShape

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3UpperTables
open SevenClassQ0Deg3SectorPeak

def sectorValue (i : Fin 9) (k : Fin 2049) : ℚ :=
  sectorUpper (mu (nextSite i)) lam (nodeQ RatInterval.piHi 2048 k) (nodeBin k)

/-- The sector upper bracket is half an edge bracket plus the node segment. -/
theorem sectorEdgeBridge (muA lamA q a : ℚ) :
    2 * sectorUpper muA lamA q a =
      edgeUpper (2 * muA) q + (2 * a - sinLoNLag (2 * a)) + 4 * lamA * a := by
  unfold sectorUpper areaUpper edgeUpper
  ring

def SectorIncSteps (i : Fin 9) : Prop :=
  ∀ k : Fin 2048, k.val < (sectorWitness i).val →
    sectorValue i ⟨k.val, by omega⟩ ≤ sectorValue i ⟨k.val + 1, by omega⟩

def SectorDecSteps (i : Fin 9) : Prop :=
  ∀ k : Fin 2048, (sectorWitness i).val ≤ k.val →
    sectorValue i ⟨k.val + 1, by omega⟩ ≤ sectorValue i ⟨k.val, by omega⟩

theorem prefix_le_of_steps {α : Type} [Preorder α] (f : ℕ → α) {w : ℕ}
    (h : ∀ n < w, f n ≤ f (n + 1)) :
    ∀ k ≤ w, f k ≤ f w := by
  intro k hk
  refine Nat.le_induction (m := k) (P := fun n => n ≤ w → f k ≤ f n)
    (fun _ => le_rfl) ?_ w hk le_rfl
  intro n hkn ih hn1
  exact (ih (by omega)).trans (h n (by omega))

theorem suffix_le_of_steps {α : Type} [Preorder α] (f : ℕ → α) {w : ℕ}
    (h : ∀ n, w ≤ n → f (n + 1) ≤ f n) :
    ∀ k, w ≤ k → f k ≤ f w := by
  intro k hwk
  refine Nat.le_induction (m := w) (P := fun n => f n ≤ f w)
    le_rfl ?_ k hwk
  intro n hwn ih
  exact (h n hwn).trans ih

theorem sectorIncTo_of_steps (i : Fin 9) (h : SectorIncSteps i) : SectorIncTo i := by
  intro k hk
  let f : ℕ → ℚ := fun n => sectorValue i ⟨min n 2048, by omega⟩
  have hfw : (sectorWitness i).val ≤ 2048 := (sectorWitness i).isLt.le
  have hf : ∀ n < (sectorWitness i).val, f n ≤ f (n + 1) := by
    intro n hn
    have hnlt : n < 2048 := lt_of_lt_of_le hn hfw
    have hnmin : min n 2048 = n := min_eq_left hnlt.le
    have hnsuccmin : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
    simpa [f, hnmin, hnsuccmin] using h ⟨n, hnlt⟩ hn
  have hmain := prefix_le_of_steps f (w := (sectorWitness i).val) hf k.val hk
  simpa [f, sectorValue, Nat.min_eq_left (show k.val ≤ 2048 by omega), hfw] using hmain

theorem sectorDecFrom_of_steps (i : Fin 9) (h : SectorDecSteps i) : SectorDecFrom i := by
  intro k hk
  let f : ℕ → ℚ := fun n => sectorValue i ⟨min n 2048, by omega⟩
  have hfw : (sectorWitness i).val ≤ 2048 := (sectorWitness i).isLt.le
  have hf : ∀ n, (sectorWitness i).val ≤ n → f (n + 1) ≤ f n := by
    intro n hwn
    by_cases hn : n < 2048
    · have hnmin : min n 2048 = n := min_eq_left hn.le
      have hnsuccmin : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
      simpa [f, hnmin, hnsuccmin] using h ⟨n, hn⟩ hwn
    · have hnmin : min n 2048 = 2048 := min_eq_right (by omega)
      have hnsuccmin : min (n + 1) 2048 = 2048 := min_eq_right (by omega)
      simp [f, hnmin, hnsuccmin]
  have hmain := suffix_le_of_steps f (w := (sectorWitness i).val) hf k.val hk
  simpa [f, sectorValue, Nat.min_eq_left (show k.val ≤ 2048 by omega), hfw] using hmain

def SectorAdjacentUnimodal : Prop :=
  ∀ i : Fin 9, SectorIncSteps i ∧ SectorDecSteps i

theorem sectorUnimodal_of_adjacent (h : SectorAdjacentUnimodal) : SectorUnimodal := by
  intro i
  exact ⟨sectorIncTo_of_steps i (h i).1, sectorDecFrom_of_steps i (h i).2⟩

end N11Formalization.SevenClassQ0Deg3SectorShape
#check @N11Formalization.SevenClassQ0Deg3SectorShape.sectorEdgeBridge
#check @N11Formalization.SevenClassQ0Deg3SectorShape.sectorUnimodal_of_adjacent
#print axioms N11Formalization.SevenClassQ0Deg3SectorShape.sectorUnimodal_of_adjacent
