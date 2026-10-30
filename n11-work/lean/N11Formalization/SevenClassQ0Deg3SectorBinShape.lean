import N11Formalization.SevenClassQ0Deg3SectorCalculus

/-! Lane A: correct eight-bin reduction for the sector rows.

The global adjacent-step premise in `SevenClassQ0Deg3SectorShape` is false:
the piecewise node table jumps at `256, 512, ..., 1792`, so values can fall
inside a bin and rise at the next boundary.  This module keeps the exact
single-peaked shape separately on each bin.  No boundary jump is hidden. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBinShape

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3SectorPeak
open SevenClassQ0Deg3SectorShape

/-- A natural-indexed view of a sector row, truncated at the final node. -/
def sectorAt (i : Fin 9) (n : ℕ) : ℚ :=
  sectorValue i ⟨min n 2048, by omega⟩

/-- First grid index in bin `j`. -/
def binFirst (j : Fin 8) : ℕ := 256 * j.val

/-- Last grid index in bin `j` (inclusive). -/
def binLast (j : Fin 8) : ℕ := (binHi j).val

/-- Every row-bin restriction is single-peaked at the supplied exact grid
witness, including the first and last points of that bin. -/
def SectorBinUnimodal (w : Fin 9 → Fin 8 → Fin 2049) : Prop :=
  ∀ i j,
    binFirst j ≤ (w i j).val ∧ (w i j).val ≤ binLast j ∧
      (∀ n, binFirst j ≤ n → n < (w i j).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (w i j).val ≤ n → n < binLast j →
        sectorAt i (n + 1) ≤ sectorAt i n)

/-- The exact-bin maxima are bounded by the already emitted global sector
peaks.  These are 72 finite rational comparisons in the eventual table. -/
def SectorBinPeakValid (w : Fin 9 → Fin 8 → Fin 2049) : Prop :=
  ∀ i j, sectorAt i (w i j).val ≤ sectorPeakAt i

theorem sectorAt_le_witness_of_bin_steps (i : Fin 9) (j : Fin 8)
    {w n : ℕ} (hfirst : binFirst j ≤ n)
    (hinc : ∀ m, binFirst j ≤ m → m < w → sectorAt i m ≤ sectorAt i (m + 1))
    (hnlast : n ≤ binLast j)
    (hdec : ∀ m, w ≤ m → m < binLast j → sectorAt i (m + 1) ≤ sectorAt i m) :
    sectorAt i n ≤ sectorAt i w := by
  by_cases hle : n ≤ w
  · refine Nat.le_induction (m := n)
      (P := fun m => m ≤ w → sectorAt i n ≤ sectorAt i m)
      (fun _ => le_rfl) ?_ w hle hle
    intro m hnm ih hmw
    exact (ih (by omega)).trans (hinc m (by omega) (by omega))
  · have hwn : w ≤ n := le_of_lt (lt_of_not_ge hle)
    refine Nat.le_induction (m := w)
      (P := fun m => m ≤ binLast j → sectorAt i m ≤ sectorAt i w)
      le_rfl ?_ n hwn hnlast
    intro m hwm ih hmlast
    exact (hdec m hwm (by omega)).trans (ih (by omega))

theorem binFirst_le_val (k : Fin 2049) : binFirst (binIndex k) ≤ k.val := by
  unfold binFirst
  calc
    256 * (binIndex k).val ≤ 256 * (k.val / 256) := by
      apply Nat.mul_le_mul_left
      change min 7 (k.val / 256) ≤ k.val / 256
      exact Nat.min_le_right 7 (k.val / 256)
    _ ≤ k.val := Nat.mul_div_le k.val 256

theorem val_le_binLast (k : Fin 2049) : k.val ≤ binLast (binIndex k) := by
  unfold binLast
  by_cases h7 : (binIndex k).val = 7
  · have htop : binHi (binIndex k) = ⟨2048, by omega⟩ := by
      apply Fin.ext
      simp [binHi, h7]
    rw [htop]
    omega
  · have hnot : min 7 (k.val / 256) ≠ 7 := by
      simpa [binIndex] using h7
    have hmin : min 7 (k.val / 256) = k.val / 256 := by
      by_cases hle : k.val / 256 ≤ 7
      · exact min_eq_right hle
      · have hlt : 7 < k.val / 256 := by omega
        exact (hnot (min_eq_left hlt.le)).elim
    have hmod : k.val % 256 ≤ 255 := by
      have := Nat.mod_lt k.val (by norm_num : 0 < 256)
      omega
    have hbound : k.val ≤ 256 * (binIndex k).val + 255 := by
      calc
        k.val = 256 * (k.val / 256) + k.val % 256 :=
          (Nat.div_add_mod k.val 256).symm
        _ = 256 * (binIndex k).val + k.val % 256 := by
          rw [show (binIndex k).val = min 7 (k.val / 256) from rfl, hmin]
        _ ≤ 256 * (binIndex k).val + 255 := Nat.add_le_add_left hmod _
    have hbin : (binHi (binIndex k)).val =
        if (binIndex k).val = 7 then 2048 else 256 * (binIndex k).val + 255 := rfl
    rw [hbin, if_neg h7]
    exact hbound

/-- The 72 local bin peaks pay all `9 × 2049` sector grid checks without any
false global-monotonicity premise. -/
theorem sectorValid_of_bin_unimodal (w : Fin 9 → Fin 8 → Fin 2049)
    (hshape : SectorBinUnimodal w) (hpeak : SectorBinPeakValid w) : SectorValid := by
  intro i k
  let j := binIndex k
  obtain ⟨_hwfirst, hwlast, hinc, hdec⟩ := hshape i j
  have hlocal : sectorAt i k.val ≤ sectorAt i (w i j).val := by
    apply sectorAt_le_witness_of_bin_steps i j
      (binFirst_le_val k)
    · exact hinc
    · exact val_le_binLast k
    · exact hdec
  have hk : sectorAt i k.val = sectorValue i k := by
    simp [sectorAt, Nat.min_eq_left (show k.val ≤ 2048 by omega)]
  have hw : sectorAt i (w i j).val = sectorValue i (w i j) := by
    simp [sectorAt, Nat.min_eq_left (show (w i j).val ≤ 2048 by omega)]
  rw [hk] at hlocal
  rw [hw] at hlocal
  exact hlocal.trans (hpeak i j)

end N11Formalization.SevenClassQ0Deg3SectorBinShape
#check @N11Formalization.SevenClassQ0Deg3SectorBinShape.sectorValid_of_bin_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBinShape.sectorValid_of_bin_unimodal
