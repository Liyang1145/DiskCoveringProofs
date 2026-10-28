/-
  DSHTopologyOwnershipC450Source.lean — DSH-TOPO-C2 (part F): re-sourcing the C2 ownership
  results from the bare `card = 9` placeholder to the REAL residual obligation of the
  ten-boundary line.

  ## Why this file exists

  My conditional results (C1706 `ownership_ledger_actual`, `capPreimage_volumeReal_pos`,
  `not_exists_coincident_of_card_nine`, `unique_ownership_actual`) take the explicit typed
  premise

      Fintype.card (BoundaryIdx c r) = 9

  The ten-boundary line (teammate `topo-ten-bdy`, C1701/C1702/C1709) reduces that premise to a
  single named obligation:

      C450PerDiskObligation := ∀ s ∈ c450Segs, s.PerDisk      (DSHTenBoundaryData.lean:189)

  (36 explicit per-segment per-disk continuum inequalities on rational data), and proves

      card_boundaryIdx_eq_nine_of_obligation_lt_sourceRadius :
        C450PerDiskObligation → r < SourceExactRoot.sourceRadius → Covers c r →
          Fintype.card (BoundaryIdx c r) = 9     (DSHTenBoundaryData.lean:212)

  This module is a pure CONSUMER of that accepted shape (no private content, no redefinition):
  it composes the two lines so that C2's output is conditional only on `C450PerDiskObligation`
  at the FROZEN source-root interval, i.e. on the actual open mathematics of C1 rather than on a
  cardinality placeholder.

  Scope: module/standalone; consumes `DSHTenBoundaryData` and `DSHTopologyOwnershipLedger`.
  Nothing here is unconditional on `C450PerDiskObligation`; the obligation itself is NOT
  discharged. No `sorry`, no custom axiom, no `native_decide`.
-/
import Mathlib
import N11Formalization.DSHTopologyOwnershipLedger
import N11Formalization.DSHTenBoundaryData

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization.DSHTopologyOwnershipC450Source

open MeasureTheory
open N11Formalization
open N11Formalization.DSHTopologyOwnership
open N11Formalization.DSHTopologyOwnershipLedger

noncomputable section

/-! ## §16  The two bridges from the C450 residual -/

/-- The paid source radius lies strictly below `19/50` (kernel-proved enclosure + margin). -/
theorem sourceRadius_lt_R0 : SourceExactRoot.sourceRadius < (19 : ℝ) / 50 :=
  lt_of_le_of_lt SourceExactRoot.sourceRadius_mem_box.2 boxHiCert_six_lt_R0_real

/-- The source-root radius is also below the unit-radius hypothesis required by the ledger. -/
theorem sourceRadius_le_one : SourceExactRoot.sourceRadius ≤ (1 : ℝ) :=
  le_trans sourceRadius_lt_R0.le (by norm_num)

/-- `8 arcsin r < π` at the frozen source-root interval. -/
theorem eight_arcsin_lt_pi_of_lt_sourceRadius {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) : 8 * Real.arcsin r < Real.pi :=
  N11Formalization.DSHTopologyOwnershipLedger.eight_arcsin_lt_pi_of_lt_R0
    (lt_of_lt_of_le hr sourceRadius_lt_R0.le)

/-- Nine boundary disks at the frozen source-root interval, from the C450 residual obligation. -/
theorem card_nine_of_c450 (h : C450PerDiskObligation) {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hcov : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 :=
  card_boundaryIdx_eq_nine_of_obligation_lt_sourceRadius h hr hcov

/-! ## §17  C2's conditional output, re-sourced to `C450PerDiskObligation` -/

/-- **Ownership ledger over the real cover, conditional on the C450 residual only.** -/
theorem ownership_ledger_of_c450 (h : C450PerDiskObligation) {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hcov : Covers c r) (i : BoundaryIdx c r) :
    0 < volume.real (ownerSetB c r i) ∧ volume.real (ownerSetB c r i) ≤ 2 * Real.arcsin r :=
  ownership_ledger_actual (Covers.nonneg hcov) (lt_of_lt_of_le hr sourceRadius_le_one)
    (eight_arcsin_lt_pi_of_lt_sourceRadius hr) hcov (card_nine_of_c450 h hr hcov) i

/-- Every actual boundary arc has positive angular length, from the C450 residual. -/
theorem capPreimage_volumeReal_pos_of_c450 (h : C450PerDiskObligation) {c : Fin 11 → Point}
    {r : ℝ} (hr : r < SourceExactRoot.sourceRadius) (hcov : Covers c r)
    (i : BoundaryIdx c r) : 0 < volume.real (capPreimage (c i.1) r) :=
  capPreimage_volumeReal_pos (Covers.nonneg hcov) (lt_of_lt_of_le hr sourceRadius_le_one)
    (eight_arcsin_lt_pi_of_lt_sourceRadius hr) hcov (card_nine_of_c450 h hr hcov) i

/-- The nine boundary disks have pairwise distinct centres, from the C450 residual
(the degenerate coincident-centre branch is excluded). -/
theorem centres_distinct_of_c450 (h : C450PerDiskObligation) {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hcov : Covers c r) :
    ¬ ∃ i j : BoundaryIdx c r, i ≠ j ∧ c i.1 = c j.1 :=
  not_exists_coincident_of_card_nine (Covers.nonneg hcov)
    (lt_of_lt_of_le hr sourceRadius_le_one) (eight_arcsin_lt_pi_of_lt_sourceRadius hr) hcov
    (card_nine_of_c450 h hr hcov)

/-- **DSH-TOPO-C2 headline, re-sourced to the C450 residual.**  For an actual eleven-disk cover
below the FROZEN source radius, conditional ONLY on the ten-boundary line's named obligation:

  1. every point of `S¹` has exactly one owning boundary disk, within `r` of it;
  2. every boundary disk owns a positive angular measure `≤ 2 arcsin r`;
  3. every actual boundary arc has positive angular length;
  4. the owned measures sum to `2π`;
  5. every angle has exactly one owning boundary disk.

The only premise beyond `Covers c r` is `C450PerDiskObligation` (the 36 per-segment per-disk
inequalities) — the cardinality placeholder `card (BoundaryIdx c r) = 9` is gone from the
statement.  `C450PerDiskObligation` itself is NOT proved here. -/
theorem unique_ownership_actual_of_c450 (h : C450PerDiskObligation) {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hcov : Covers c r) :
    (∀ x : Point, ‖x‖ = 1 →
        ∃! i : Fin 11, MeetsCircle c r i ∧ OwnsPt c i x ∧ dist x (c i) ≤ r) ∧
    (∀ i : BoundaryIdx c r, 0 < volume.real (ownerSetB c r i) ∧
        volume.real (ownerSetB c r i) ≤ 2 * Real.arcsin r) ∧
    (∀ i : BoundaryIdx c r, 0 < volume.real (capPreimage (c i.1) r)) ∧
    (∑ i : BoundaryIdx c r, volume.real (ownerSetB c r i) = 2 * Real.pi) ∧
    (∀ t : ℝ, t ∈ Set.Ioo 0 (2 * Real.pi) → ∃! i : BoundaryIdx c r, OwnsB c r i t) :=
  unique_ownership_actual (Covers.nonneg hcov) (lt_of_lt_of_le hr sourceRadius_lt_R0.le) hcov
    (card_nine_of_c450 h hr hcov)

/-! ## §18  Verbatim types and trusted base (evidence pack) -/

#check @N11Formalization.DSHTopologyOwnershipC450Source.sourceRadius_lt_R0
#check @N11Formalization.DSHTopologyOwnershipC450Source.eight_arcsin_lt_pi_of_lt_sourceRadius
#check @N11Formalization.DSHTopologyOwnershipC450Source.card_nine_of_c450
#check @N11Formalization.DSHTopologyOwnershipC450Source.ownership_ledger_of_c450
#check @N11Formalization.DSHTopologyOwnershipC450Source.capPreimage_volumeReal_pos_of_c450
#check @N11Formalization.DSHTopologyOwnershipC450Source.centres_distinct_of_c450
#check @N11Formalization.DSHTopologyOwnershipC450Source.unique_ownership_actual_of_c450

#print axioms N11Formalization.DSHTopologyOwnershipC450Source.sourceRadius_lt_R0
#print axioms N11Formalization.DSHTopologyOwnershipC450Source.eight_arcsin_lt_pi_of_lt_sourceRadius
#print axioms N11Formalization.DSHTopologyOwnershipC450Source.card_nine_of_c450
#print axioms N11Formalization.DSHTopologyOwnershipC450Source.ownership_ledger_of_c450
#print axioms N11Formalization.DSHTopologyOwnershipC450Source.capPreimage_volumeReal_pos_of_c450
#print axioms N11Formalization.DSHTopologyOwnershipC450Source.centres_distinct_of_c450
#print axioms N11Formalization.DSHTopologyOwnershipC450Source.unique_ownership_actual_of_c450

end

end N11Formalization.DSHTopologyOwnershipC450Source
