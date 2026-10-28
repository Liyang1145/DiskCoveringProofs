import N11Formalization.DSHPatchDispatcher

set_option autoImplicit false

/-! # DSH-PATCH-DISP negative-control failure log (expected exit != 0)

RED BY DESIGN.  Each claim below is provably FALSE in `DSHPatchDispatcherControl.lean`, so the
error is the intended mathematical failure, not an elaborator accident:

  FAIL-1  the two K5 cells are claimed to be in the 118-cell survey list.  FALSE:
          `DSHPatchDispatcherControl.k5_not_in_nidList` proves `4935 ∉ nidList` (cluster 5 is
          excluded because its dual-cap gate is pending; its cells come from the root-paid route).
  FAIL-2  cell 4974 is claimed to be in the list with cell 4974 deleted.  FALSE:
          `DSHPatchDispatcherControl.dropped_cell_not_member` proves the removal is effective.
  FAIL-3  the 118-cell list is claimed to have 119 entries.  FALSE:
          `DSHPatchDispatcherControl.nidList_length` proves 118.

Same proof scripts (`decide +kernel`) that close the TRUE versions in the control module, with only
the membership/count swapped.
-/
namespace N11Formalization.DSHPatchDispatcherFail

open N11Formalization

noncomputable section

/-- FAIL-1 (expected error: `decide` failed, proposition is false). -/
theorem bad_k5_membership : (4935 : Fin 5011) ∈ DSHPatchDispatcher.nidList := by
  decide +kernel

/-- FAIL-2 (expected error: `decide` failed, proposition is false). -/
theorem bad_dropped_membership : (4974 : Fin 5011) ∈
    DSHPatchDispatcherControl.nidListDrop := by
  decide +kernel

/-- FAIL-3 (expected error: `decide` failed, proposition is false). -/
theorem bad_length : DSHPatchDispatcher.nidList.length = 119 := by decide +kernel

end

end N11Formalization.DSHPatchDispatcherFail
