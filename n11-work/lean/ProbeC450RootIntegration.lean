/-
PILOT root-integration probe (task-8, m6-c450-pilot).

PURPOSE. Importing ONLY `N11Formalization` (the root), verify that the root has
GENUINELY integrated C450Source13Segment -- i.e. that the declarations are visible
through the root's import closure and not merely present as an olean on LEAN_PATH.
This is the stale-olean control: `lake env lean` does NOT rebuild imports, so a
green probe against a stale root olean would be a false positive.

NEGATIVE CONTROL. Run this same file BEFORE the root import block is added: every
`#check` below must FAIL with `unknownIdentifier`. If it resolves without the
import, then `#check` is not testing the import closure and the positive run would
prove nothing.

WHAT THE CHAIN DOES. The two-step composition `h450_of_h13` shows the segment
modules compose through the root exactly as the chain design intends:
  C450Source13Segment.RemainingSourceObligation
    -> C450Source12Segment.RemainingSourceObligation   (source12_remaining_of_remaining)
    -> C450Source11Segment.RemainingSourceObligation   (source11_remaining_of_remaining)
The target of the second step IS the root's h450 (ActualMetricClassReduction.lean:65).

SCOPE / NON-CLAIM. `h13` is NOT vacuous and this probe does NOT discharge h450.
It reduces h450 to `h13`, which is a genuine obligation on 23 segments
(`remaining_count : remainingSegs.length = 23`). Vacuity arrives only at index 35.
-/
import N11Formalization

set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450RootIntegrationPilot

-- (1) Is the emitted segment visible THROUGH THE ROOT?
#check @C450Source13Segment.source13_paid
#check @C450Source13Segment.directions_cover
#check @C450Source13Segment.cells_paid

-- (2) Is the transitively pulled predecessor visible through the root too?
#check @C450Source12Segment.source12_paid
#check @C450Source12Segment.source11_remaining_of_remaining

-- (3) The root's h450, reached only through the root import closure.
#check @C450Source11Segment.RemainingSourceObligation

-- (4) THE INTERFACE: does the chain compose through the root?
theorem h450_of_h13 (hr : C450Source13Segment.RemainingSourceObligation) :
    C450Source11Segment.RemainingSourceObligation :=
  C450Source12Segment.source11_remaining_of_remaining
    (C450Source13Segment.source12_remaining_of_remaining hr)

-- (5) NON-VACUITY of what remains owed: h13 covers 23 segments, not none.
theorem h13_covers_23 : C450Source13Segment.remainingSegs.length = 23 :=
  C450Source13Segment.remaining_count

-- (6) The 12 already-paid segments sit BELOW the drop, so h13 excludes them.
theorem h13_excludes_paid : C450Source13Segment.remainingSegs
    = c450Segs.drop 13 := rfl

-- (7) KERNEL-CHECKED TERMINATION (converts C1837's regex count into a theorem).
-- c450Segs has exactly 36 entries, so the chain terminates vacuously at the last
-- index: the final module's RemainingSourceObligation quantifies over the EMPTY
-- list and is therefore trivially true. This is what makes the telescoping
-- discharge h450 once all 24 segments exist.
theorem c450Segs_length : c450Segs.length = 36 := by decide +kernel
theorem c450Segs_drop_36_empty : c450Segs.drop 36 = [] := by decide +kernel
theorem c450Segs_drop_35_singleton : (c450Segs.drop 35).length = 1 := by decide +kernel

-- (8) THE VACUOUS TERMINUS, as a theorem rather than a structural remark.
-- At the last index the obligation quantifies over the EMPTY list, so it holds
-- for free. This is the base case of the telescope that would discharge h450.
theorem vacuous_obligation_at_36 :
    ∀ s ∈ (c450Segs.drop 36 : List TenSeg),
      C450NormalizedInterface.SegmentNormalized s := by
  rw [c450Segs_drop_36_empty]
  intro s hs
  simp at hs

-- (9) NON-VACUITY OF THE CURRENT STEP. h13 is NOT free: it genuinely owes the
-- 23 remaining segments. Without this, step (7)-(8) could be misread as the
-- pilot having discharged h450. It has not; it has REDUCED it by one segment.
theorem h13_owes_23_not_0 : C450Source13Segment.remainingSegs.length ≠ 0 := by
  rw [C450Source13Segment.remaining_count]
  decide

/-! ## (10) THE TERMINAL STEP — what the LAST module must actually prove

The question: does the last segment (index 35) still need a `*_paid` proof, or is
its step free because its own RemainingSourceObligation is vacuous?

The chain at index k supplies
  `*_remaining_of_remaining (hr : <k>.obl) : <k-1>.obl`
where `<k-1>.remainingSegs = <k> :: <k>.remainingSegs`. So the proof case-splits:
the HEAD element is paid by `<k>_paid`, the TAIL by `hr`.

At the last index (k = 35) we have `<35>.remainingSegs = c450Segs.drop 36 = []`,
so `<35>.obl` IS vacuous (step 8) and the `hr` hypothesis is free. BUT the head of
`<34>.remainingSegs = c450Segs.drop 35` is a genuine singleton, so the head case
still demands `<35>_paid`. The two facts are independent:

  * the TERMINUS (the `hr` at the bottom) is free  -> no infinite regress
  * the LAST ELEMENT (index 35) still needs paid   -> one more emitted segment

Step (10a) proves the terminus is free; (10b) proves the last element's obligation
is NOT vacuous (it reduces to exactly one paid obligation); (10c) counts the
non-vacuous obligations, which is the number of segments still to emit.
-/

-- (10a) The terminus is free: the obligation over the empty tail holds for free.
theorem terminus_is_free :
    ∀ s ∈ (c450Segs.drop 36 : List TenSeg),
      C450NormalizedInterface.SegmentNormalized s :=
  vacuous_obligation_at_36

-- (10b) But the LAST element's obligation is NOT vacuous. `drop 35` is a
-- singleton, and an obligation over a singleton reduces to one paid obligation.
-- Hence the last module must still supply `<35>_paid`.
theorem terminal_predecessor_needs_one_paid :
    ∃ a : TenSeg, c450Segs.drop 35 = [a] ∧
      ((∀ s ∈ (c450Segs.drop 35 : List TenSeg),
          C450NormalizedInterface.SegmentNormalized s)
        ↔ C450NormalizedInterface.SegmentNormalized a) := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp c450Segs_drop_35_singleton
  refine ⟨a, ha, ?_⟩
  rw [ha]
  constructor
  · intro h
    exact h a (by simp)
  · intro h
    intro s hs
    simp only [List.mem_singleton] at hs
    rwa [hs]

-- (10c) The count of NON-VACUOUS segment obligations from index 13 is 23, and the
-- ONLY vacuous one in the whole chain is the tail at 36. So the batch is 23
-- segments, each needing a paid proof — NOT 22 plus a free terminal.
theorem obligations_from_13_nonvacuous :
    (c450Segs.drop 13).length = 23 ∧ (c450Segs.drop 13).length ≠ 0 := by
  have h : (c450Segs.drop 13).length = 23 := C450Source13Segment.remaining_count
  exact ⟨h, by rw [h]; decide⟩

end N11Formalization.C450RootIntegrationPilot

#print axioms N11Formalization.C450RootIntegrationPilot.h450_of_h13
#print axioms N11Formalization.C450RootIntegrationPilot.h13_covers_23
#print axioms N11Formalization.C450RootIntegrationPilot.c450Segs_length
#print axioms N11Formalization.C450RootIntegrationPilot.c450Segs_drop_36_empty
#print axioms N11Formalization.C450RootIntegrationPilot.vacuous_obligation_at_36
#print axioms N11Formalization.C450RootIntegrationPilot.h13_owes_23_not_0
#print axioms N11Formalization.C450RootIntegrationPilot.terminus_is_free
#print axioms N11Formalization.C450RootIntegrationPilot.terminal_predecessor_needs_one_paid
#print axioms N11Formalization.C450RootIntegrationPilot.obligations_from_13_nonvacuous
