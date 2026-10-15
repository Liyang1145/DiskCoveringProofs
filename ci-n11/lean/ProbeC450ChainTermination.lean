/-
  ProbeC450ChainTermination.lean   (owner: lead)

  ============================ CREDIT SCOPE ============================
  Validates the TERMINATION arithmetic behind C1837: that the C450 chain can be
  discharged vacuously, so completing segments 12..35 would eliminate h450 — one
  of the two explicit hypotheses of the frozen unconditional theorem.

  This probe proves only the ARITHMETIC and the VACUITY. It does NOT emit any
  segment, does NOT discharge h450, and pays no class credit.

  Axioms: propext, Classical.choice, Quot.sound only.
-/
import N11Formalization.C450Source13Segment

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeC450ChainTermination

open N11Formalization

/-- `c450Segs` really has 36 entries, so dropping 36 leaves the empty list. -/
theorem aud_c450Segs_length : c450Segs.length = 36 := by decide +kernel

/-- Dropping all 36 entries leaves nothing. -/
theorem aud_drop36 : c450Segs.drop 36 = [] := by
  apply List.drop_eq_nil_of_le
  rw [aud_c450Segs_length]

/-- **The termination fact.**  The obligation at the last index is VACUOUS:
any `RemainingSourceObligation` indexed by `c450Segs.drop 36` holds trivially,
with no segment proof required. -/
theorem aud_vacuous_obligation :
    ∀ s ∈ c450Segs.drop 36, C450NormalizedInterface.SegmentNormalized s := by
  rw [aud_drop36]
  intro s hs
  simp at hs

/-- The same, phrased as the shape a final module would need: the empty-index
obligation is inhabited unconditionally. -/
theorem aud_vacuous_holds : (∀ s ∈ ([] : List TenSeg),
    C450NormalizedInterface.SegmentNormalized s) := by
  intro s hs
  simp at hs

/-- Sanity: the chain's `drop` indices are exactly 11, 12, 13 for the three
modules we have, and each leaves the expected count. -/
theorem aud_chain_counts :
    (c450Segs.drop 11).length = 25 ∧ (c450Segs.drop 12).length = 24 ∧
      (c450Segs.drop 13).length = 23 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end N11Formalization.ProbeC450ChainTermination

#print axioms N11Formalization.ProbeC450ChainTermination.aud_c450Segs_length
#print axioms N11Formalization.ProbeC450ChainTermination.aud_drop36
#print axioms N11Formalization.ProbeC450ChainTermination.aud_vacuous_obligation
#print axioms N11Formalization.ProbeC450ChainTermination.aud_vacuous_holds
#print axioms N11Formalization.ProbeC450ChainTermination.aud_chain_counts
