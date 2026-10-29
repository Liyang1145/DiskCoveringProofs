import N11Formalization.C450Source36Segment

/-! The vacuous C450 source-36 endpoint, isolated from all telescope transfers. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionEndpoint
open N11Formalization

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] :=
  List.eq_nil_of_length_eq_zero C450Source36Segment.remaining_count

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation := by
  intro s hs
  rw [source36_remaining_vacuous] at hs
  cases hs

end N11Formalization.C450ChainCompletionEndpoint
#check @N11Formalization.C450ChainCompletionEndpoint.source36_remaining
