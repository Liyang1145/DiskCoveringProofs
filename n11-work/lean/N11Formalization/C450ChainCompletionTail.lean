import N11Formalization.C450ChainCompletionEndpoint

/-! The first five C450 telescope transfers (36 through 32). -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionTail
open N11Formalization

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] :=
  C450ChainCompletionEndpoint.source36_remaining_vacuous

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation :=
  C450ChainCompletionEndpoint.source36_remaining

theorem source31_remaining : C450Source31Segment.RemainingSourceObligation :=
  C450Source32Segment.source31_remaining_of_remaining (
    C450Source33Segment.source32_remaining_of_remaining (
      C450Source34Segment.source33_remaining_of_remaining (
        C450Source35Segment.source34_remaining_of_remaining (
          C450Source36Segment.source35_remaining_of_remaining (
            source36_remaining
          )
        )
      )
    )
  )

end N11Formalization.C450ChainCompletionTail
#check @N11Formalization.C450ChainCompletionTail.source36_remaining
#check @N11Formalization.C450ChainCompletionTail.source31_remaining
