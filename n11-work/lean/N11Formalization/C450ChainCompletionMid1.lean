import N11Formalization.C450ChainCompletionTail

/-! C450 telescope transfers 31 through 27. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionMid1
open N11Formalization

theorem source26_remaining : C450Source26Segment.RemainingSourceObligation :=
  C450Source27Segment.source26_remaining_of_remaining (
    C450Source28Segment.source27_remaining_of_remaining (
      C450Source29Segment.source28_remaining_of_remaining (
        C450Source30Segment.source29_remaining_of_remaining (
          C450Source31Segment.source30_remaining_of_remaining (
            C450ChainCompletionTail.source31_remaining
          )
        )
      )
    )
  )

end N11Formalization.C450ChainCompletionMid1
#check @N11Formalization.C450ChainCompletionMid1.source26_remaining
