import N11Formalization.C450ChainCompletionMid1

/-! C450 telescope transfers 26 through 22. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionMid2
open N11Formalization

theorem source21_remaining : C450Source21Segment.RemainingSourceObligation :=
  C450Source22Segment.source21_remaining_of_remaining (
    C450Source23Segment.source22_remaining_of_remaining (
      C450Source24Segment.source23_remaining_of_remaining (
        C450Source25Segment.source24_remaining_of_remaining (
          C450Source26Segment.source25_remaining_of_remaining (
            C450ChainCompletionMid1.source26_remaining
          )
        )
      )
    )
  )

end N11Formalization.C450ChainCompletionMid2
#check @N11Formalization.C450ChainCompletionMid2.source21_remaining
