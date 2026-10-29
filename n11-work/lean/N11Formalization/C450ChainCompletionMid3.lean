import N11Formalization.C450ChainCompletionMid2

/-! C450 telescope transfers 21 through 17. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionMid3
open N11Formalization

theorem source16_remaining : C450Source16Segment.RemainingSourceObligation :=
  C450Source17Segment.source16_remaining_of_remaining (
    C450Source18Segment.source17_remaining_of_remaining (
      C450Source19Segment.source18_remaining_of_remaining (
        C450Source20Segment.source19_remaining_of_remaining (
          C450Source21Segment.source20_remaining_of_remaining (
            C450ChainCompletionMid2.source21_remaining
          )
        )
      )
    )
  )

end N11Formalization.C450ChainCompletionMid3
#check @N11Formalization.C450ChainCompletionMid3.source16_remaining
