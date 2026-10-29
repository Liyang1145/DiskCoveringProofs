import N11Formalization.C450Source36Segment
import N11Formalization.C450NormalizedInterface

/-! Vacuous C450 source-36 tail and the first five telescope transfers (36 through 32). -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionTail
open N11Formalization C450NormalizedInterface

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation := by
  intro s hs
  have hlen : C450Source36Segment.remainingSegs.length = 0 :=
    C450Source36Segment.remaining_count
  cases h : C450Source36Segment.remainingSegs with
  | nil =>
      rw [h] at hs
      simp at hs
  | cons a as =>
      rw [h] at hlen
      exfalso
      exact absurd hlen (by simp)

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

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] := by
  cases h : C450Source36Segment.remainingSegs with
  | nil => rfl
  | cons a as =>
      have hlen := C450Source36Segment.remaining_count
      rw [h] at hlen
      exfalso
      exact absurd hlen (by simp)

end N11Formalization.C450ChainCompletionTail
#check @N11Formalization.C450ChainCompletionTail.source36_remaining
#check @N11Formalization.C450ChainCompletionTail.source31_remaining
