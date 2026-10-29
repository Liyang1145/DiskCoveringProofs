import N11Formalization.C450ChainCompletionMid3
import N11Formalization.C450NormalizedInterface

/-! Final C450 transfers 16 through 12 and the public h450 consumer interface. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletion
open N11Formalization C450NormalizedInterface

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation :=
  C450ChainCompletionTail.source36_remaining

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] :=
  C450ChainCompletionTail.source36_remaining_vacuous

theorem h450 : C450Source11Segment.RemainingSourceObligation :=
  C450Source12Segment.source11_remaining_of_remaining (
    C450Source13Segment.source12_remaining_of_remaining (
      C450Source14Segment.source13_remaining_of_remaining (
        C450Source15Segment.source14_remaining_of_remaining (
          C450Source16Segment.source15_remaining_of_remaining (
            C450ChainCompletionMid3.source16_remaining
          )
        )
      )
    )
  )

theorem source_obligation : SourceObligation :=
  C450Source11Segment.source_of_remaining h450

theorem c450_atom : C450Atom :=
  C450Source11Segment.atom_of_remaining h450

theorem card_boundaryIdx_eq_nine {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 :=
  C450NormalizedInterface.nine_of_source source_obligation hr hc

theorem exists_covers_ringLabels {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11), Covers (fun j => c (p j)) r ∧
      DSHTopologyInterior.RingLabels (fun j => c (p j)) r :=
  C450NormalizedInterface.ringLabels_of_source source_obligation hr hc

theorem chain_step_count : (36 - 12) + 1 = 25 := rfl

end N11Formalization.C450ChainCompletion
#check @N11Formalization.C450ChainCompletion.h450
#check @N11Formalization.C450ChainCompletion.source_obligation
#check @N11Formalization.C450ChainCompletion.c450_atom
#check @N11Formalization.C450ChainCompletion.card_boundaryIdx_eq_nine
#check @N11Formalization.C450ChainCompletion.exists_covers_ringLabels
