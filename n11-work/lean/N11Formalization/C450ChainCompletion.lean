import N11Formalization.C450Source36Segment
import N11Formalization.C450NormalizedInterface

/-! Kernel-checked completion of the C450 source telescope.

`C450Source36Segment.remainingSegs` is `c450Segs.drop 36`, hence empty.  Applying
the 25 emitted predecessor-transfer lemmas from Source12 through Source36 turns
that vacuous tail into `C450Source11Segment.RemainingSourceObligation`, the
root's `h450`, without a new hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletion

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

theorem h450 : C450Source11Segment.RemainingSourceObligation :=
  C450Source12Segment.source11_remaining_of_remaining (
    C450Source13Segment.source12_remaining_of_remaining (
      C450Source14Segment.source13_remaining_of_remaining (
        C450Source15Segment.source14_remaining_of_remaining (
          C450Source16Segment.source15_remaining_of_remaining (
            C450Source17Segment.source16_remaining_of_remaining (
              C450Source18Segment.source17_remaining_of_remaining (
                C450Source19Segment.source18_remaining_of_remaining (
                  C450Source20Segment.source19_remaining_of_remaining (
                    C450Source21Segment.source20_remaining_of_remaining (
                      C450Source22Segment.source21_remaining_of_remaining (
                        C450Source23Segment.source22_remaining_of_remaining (
                          C450Source24Segment.source23_remaining_of_remaining (
                            C450Source25Segment.source24_remaining_of_remaining (
                              C450Source26Segment.source25_remaining_of_remaining (
                                C450Source27Segment.source26_remaining_of_remaining (
                                  C450Source28Segment.source27_remaining_of_remaining (
                                    C450Source29Segment.source28_remaining_of_remaining (
                                      C450Source30Segment.source29_remaining_of_remaining (
                                        C450Source31Segment.source30_remaining_of_remaining (
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
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
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

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] := by
  cases h : C450Source36Segment.remainingSegs with
  | nil => rfl
  | cons a as =>
      have hlen := C450Source36Segment.remaining_count
      rw [h] at hlen
      exfalso
      exact absurd hlen (by simp)

theorem chain_step_count : (36 - 12) + 1 = 25 := rfl

end N11Formalization.C450ChainCompletion
#check @N11Formalization.C450ChainCompletion.source36_remaining
#check @N11Formalization.C450ChainCompletion.h450
#check @N11Formalization.C450ChainCompletion.source_obligation
#check @N11Formalization.C450ChainCompletion.c450_atom
#check @N11Formalization.C450ChainCompletion.card_boundaryIdx_eq_nine
#check @N11Formalization.C450ChainCompletion.exists_covers_ringLabels
#print axioms N11Formalization.C450ChainCompletion.h450
#print axioms N11Formalization.C450ChainCompletion.source_obligation
#print axioms N11Formalization.C450ChainCompletion.c450_atom
