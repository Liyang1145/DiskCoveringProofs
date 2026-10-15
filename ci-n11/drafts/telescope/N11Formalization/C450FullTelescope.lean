import N11Formalization.C450Source36Segment
import N11Formalization.ActualMainRoute

/-! DRAFT (dcp-n11-lean agent, 2026-10-15), NOT COMPILED: no Mathlib build was possible in this
sandbox. Telescope from the empty `drop 36` tail of the emitted C450Source36Segment back to
`C450Source11Segment.RemainingSourceObligation` (= the `h450` input of
`ActualMainRoute.main_of_remaining`). It pays nothing by itself: every step consumes the
segment's own `sourceK_paid` inside `source{K-1}_remaining_of_remaining`. It only becomes a
credit after Source12..36 Segment modules build green in a fresh serial root build and pass
the axiom audit (propext, Classical.choice, Quot.sound only). -/
set_option autoImplicit false
namespace N11Formalization.C450FullTelescope

theorem tail36 : C450Source36Segment.RemainingSourceObligation := by
  intro s hs
  have h0 : C450Source36Segment.remainingSegs = [] :=
    List.eq_nil_of_length_eq_zero C450Source36Segment.remaining_count
  rw [h0] at hs
  exact absurd hs (List.not_mem_nil)

theorem tail35 : C450Source35Segment.RemainingSourceObligation :=
  C450Source36Segment.source35_remaining_of_remaining tail36
theorem tail34 : C450Source34Segment.RemainingSourceObligation :=
  C450Source35Segment.source34_remaining_of_remaining tail35
theorem tail33 : C450Source33Segment.RemainingSourceObligation :=
  C450Source34Segment.source33_remaining_of_remaining tail34
theorem tail32 : C450Source32Segment.RemainingSourceObligation :=
  C450Source33Segment.source32_remaining_of_remaining tail33
theorem tail31 : C450Source31Segment.RemainingSourceObligation :=
  C450Source32Segment.source31_remaining_of_remaining tail32
theorem tail30 : C450Source30Segment.RemainingSourceObligation :=
  C450Source31Segment.source30_remaining_of_remaining tail31
theorem tail29 : C450Source29Segment.RemainingSourceObligation :=
  C450Source30Segment.source29_remaining_of_remaining tail30
theorem tail28 : C450Source28Segment.RemainingSourceObligation :=
  C450Source29Segment.source28_remaining_of_remaining tail29
theorem tail27 : C450Source27Segment.RemainingSourceObligation :=
  C450Source28Segment.source27_remaining_of_remaining tail28
theorem tail26 : C450Source26Segment.RemainingSourceObligation :=
  C450Source27Segment.source26_remaining_of_remaining tail27
theorem tail25 : C450Source25Segment.RemainingSourceObligation :=
  C450Source26Segment.source25_remaining_of_remaining tail26
theorem tail24 : C450Source24Segment.RemainingSourceObligation :=
  C450Source25Segment.source24_remaining_of_remaining tail25
theorem tail23 : C450Source23Segment.RemainingSourceObligation :=
  C450Source24Segment.source23_remaining_of_remaining tail24
theorem tail22 : C450Source22Segment.RemainingSourceObligation :=
  C450Source23Segment.source22_remaining_of_remaining tail23
theorem tail21 : C450Source21Segment.RemainingSourceObligation :=
  C450Source22Segment.source21_remaining_of_remaining tail22
theorem tail20 : C450Source20Segment.RemainingSourceObligation :=
  C450Source21Segment.source20_remaining_of_remaining tail21
theorem tail19 : C450Source19Segment.RemainingSourceObligation :=
  C450Source20Segment.source19_remaining_of_remaining tail20
theorem tail18 : C450Source18Segment.RemainingSourceObligation :=
  C450Source19Segment.source18_remaining_of_remaining tail19
theorem tail17 : C450Source17Segment.RemainingSourceObligation :=
  C450Source18Segment.source17_remaining_of_remaining tail18
theorem tail16 : C450Source16Segment.RemainingSourceObligation :=
  C450Source17Segment.source16_remaining_of_remaining tail17
theorem tail15 : C450Source15Segment.RemainingSourceObligation :=
  C450Source16Segment.source15_remaining_of_remaining tail16
theorem tail14 : C450Source14Segment.RemainingSourceObligation :=
  C450Source15Segment.source14_remaining_of_remaining tail15
theorem tail13 : C450Source13Segment.RemainingSourceObligation :=
  C450Source14Segment.source13_remaining_of_remaining tail14
theorem tail12 : C450Source12Segment.RemainingSourceObligation :=
  C450Source13Segment.source12_remaining_of_remaining tail13

/-- The `h450` input of `ActualMainRoute.main_of_remaining`. -/
theorem h450 : C450Source11Segment.RemainingSourceObligation :=
  C450Source12Segment.source11_remaining_of_remaining tail12

/-- Main route with C450 discharged; still conditional on energy and canonical33. -/
theorem main_of_energy_and_33
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (h33 : ActualMainRoute.Canonical33Obligation) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMainRoute.main_of_remaining h450 henergy h33

end N11Formalization.C450FullTelescope
#print axioms N11Formalization.C450FullTelescope.h450
#print axioms N11Formalization.C450FullTelescope.main_of_energy_and_33
