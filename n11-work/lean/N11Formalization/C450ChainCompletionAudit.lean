import N11Formalization.C450ChainCompletion

/-! Non-vacuity audit for the end of the C450 telescope.  The empty `drop 36`
tail is only the base case; `source36` itself is added by the 35-to-36 transfer
and must remain a member of the list consumed by `h450`. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionAudit
open N11Formalization

theorem source36_mem_h450_list :
    C450Source36Data.source36 ∈ C450Source11Segment.remainingSegs := by
  change C450Source36Data.source36 ∈ c450Segs.drop 11
  decide +kernel

theorem source36_paid_from_h450 :
    C450NormalizedInterface.SegmentNormalized C450Source36Data.source36 :=
  C450ChainCompletion.h450 C450Source36Data.source36 source36_mem_h450_list

theorem source36_mem_tail_not_empty :
    C450Source11Segment.remainingSegs ≠ [] := by
  intro hnil
  have hmem := source36_mem_h450_list
  rw [hnil] at hmem
  cases hmem

end N11Formalization.C450ChainCompletionAudit
#check @N11Formalization.C450ChainCompletionAudit.source36_mem_h450_list
#check @N11Formalization.C450ChainCompletionAudit.source36_paid_from_h450
#check @N11Formalization.C450ChainCompletionAudit.source36_mem_tail_not_empty
