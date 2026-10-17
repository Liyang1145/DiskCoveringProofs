import N11Formalization.ActualBinaryCycleRuns

set_option autoImplicit false
namespace N11Formalization.ProbeA14RunControls
def fourChanges : Fin 9 → Bool := ![true,false,true,false,false,false,false,false,false]

theorem four_changes_exact : ∀ i : Fin 9,
    fourChanges (i-1) ≠ fourChanges i ↔ i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by
  decide +kernel

theorem four_changes_not_two_runs :
    ¬ ∃ k m : Fin 9, m ≠ 0 ∧ ∀ i : Fin 9,
      fourChanges (i+k) = if i.val < m.val then fourChanges k else !fourChanges k := by
  decide +kernel
end N11Formalization.ProbeA14RunControls
#check @N11Formalization.ProbeA14RunControls.four_changes_not_two_runs
#print axioms N11Formalization.ProbeA14RunControls.four_changes_exact
#print axioms N11Formalization.ProbeA14RunControls.four_changes_not_two_runs
