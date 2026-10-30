import N11Formalization.EnergyTerminalResidualCensus

/-! The seven public frozen-cap exclusion IDs are members of the exact B13
residual census.  This links the exclusion payloads to the outstanding energy
set without claiming any packet payment. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapResidualMembership
open Finset
noncomputable section

private theorem mem_of_chunk0 {n : Fin 5011} (hn : n ∈ EnergyTerminalResidualCensus.chunk0) :
    n ∈ EnergyTerminalBatchB13.residualIDs := by
  rw [← EnergyTerminalResidualCensus.residualIDs_eq]
  exact Finset.mem_union_left _ hn

theorem mem_1409 : (1409 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs :=
  mem_of_chunk0 (by decide +kernel)

theorem mem_2337 : (2337 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs :=
  mem_of_chunk0 (by decide +kernel)

theorem mem_2341 : (2341 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs :=
  mem_of_chunk0 (by decide +kernel)

theorem mem_2356 : (2356 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs :=
  mem_of_chunk0 (by decide +kernel)

theorem mem_2360 : (2360 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs :=
  mem_of_chunk0 (by decide +kernel)

theorem mem_2368 : (2368 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs :=
  mem_of_chunk0 (by decide +kernel)

theorem mem_2370 : (2370 : Fin 5011) ∈ EnergyTerminalBatchB13.residualIDs :=
  mem_of_chunk0 (by decide +kernel)

theorem public_seven_subset :
    ({1409, 2337, 2341, 2356, 2360, 2368, 2370} : Finset (Fin 5011)) ⊆
      EnergyTerminalBatchB13.residualIDs := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_1409
  · exact mem_2337
  · exact mem_2341
  · exact mem_2356
  · exact mem_2360
  · exact mem_2368
  · exact mem_2370

theorem not_paid_1409 : (1409 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs :=
  ((EnergyTerminalBatchB13.mem_residualIDs_iff _).mp mem_1409).2.2

theorem not_paid_2337 : (2337 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs :=
  ((EnergyTerminalBatchB13.mem_residualIDs_iff _).mp mem_2337).2.2

theorem not_paid_2341 : (2341 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs :=
  ((EnergyTerminalBatchB13.mem_residualIDs_iff _).mp mem_2341).2.2

theorem not_paid_2356 : (2356 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs :=
  ((EnergyTerminalBatchB13.mem_residualIDs_iff _).mp mem_2356).2.2

theorem not_paid_2360 : (2360 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs :=
  ((EnergyTerminalBatchB13.mem_residualIDs_iff _).mp mem_2360).2.2

theorem not_paid_2368 : (2368 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs :=
  ((EnergyTerminalBatchB13.mem_residualIDs_iff _).mp mem_2368).2.2

theorem not_paid_2370 : (2370 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs :=
  ((EnergyTerminalBatchB13.mem_residualIDs_iff _).mp mem_2370).2.2

end
end N11Formalization.FrozenCapResidualMembership

#check @N11Formalization.FrozenCapResidualMembership.public_seven_subset
#check @N11Formalization.FrozenCapResidualMembership.not_paid_1409
#print axioms N11Formalization.FrozenCapResidualMembership.public_seven_subset
#print axioms N11Formalization.FrozenCapResidualMembership.not_paid_1409
