import N11Formalization
set_option autoImplicit false
open N11Formalization SourceNEnclosure SourceNormalizedKernel

#print SourceNEnclosure.centre
#print SourceNEnclosure.actualResidual
#print SourceNEnclosure.dependentBox
#print SourceNormalizedKernel.dependentColumn
#check @SourceNColumnProposal.free_binding
#check @SourceNColumnProposal.all_errors
#check @SourceNEnclosure.actualResidual_identity
#check @SourceNEnclosure.actualResidual_norm
#check @SourceNEnclosure.dependentColumn_error
#check @SourceNEnclosure.dependentBox_mem
#check @SourceNEnclosure.NBox_mem
#check @SourceNEnclosure.canonicalNBox_mem
#print axioms SourceNEnclosure.actualResidual_identity
#print axioms SourceNEnclosure.actualResidual_norm
#print axioms SourceNEnclosure.dependentColumn_error
#print axioms SourceNEnclosure.NBox_mem
#print axioms SourceNEnclosure.canonicalNBox_mem

-- Actual exact inverse solution, not equality to the proposed rational centre.
example (a : Fin 4) (i : Fin 41) :
    (dependentBox i a).Mem (SourceNormalizedKernel.N (SourceB41Proposal.dep i) a) := by
  rw [SourceNormalizedKernel.N_dep]
  exact dependentBox_mem i a

example (e : Fin 45) (a : Fin 4) :
    (NBox e a).Mem (SourceNormalizedKernel.N e a) := NBox_mem e a

example (e : ResumeNetwork.Edge) (a : Fin 4) :
    (canonicalNBox e a).Mem (SourceNormalizedCanonical.Ncanon e a) :=
  canonicalNBox_mem e a

-- Direct real readout consumer, retaining EVERY dependent slot and column.
example (i : Fin 41) (a : Fin 4) :
    dependentColumn a i ≤ (SourceNColumnProposal.YN i a : ℝ)/100000000+1/245 := by
  have h := (dependentBox_mem i a).2
  simpa only [dependentBox,RatInterval.intv,Rat.cast_add,Rat.cast_div,
    Rat.cast_intCast,Rat.cast_one,Rat.cast_ofNat] using h

example (a : Fin 4) :
    ∑ e : Fin 45, SourceNormalizedKernel.N e a = 0 :=
  SourceNormalizedKernel.column_sum_zero a

-- Free slots remain exact; proposal centre/error never changes them.
example : SourceNormalizedKernel.N (SourceB41Proposal.freeCol 0) 0 = 1 := by
  rw [SourceNormalizedKernel.N_free]
  simp
example : SourceNormalizedKernel.N (SourceB41Proposal.freeCol 0) 1 = 0 := by
  rw [SourceNormalizedKernel.N_free]
  norm_num

-- Negative control: a certified small error does not prove centre equality.
example : |(1 : ℝ)/490-0| ≤ 1/245 ∧ (1 : ℝ)/490 ≠ 0 := by norm_num

example (k : Fin 3) (a : Fin 4) :
    SourceNormalizedCanonical.Ncanon (.inr (5,k)) a = 0 ∧
      SourceNormalizedCanonical.Ncanon (.inr (7,k)) a = 0 :=
  SourceNormalizedCanonical.Ncanon_zero_slack k a

example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceExactRoot.source_attainment
