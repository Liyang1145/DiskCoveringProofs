import N11Formalization
set_option autoImplicit false
open N11Formalization SourceContractionProposal SourceActualContraction
open SourceActiveFiniteSystem SourceCompactStressIntervals

#print SourceExactRoot.sourceRadius
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print SourceContractionProposal.C
#print SourceActualContraction.residualEntry
#check @SourceCompactStressIntervals.compact_mem
#check @SourceContractionProposal.table_binding
#check @SourceContractionProposal.all_rows
#check @SourceActualContraction.actual_matrix_bounds
#check @SourceActualContraction.actual_residual_bounds
#check @SourceActualContraction.actual_residual_rows
#check @SourceActualContraction.residualCLM_bound
#check @SourceActualContraction.actual_contraction
#check @SourceActualContraction.H20_error_bound
#print axioms SourceCompactStressIntervals.compact_mem
#print axioms SourceContractionProposal.all_rows
#print axioms SourceActualContraction.actual_matrix_bounds
#print axioms SourceActualContraction.actual_contraction
#print axioms SourceActualContraction.H20_error_bound

example (x : Fin 20 → ℝ) :
    ‖x-(C.map (Rat.cast : ℚ → ℝ)).mulVec (matrix20.mulVec x)‖ ≤
      ((1 : ℝ)/50)*‖x‖ := actual_contraction x

example (j : Fin 9) (y : Fin 20 → ℝ) :
    ‖H20 j-y‖ ≤
      ‖(C.map (Rat.cast : ℚ → ℝ)).mulVec (rhs20 j-matrix20.mulVec y)‖/
        (1-(1 : ℝ)/50) := H20_error_bound j y

-- In particular the actual error certificate still asks for an actual
-- preconditioned residual bound, not an equality to a proposed numerical solve.
example (j : Fin 9) (y : Fin 20 → ℝ) (err : ℝ)
    (hres : ‖(C.map (Rat.cast : ℚ → ℝ)).mulVec (rhs20 j-matrix20.mulVec y)‖ ≤ err) :
    ‖H20 j-y‖ ≤ err/(1-(1 : ℝ)/50) :=
  (H20_error_bound j y).trans
    (div_le_div_of_nonneg_right hres (by norm_num))
